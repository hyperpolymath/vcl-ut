// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Total, panic-free tokenizer. Every code path returns a `Result`; the
//! cursor advances only via `saturating_add` and reads only via
//! `slice::get`, so no input can panic or index out of bounds.

/// One lexical token. Keyword vs identifier is left to the parser
/// (case-insensitive), so the lexer stays a pure character classifier.
#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    /// Bare word: keyword or identifier (original case preserved).
    Word(String),
    /// Single-quoted string literal, contents unescaped.
    Str(String),
    /// Integer literal.
    Int(i64),
    /// Floating-point literal.
    Float(f64),
    /// `$name` or `$1` parameter placeholder (name without the `$`).
    Param(String),
    /// Punctuation / operator symbol, normalised (`<>` -> `!=`).
    Sym(&'static str),
}

/// A token plus its 0-based char start offset (for diagnostics).
#[derive(Debug, Clone, PartialEq)]
pub struct Spanned {
    pub tok: Tok,
    pub at: usize,
}

/// Lexing failure with the offending char offset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    pub at: usize,
    pub msg: String,
}

struct Cur {
    src: Vec<char>,
    pos: usize,
}

impl Cur {
    fn peek(&self) -> Option<char> {
        self.src.get(self.pos).copied()
    }
    fn peek2(&self) -> Option<char> {
        self.src.get(self.pos.saturating_add(1)).copied()
    }
    fn bump(&mut self) {
        self.pos = self.pos.saturating_add(1);
    }
}

const SYMS_2: [(&str, &str); 3] = [("<=", "<="), (">=", ">="), ("<>", "!=")];
// The VCL-total alphabet includes `{ } :` (e.g. `EFFECTS { Read }`,
// agent `prover:lean4`). The lexer accepts the whole alphabet; the
// *parser* enforces structure and fail-closes on unsupported clauses.
const SYMS_1: [char; 12] = ['(', ')', ',', '.', '*', ';', '=', '<', '>', '{', '}', ':'];

/// Tokenize `input`. Returns every token in order; never panics.
pub fn lex(input: &str) -> Result<Vec<Spanned>, LexError> {
    let mut c = Cur {
        src: input.chars().collect(),
        pos: 0,
    };
    let mut out: Vec<Spanned> = Vec::new();

    while let Some(ch) = c.peek() {
        if ch.is_whitespace() {
            c.bump();
            continue;
        }
        // Line comment: -- ... to end of line.
        if ch == '-' && c.peek2() == Some('-') {
            while let Some(x) = c.peek() {
                if x == '\n' {
                    break;
                }
                c.bump();
            }
            continue;
        }
        let at = c.pos;

        if ch == '\'' {
            out.push(Spanned {
                tok: lex_string(&mut c)?,
                at,
            });
            continue;
        }
        if ch == '$' {
            out.push(Spanned {
                tok: lex_param(&mut c)?,
                at,
            });
            continue;
        }
        if ch.is_ascii_digit() {
            out.push(Spanned {
                tok: lex_number(&mut c)?,
                at,
            });
            continue;
        }
        if ch == '_' || ch.is_alphabetic() {
            out.push(Spanned {
                tok: lex_word(&mut c),
                at,
            });
            continue;
        }
        if ch == '!' {
            // Only `!=` is meaningful.
            if c.peek2() == Some('=') {
                c.bump();
                c.bump();
                out.push(Spanned {
                    tok: Tok::Sym("!="),
                    at,
                });
                continue;
            }
            return Err(LexError {
                at,
                msg: "lone '!' (expected '!=')".to_string(),
            });
        }
        // Two-char symbols before one-char.
        if let Some(rest) = c.peek2() {
            let pair = [ch, rest].iter().collect::<String>();
            if let Some(found) = SYMS_2.iter().find(|(p, _)| *p == pair) {
                c.bump();
                c.bump();
                out.push(Spanned {
                    tok: Tok::Sym(found.1),
                    at,
                });
                continue;
            }
        }
        if let Some(sym) = SYMS_1.iter().find(|s| **s == ch) {
            c.bump();
            // Map char -> &'static str without allocation.
            let s: &'static str = match sym {
                '(' => "(",
                ')' => ")",
                ',' => ",",
                '.' => ".",
                '*' => "*",
                ';' => ";",
                '=' => "=",
                '<' => "<",
                '>' => ">",
                '{' => "{",
                '}' => "}",
                ':' => ":",
                _ => "",
            };
            out.push(Spanned {
                tok: Tok::Sym(s),
                at,
            });
            continue;
        }

        return Err(LexError {
            at,
            msg: format!("unexpected character {ch:?}"),
        });
    }
    Ok(out)
}

fn lex_string(c: &mut Cur) -> Result<Tok, LexError> {
    let start = c.pos;
    c.bump(); // opening quote
    let mut buf = String::new();
    loop {
        match c.peek() {
            None => {
                return Err(LexError {
                    at: start,
                    msg: "unterminated string literal".to_string(),
                })
            }
            Some('\'') => {
                // '' is an escaped single quote.
                if c.peek2() == Some('\'') {
                    buf.push('\'');
                    c.bump();
                    c.bump();
                    continue;
                }
                c.bump();
                return Ok(Tok::Str(buf));
            }
            Some(other) => {
                buf.push(other);
                c.bump();
            }
        }
    }
}

fn lex_param(c: &mut Cur) -> Result<Tok, LexError> {
    let at = c.pos;
    c.bump(); // '$'
    let mut buf = String::new();
    while let Some(x) = c.peek() {
        if x == '_' || x.is_alphanumeric() {
            buf.push(x);
            c.bump();
        } else {
            break;
        }
    }
    if buf.is_empty() {
        return Err(LexError {
            at,
            msg: "empty parameter name after '$'".to_string(),
        });
    }
    Ok(Tok::Param(buf))
}

fn lex_number(c: &mut Cur) -> Result<Tok, LexError> {
    let at = c.pos;
    let mut buf = String::new();
    let mut is_float = false;
    while let Some(x) = c.peek() {
        if x.is_ascii_digit() {
            buf.push(x);
            c.bump();
        } else if x == '.' && !is_float && c.peek2().is_some_and(|d| d.is_ascii_digit()) {
            is_float = true;
            buf.push('.');
            c.bump();
        } else {
            break;
        }
    }
    if is_float {
        buf.parse::<f64>().map(Tok::Float).map_err(|e| LexError {
            at,
            msg: format!("bad float literal: {e}"),
        })
    } else {
        buf.parse::<i64>().map(Tok::Int).map_err(|e| LexError {
            at,
            msg: format!("bad integer literal: {e}"),
        })
    }
}

fn lex_word(c: &mut Cur) -> Tok {
    let mut buf = String::new();
    while let Some(x) = c.peek() {
        if x == '_' || x.is_alphanumeric() {
            buf.push(x);
            c.bump();
        } else {
            break;
        }
    }
    Tok::Word(buf)
}
