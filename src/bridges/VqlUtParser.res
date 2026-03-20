// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// VQL-UT Recursive Descent Parser — ReScript implementation
//
// Parses VQL-UT query strings into the AST defined in VqlUtAst.res.
// The parser operates in two phases:
//
//   1. Tokenisation: splits the input on whitespace and punctuation,
//      preserving quoted strings and recognising VQL-UT keywords.
//   2. Recursive descent: walks the token stream to build a Statement.
//
// The parser sets `requestedLevel` based on which VQL-UT extension
// clauses are present in the query, using the highest applicable level:
//
//   - No extensions:       ParseSafe       (Level 0)
//   - Has PROOF:           InjectionProof  (Level 4)
//   - Has EFFECTS:         EffectTracked   (Level 7)
//   - Has AT VERSION:      TemporalSafe    (Level 8)
//   - Has CONSUME/USAGE:   LinearSafe      (Level 9)
//
// Grammar (case-insensitive keywords):
//
//   query := SELECT select_items FROM source [WHERE expr]
//            [GROUP BY fields] [HAVING expr] [ORDER BY order_items]
//            [LIMIT n] [OFFSET n]
//            [proof_clause] [effect_clause] [version_clause]
//            [linear_clause]

open VqlUtAst

// ═══════════════════════════════════════════════════════════════════════
// Token type
// ═══════════════════════════════════════════════════════════════════════

/// A token produced by the lexer. Tokens are either keywords/identifiers
/// (TWord), quoted string literals (TString), integer literals (TNumber),
/// float literals (TFloat), or single-character punctuation (TPunct).
type token =
  | TWord(string)
  | TString(string)
  | TNumber(int)
  | TFloat(float)
  | TPunct(string)

// ═══════════════════════════════════════════════════════════════════════
// Parser state
// ═══════════════════════════════════════════════════════════════════════

/// Mutable parser state: holds the token stream and current position.
/// The parser advances `pos` as it consumes tokens. All parse functions
/// receive this state by reference and mutate `pos` in place.
type parserState = {
  /// The full array of tokens produced by the lexer
  tokens: array<token>,
  /// Current position in the token array (mutable)
  mutable pos: int,
}

// ═══════════════════════════════════════════════════════════════════════
// Tokeniser
// ═══════════════════════════════════════════════════════════════════════

/// Check whether a character is whitespace (space, tab, newline, carriage return).
let isWhitespace = (c: string): bool =>
  c == " " || c == "\t" || c == "\n" || c == "\r"

/// Check whether a character is a digit (0-9).
let isDigit = (c: string): bool =>
  c >= "0" && c <= "9"

/// Check whether a character is alphabetic (a-z, A-Z) or underscore.
let isAlpha = (c: string): bool =>
  (c >= "a" && c <= "z") || (c >= "A" && c <= "Z") || c == "_"

/// Check whether a character is alphanumeric or underscore/hyphen.
let isAlphaNum = (c: string): bool =>
  isAlpha(c) || isDigit(c) || c == "-"

/// Single-character punctuation tokens that the lexer emits individually.
let isPunct = (c: string): bool =>
  c == "(" || c == ")" || c == "," || c == "." || c == "*" ||
  c == "{" || c == "}" || c == "=" || c == "<" || c == ">" || c == "!"

/// Tokenise a VQL-UT query string into an array of tokens.
///
/// Rules:
/// - Whitespace is skipped (not emitted as tokens)
/// - Single-quoted strings are preserved (quotes stripped)
/// - Numbers (with optional leading minus) become TNumber or TFloat
/// - Two-character operators (!=, <=, >=) are combined into one TWord
/// - Everything else that starts with a letter/underscore becomes TWord
/// - Single punctuation characters become TPunct
let tokenize = (input: string): array<token> => {
  let tokens = []
  let len = String.length(input)
  let i = ref(0)

  while i.contents < len {
    let c = String.charAt(input, i.contents)

    // Skip whitespace
    if isWhitespace(c) {
      i := i.contents + 1
    }
    // Quoted string literal (single quotes)
    else if c == "'" {
      i := i.contents + 1
      let start = i.contents
      while i.contents < len && String.charAt(input, i.contents) != "'" {
        i := i.contents + 1
      }
      let value = String.slice(input, ~start, ~end=i.contents)
      if i.contents < len {
        i := i.contents + 1 // skip closing quote
      }
      let _ = Array.push(tokens, TString(value))
    }
    // Quoted string literal (double quotes)
    else if c == "\"" {
      i := i.contents + 1
      let start = i.contents
      while i.contents < len && String.charAt(input, i.contents) != "\"" {
        i := i.contents + 1
      }
      let value = String.slice(input, ~start, ~end=i.contents)
      if i.contents < len {
        i := i.contents + 1 // skip closing quote
      }
      let _ = Array.push(tokens, TString(value))
    }
    // Two-character operators: !=, <=, >=
    else if c == "!" && i.contents + 1 < len && String.charAt(input, i.contents + 1) == "=" {
      let _ = Array.push(tokens, TWord("!="))
      i := i.contents + 2
    } else if c == "<" && i.contents + 1 < len && String.charAt(input, i.contents + 1) == "=" {
      let _ = Array.push(tokens, TWord("<="))
      i := i.contents + 2
    } else if c == ">" && i.contents + 1 < len && String.charAt(input, i.contents + 1) == "=" {
      let _ = Array.push(tokens, TWord(">="))
      i := i.contents + 2
    }
    // Number literal (possibly negative, possibly float)
    else if isDigit(c) || (c == "-" && i.contents + 1 < len && isDigit(String.charAt(input, i.contents + 1))) {
      let start = i.contents
      if c == "-" {
        i := i.contents + 1
      }
      while i.contents < len && isDigit(String.charAt(input, i.contents)) {
        i := i.contents + 1
      }
      // Check for decimal point (float)
      if i.contents < len && String.charAt(input, i.contents) == "." &&
         i.contents + 1 < len && isDigit(String.charAt(input, i.contents + 1)) {
        i := i.contents + 1 // skip the dot
        while i.contents < len && isDigit(String.charAt(input, i.contents)) {
          i := i.contents + 1
        }
        let numStr = String.slice(input, ~start, ~end=i.contents)
        switch Float.fromString(numStr) {
        | Some(f) => {
            let _ = Array.push(tokens, TFloat(f))
          }
        | None => {
            let _ = Array.push(tokens, TWord(numStr))
          }
        }
      } else {
        let numStr = String.slice(input, ~start, ~end=i.contents)
        switch Int.fromString(numStr) {
        | Some(n) => {
            let _ = Array.push(tokens, TNumber(n))
          }
        | None => {
            let _ = Array.push(tokens, TWord(numStr))
          }
        }
      }
    }
    // Word (keyword or identifier): starts with letter or underscore
    else if isAlpha(c) {
      let start = i.contents
      while i.contents < len && isAlphaNum(String.charAt(input, i.contents)) {
        i := i.contents + 1
      }
      let word = String.slice(input, ~start, ~end=i.contents)
      let _ = Array.push(tokens, TWord(word))
    }
    // Dollar-prefixed parameter ($name, $1)
    else if c == "$" {
      i := i.contents + 1
      let start = i.contents
      while i.contents < len && isAlphaNum(String.charAt(input, i.contents)) {
        i := i.contents + 1
      }
      let name = String.slice(input, ~start, ~end=i.contents)
      let _ = Array.push(tokens, TWord("$" ++ name))
    }
    // Single punctuation character
    else if isPunct(c) {
      let _ = Array.push(tokens, TPunct(c))
      i := i.contents + 1
    }
    // Unknown character — skip
    else {
      i := i.contents + 1
    }
  }

  tokens
}

// ═══════════════════════════════════════════════════════════════════════
// Parser helpers
// ═══════════════════════════════════════════════════════════════════════

/// Peek at the current token without consuming it.
/// Returns None if the parser has reached the end of the token stream.
let peek = (state: parserState): option<token> =>
  if state.pos < Array.length(state.tokens) {
    Some(state.tokens[state.pos])
  } else {
    None
  }

/// Consume and return the current token, advancing the position.
/// Returns None if the parser has reached the end of the token stream.
let advance = (state: parserState): option<token> =>
  if state.pos < Array.length(state.tokens) {
    let tok = state.tokens[state.pos]
    state.pos = state.pos + 1
    Some(tok)
  } else {
    None
  }

/// Check whether the current token is a word matching the given string
/// (case-insensitive comparison). Does NOT consume the token.
let peekWord = (state: parserState, word: string): bool =>
  switch peek(state) {
  | Some(TWord(w)) => String.toUpperCase(w) == String.toUpperCase(word)
  | _ => false
  }

/// Consume the current token if it is a word matching the given string
/// (case-insensitive). Returns true if consumed, false otherwise.
let expectWord = (state: parserState, word: string): bool =>
  if peekWord(state, word) {
    state.pos = state.pos + 1
    true
  } else {
    false
  }

/// Consume the current token if it is a punctuation character matching
/// the given string. Returns true if consumed, false otherwise.
let expectPunct = (state: parserState, punct: string): bool =>
  switch peek(state) {
  | Some(TPunct(p)) if p == punct => {
      state.pos = state.pos + 1
      true
    }
  | _ => false
  }

/// Return an error result with a message describing what was expected
/// and what was actually found at the current position.
let parseError = (state: parserState, expected: string): result<'a, string> => {
  let found = switch peek(state) {
  | Some(TWord(w)) => `word "${w}"`
  | Some(TString(s)) => `string '${s}'`
  | Some(TNumber(n)) => `number ${Int.toString(n)}`
  | Some(TFloat(f)) => `float ${Float.toString(f)}`
  | Some(TPunct(p)) => `'${p}'`
  | None => "end of input"
  }
  Error(`Expected ${expected}, found ${found} at position ${Int.toString(state.pos)}`)
}

// ═══════════════════════════════════════════════════════════════════════
// Modality parsing
// ═══════════════════════════════════════════════════════════════════════

/// Parse a modality name from the current token.
/// Modality names are case-insensitive and must be one of the 8
/// VeriSimDB modalities (GRAPH, VECTOR, TENSOR, SEMANTIC, DOCUMENT,
/// TEMPORAL, PROVENANCE, SPATIAL).
///
/// Returns the parsed modality or an error if the current token is
/// not a recognised modality name.
let parseModality = (name: string): option<modality> =>
  switch String.toUpperCase(name) {
  | "GRAPH" => Some(Graph)
  | "VECTOR" => Some(Vector)
  | "TENSOR" => Some(Tensor)
  | "SEMANTIC" => Some(Semantic)
  | "DOCUMENT" => Some(Document)
  | "TEMPORAL" => Some(Temporal)
  | "PROVENANCE" => Some(Provenance)
  | "SPATIAL" => Some(Spatial)
  | _ => None
  }

/// Check whether a word is a VQL-UT keyword (case-insensitive).
/// Keywords cannot be used as field names or identifiers.
let isKeyword = (word: string): bool => {
  let upper = String.toUpperCase(word)
  upper == "SELECT" || upper == "FROM" || upper == "WHERE" ||
  upper == "GROUP" || upper == "HAVING" || upper == "ORDER" ||
  upper == "LIMIT" || upper == "OFFSET" || upper == "AND" ||
  upper == "OR" || upper == "NOT" || upper == "LIKE" ||
  upper == "IN" || upper == "BY" || upper == "ASC" ||
  upper == "DESC" || upper == "PROOF" || upper == "EFFECTS" ||
  upper == "AT" || upper == "CONSUME" || upper == "USAGE" ||
  upper == "HEXAD" || upper == "FEDERATION" || upper == "STORE" ||
  upper == "ATTACHED" || upper == "WITNESS" || upper == "ASSERT" ||
  upper == "VERSION" || upper == "LATEST" || upper == "BETWEEN" ||
  upper == "AFTER" || upper == "USE" || upper == "TRUE" ||
  upper == "FALSE" || upper == "NULL" || upper == "WITH" ||
  upper == "SESSION" || upper == "COUNT" || upper == "SUM" ||
  upper == "AVG" || upper == "MIN" || upper == "MAX"
}

// ═══════════════════════════════════════════════════════════════════════
// Aggregate function parsing
// ═══════════════════════════════════════════════════════════════════════

/// Try to parse an aggregate function name from the given word.
/// Returns None if the word is not a recognised aggregate function.
let parseAggFunc = (name: string): option<aggFunc> =>
  switch String.toUpperCase(name) {
  | "COUNT" => Some(Count)
  | "SUM" => Some(Sum)
  | "AVG" => Some(Avg)
  | "MIN" => Some(Min)
  | "MAX" => Some(Max)
  | _ => None
  }

// ═══════════════════════════════════════════════════════════════════════
// Field reference parsing
// ═══════════════════════════════════════════════════════════════════════

/// Parse a field reference of the form MODALITY.field_name.
/// The modality must be one of the 8 VeriSimDB modalities.
/// The field name follows the dot and must be an alphanumeric identifier.
///
/// Example: GRAPH.name, VECTOR.embedding, TEMPORAL.created_at
let parseFieldRef = (state: parserState): result<fieldRef, string> =>
  switch advance(state) {
  | Some(TWord(w)) =>
    switch parseModality(w) {
    | Some(mod) =>
      if expectPunct(state, ".") {
        switch advance(state) {
        | Some(TWord(fieldName)) => Ok({modality: mod, fieldName})
        | _ => parseError(state, "field name after '.'")
        }
      } else {
        // Might be a bare modality reference — put it back
        state.pos = state.pos - 1
        parseError(state, "field reference (MODALITY.field_name)")
      }
    | None => {
        state.pos = state.pos - 1
        parseError(state, "modality name")
      }
    }
  | _ => parseError(state, "field reference")
  }

/// Try to parse a field reference. Returns None if the current tokens
/// do not form a valid field reference, without consuming any tokens.
let tryParseFieldRef = (state: parserState): option<fieldRef> => {
  let savedPos = state.pos
  switch parseFieldRef(state) {
  | Ok(ref) => Some(ref)
  | Error(_) => {
      state.pos = savedPos
      None
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════
// Expression parsing (recursive descent)
// ═══════════════════════════════════════════════════════════════════════

/// Parse a primary (atomic) expression.
///
/// Primary expressions are the leaves of the expression tree:
/// - Parenthesised sub-expression: ( expr )
/// - Parameter reference: $name
/// - String literal: 'hello'
/// - Boolean literal: TRUE / FALSE
/// - NULL literal
/// - Number literal: 42, 3.14
/// - Aggregate function: COUNT(expr), SUM(expr), etc.
/// - Star: *
/// - Field reference: MODALITY.field_name
/// - Subquery: ( SELECT ... )
let rec parsePrimary = (state: parserState): result<expr, string> => {
  switch peek(state) {
  // Parenthesised expression or subquery
  | Some(TPunct("(")) => {
      let _ = advance(state)
      // Check if it's a subquery (starts with SELECT)
      if peekWord(state, "SELECT") {
        switch parseStatementInner(state) {
        | Ok(stmt) =>
          if expectPunct(state, ")") {
            Ok(ESubquery(stmt))
          } else {
            parseError(state, "closing ')' after subquery")
          }
        | Error(e) => Error(e)
        }
      } else {
        switch parseExpr(state) {
        | Ok(e) =>
          if expectPunct(state, ")") {
            Ok(e)
          } else {
            parseError(state, "closing ')'")
          }
        | Error(e) => Error(e)
        }
      }
    }

  // Star wildcard
  | Some(TPunct("*")) => {
      let _ = advance(state)
      Ok(EStar)
    }

  // String literal
  | Some(TString(s)) => {
      let _ = advance(state)
      Ok(ELiteral(LitString(s), TString))
    }

  // Integer literal
  | Some(TNumber(n)) => {
      let _ = advance(state)
      Ok(ELiteral(LitInt(n), TInt))
    }

  // Float literal
  | Some(TFloat(f)) => {
      let _ = advance(state)
      Ok(ELiteral(LitFloat(f), TFloat))
    }

  // Word: could be keyword, aggregate, modality, field ref, parameter
  | Some(TWord(w)) => {
      let upper = String.toUpperCase(w)

      // Boolean literals
      if upper == "TRUE" {
        let _ = advance(state)
        Ok(ELiteral(LitBool(true), TBool))
      } else if upper == "FALSE" {
        let _ = advance(state)
        Ok(ELiteral(LitBool(false), TBool))
      }
      // NULL literal
      else if upper == "NULL" {
        let _ = advance(state)
        Ok(ELiteral(LitNull, TAny))
      }
      // NOT (unary logical)
      else if upper == "NOT" {
        let _ = advance(state)
        switch parsePrimary(state) {
        | Ok(operand) => Ok(ELogic(Not, operand, None, TBool))
        | Error(e) => Error(e)
        }
      }
      // Parameter ($name)
      else if String.startsWith(w, "$") {
        let _ = advance(state)
        let paramName = String.sliceToEnd(w, ~start=1)
        Ok(EParam(paramName, TAny))
      }
      // Aggregate function: COUNT(...), SUM(...), etc.
      else {
        switch parseAggFunc(upper) {
        | Some(aggFn) => {
            let _ = advance(state) // consume the function name
            if expectPunct(state, "(") {
              switch parseExpr(state) {
              | Ok(innerExpr) =>
                if expectPunct(state, ")") {
                  Ok(EAggregate(aggFn, innerExpr, TAny))
                } else {
                  parseError(state, "closing ')' after aggregate argument")
                }
              | Error(e) => Error(e)
              }
            } else {
              // Not an aggregate call — treat as a field ref
              state.pos = state.pos - 1
              switch tryParseFieldRef(state) {
              | Some(ref) => Ok(EField(ref, TAny))
              | None => {
                  let _ = advance(state) // consume the word
                  Ok(EField({modality: Graph, fieldName: w}, TAny))
                }
              }
            }
          }
        | None =>
          // Try as a field reference (MODALITY.field_name)
          switch tryParseFieldRef(state) {
          | Some(ref) => Ok(EField(ref, TAny))
          | None => {
              // Bare word — treat as an unqualified field name
              let _ = advance(state)
              Ok(EField({modality: Graph, fieldName: w}, TAny))
            }
          }
        }
      }
    }

  | _ => parseError(state, "expression")
  }
}

/// Parse a comparison expression.
///
/// Handles binary comparison operators: =, !=, <, >, <=, >=, LIKE, IN.
/// Left-hand side is a primary expression; if a comparison operator
/// follows, the right-hand side is also parsed as a primary.
and parseComparison = (state: parserState): result<expr, string> => {
  switch parsePrimary(state) {
  | Ok(left) => {
      // Check for comparison operator
      let compOp = switch peek(state) {
      | Some(TPunct("=")) => Some(Eq)
      | Some(TWord("!=")) => Some(NotEq)
      | Some(TPunct("<")) => Some(Lt)
      | Some(TPunct(">")) => Some(Gt)
      | Some(TWord("<=")) => Some(LtEq)
      | Some(TWord(">=")) => Some(GtEq)
      | Some(TWord(w)) if String.toUpperCase(w) == "LIKE" => Some(Like)
      | Some(TWord(w)) if String.toUpperCase(w) == "IN" => Some(In)
      | _ => None
      }

      switch compOp {
      | Some(op) => {
          let _ = advance(state)
          switch parsePrimary(state) {
          | Ok(right) => Ok(ECompare(op, left, right, TBool))
          | Error(e) => Error(e)
          }
        }
      | None => Ok(left)
      }
    }
  | Error(e) => Error(e)
  }
}

/// Parse a logical expression (AND, OR).
///
/// AND has higher precedence than OR. Both are left-associative.
/// NOT is handled in parsePrimary as a unary prefix operator.
///
/// This uses a simple left-to-right pass: first parse a comparison,
/// then while AND or OR follows, parse the next comparison and
/// combine them into an ELogic node.
and parseExpr = (state: parserState): result<expr, string> => {
  switch parseAndExpr(state) {
  | Ok(left) => parseOrTail(state, left)
  | Error(e) => Error(e)
  }
}

/// Parse the AND level of precedence.
/// AND binds tighter than OR.
and parseAndExpr = (state: parserState): result<expr, string> => {
  switch parseComparison(state) {
  | Ok(left) => parseAndTail(state, left)
  | Error(e) => Error(e)
  }
}

/// Continue parsing AND conjunctions after the left operand.
and parseAndTail = (state: parserState, left: expr): result<expr, string> => {
  if peekWord(state, "AND") {
    let _ = advance(state)
    switch parseComparison(state) {
    | Ok(right) => {
        let combined = ELogic(And, left, Some(right), TBool)
        parseAndTail(state, combined)
      }
    | Error(e) => Error(e)
    }
  } else {
    Ok(left)
  }
}

/// Continue parsing OR disjunctions after the left operand.
and parseOrTail = (state: parserState, left: expr): result<expr, string> => {
  if peekWord(state, "OR") {
    let _ = advance(state)
    switch parseAndExpr(state) {
    | Ok(right) => {
        let combined = ELogic(Or, left, Some(right), TBool)
        parseOrTail(state, combined)
      }
    | Error(e) => Error(e)
    }
  } else {
    Ok(left)
  }
}

// ═══════════════════════════════════════════════════════════════════════
// SELECT items
// ═══════════════════════════════════════════════════════════════════════

/// Parse a single SELECT item.
///
/// A select item can be:
/// - * (all modalities)
/// - An aggregate function call: COUNT(expr), SUM(expr), etc.
/// - A modality name: GRAPH, VECTOR, etc.
/// - A field reference: MODALITY.field_name
and parseSelectItem = (state: parserState): result<selectItem, string> => {
  switch peek(state) {
  // Star: SELECT *
  | Some(TPunct("*")) => {
      let _ = advance(state)
      Ok(SelStar)
    }

  | Some(TWord(w)) => {
      let upper = String.toUpperCase(w)

      // Check for aggregate function: COUNT(...), SUM(...), etc.
      switch parseAggFunc(upper) {
      | Some(aggFn) => {
          let savedPos = state.pos
          let _ = advance(state)
          if expectPunct(state, "(") {
            switch parseExpr(state) {
            | Ok(innerExpr) =>
              if expectPunct(state, ")") {
                Ok(SelAggregate(aggFn, innerExpr))
              } else {
                parseError(state, "closing ')' after aggregate argument")
              }
            | Error(e) => Error(e)
            }
          } else {
            // Not a function call — backtrack
            state.pos = savedPos
            switch tryParseFieldRef(state) {
            | Some(ref) => Ok(SelField(ref))
            | None => {
                let _ = advance(state)
                switch parseModality(w) {
                | Some(mod) => Ok(SelModality(mod))
                | None => Ok(SelField({modality: Graph, fieldName: w}))
                }
              }
            }
          }
        }

      | None =>
        // Check if it's MODALITY.field or bare MODALITY
        switch tryParseFieldRef(state) {
        | Some(ref) => Ok(SelField(ref))
        | None => {
            let _ = advance(state)
            switch parseModality(w) {
            | Some(mod) => Ok(SelModality(mod))
            | None => Ok(SelField({modality: Graph, fieldName: w}))
            }
          }
        }
      }
    }

  | _ => parseError(state, "select item")
  }
}

/// Parse a comma-separated list of SELECT items.
/// At least one item is required.
and parseSelectItems = (state: parserState): result<array<selectItem>, string> => {
  switch parseSelectItem(state) {
  | Ok(first) => {
      let items = [first]
      while expectPunct(state, ",") {
        switch parseSelectItem(state) {
        | Ok(item) => {
            let _ = Array.push(items, item)
          }
        | Error(_) => ()
        }
      }
      Ok(items)
    }
  | Error(e) => Error(e)
  }
}

// ═══════════════════════════════════════════════════════════════════════
// FROM source
// ═══════════════════════════════════════════════════════════════════════

/// Parse a FROM clause source.
///
/// Sources can be:
/// - HEXAD <uuid>       — a single octad by UUID
/// - FEDERATION <pattern> — a federation query pattern
/// - STORE <id>         — a named data store
and parseSource = (state: parserState): result<source, string> => {
  if expectWord(state, "HEXAD") {
    switch advance(state) {
    | Some(TWord(uuid)) => Ok(SrcOctad(uuid))
    | Some(TString(uuid)) => Ok(SrcOctad(uuid))
    | _ => parseError(state, "octad UUID after HEXAD")
    }
  } else if expectWord(state, "FEDERATION") {
    switch advance(state) {
    | Some(TWord(pattern)) => Ok(SrcFederation(pattern))
    | Some(TString(pattern)) => Ok(SrcFederation(pattern))
    | _ => parseError(state, "federation pattern after FEDERATION")
    }
  } else if expectWord(state, "STORE") {
    switch advance(state) {
    | Some(TWord(id)) => Ok(SrcStore(id))
    | Some(TString(id)) => Ok(SrcStore(id))
    | _ => parseError(state, "store identifier after STORE")
    }
  } else {
    parseError(state, "source (HEXAD, FEDERATION, or STORE)")
  }
}

// ═══════════════════════════════════════════════════════════════════════
// Extension clauses
// ═══════════════════════════════════════════════════════════════════════

/// Parse a PROOF clause.
///
/// Syntax:
/// - PROOF ATTACHED           — sigma-type proof is bundled
/// - PROOF WITNESS <name>     — references a named witness
/// - PROOF ASSERT <expr>      — inline assertion expression
and parseProofClause = (state: parserState): result<proofClause, string> => {
  if expectWord(state, "ATTACHED") {
    Ok(ProofAttached)
  } else if expectWord(state, "WITNESS") {
    switch advance(state) {
    | Some(TWord(name)) => Ok(ProofWitness(name))
    | Some(TString(name)) => Ok(ProofWitness(name))
    | _ => parseError(state, "witness name after PROOF WITNESS")
    }
  } else if expectWord(state, "ASSERT") {
    switch parseExpr(state) {
    | Ok(e) => Ok(ProofAssert(e))
    | Error(e) => Error(e)
    }
  } else {
    parseError(state, "ATTACHED, WITNESS, or ASSERT after PROOF")
  }
}

/// Parse an EFFECTS clause.
///
/// Syntax: EFFECTS { Read } | EFFECTS { Write } |
///         EFFECTS { Read, Write } | EFFECTS { Consume }
and parseEffectClause = (state: parserState): result<effectDecl, string> => {
  if !expectPunct(state, "{") {
    return parseError(state, "'{' after EFFECTS")
  }

  // Collect effect names
  let effects = []
  switch advance(state) {
  | Some(TWord(w)) => {
      let _ = Array.push(effects, String.toUpperCase(w))
    }
  | _ => return parseError(state, "effect name (Read, Write, Consume)")
  }

  // Check for additional effects (comma-separated)
  while expectPunct(state, ",") {
    switch advance(state) {
    | Some(TWord(w)) => {
        let _ = Array.push(effects, String.toUpperCase(w))
      }
    | _ => ()
    }
  }

  if !expectPunct(state, "}") {
    return parseError(state, "'}' to close EFFECTS block")
  }

  // Determine effect type from collected names
  let hasRead = Array.some(effects, e => e == "READ")
  let hasWrite = Array.some(effects, e => e == "WRITE")
  let hasConsume = Array.some(effects, e => e == "CONSUME")

  if hasConsume {
    Ok(EffConsume)
  } else if hasRead && hasWrite {
    Ok(EffReadWrite)
  } else if hasWrite {
    Ok(EffWrite)
  } else if hasRead {
    Ok(EffRead)
  } else {
    Error("Unknown effect combination in EFFECTS clause")
  }
}

/// Parse a version constraint clause.
///
/// Syntax:
/// - AT LATEST                         — use latest version
/// - AT VERSION >= n                   — at least version n
/// - AT VERSION = n                    — exactly version n
/// - AT VERSION BETWEEN n AND m        — version range [n, m]
and parseVersionClause = (state: parserState): result<versionConstraint, string> => {
  if expectWord(state, "LATEST") {
    Ok(VerLatest)
  } else if expectWord(state, "VERSION") {
    // Check which constraint type
    if expectWord(state, ">=") || (expectPunct(state, ">") && expectPunct(state, "=")) {
      switch advance(state) {
      | Some(TNumber(n)) => Ok(VerAtLeast(n))
      | _ => parseError(state, "version number after >=")
      }
    } else if expectPunct(state, "=") {
      switch advance(state) {
      | Some(TNumber(n)) => Ok(VerExact(n))
      | _ => parseError(state, "version number after =")
      }
    } else if expectWord(state, "BETWEEN") {
      switch advance(state) {
      | Some(TNumber(lo)) =>
        if expectWord(state, "AND") {
          switch advance(state) {
          | Some(TNumber(hi)) => Ok(VerRange(lo, hi))
          | _ => parseError(state, "upper version number after AND")
          }
        } else {
          parseError(state, "AND after lower version bound")
        }
      | _ => parseError(state, "lower version number after BETWEEN")
      }
    } else {
      parseError(state, ">=, =, or BETWEEN after VERSION")
    }
  } else {
    parseError(state, "LATEST or VERSION after AT")
  }
}

/// Parse a linearity clause.
///
/// Syntax:
/// - CONSUME AFTER n USE    — resource consumed after n uses
///   (n=1 maps to LinUseOnce, n>1 maps to LinBounded)
/// - USAGE LIMIT n          — explicit usage limit
and parseLinearClause = (state: parserState, keyword: string): result<linearAnnotation, string> => {
  let upper = String.toUpperCase(keyword)
  if upper == "CONSUME" {
    if expectWord(state, "AFTER") {
      switch advance(state) {
      | Some(TNumber(n)) =>
        if expectWord(state, "USE") || expectWord(state, "USES") {
          if n == 1 {
            Ok(LinUseOnce)
          } else {
            Ok(LinBounded(n))
          }
        } else {
          parseError(state, "USE after count in CONSUME AFTER n USE")
        }
      | _ => parseError(state, "count after CONSUME AFTER")
      }
    } else {
      parseError(state, "AFTER following CONSUME")
    }
  } else if upper == "USAGE" {
    if expectWord(state, "LIMIT") {
      switch advance(state) {
      | Some(TNumber(n)) =>
        if n == 1 {
          Ok(LinUseOnce)
        } else {
          Ok(LinBounded(n))
        }
      | _ => parseError(state, "count after USAGE LIMIT")
      }
    } else {
      parseError(state, "LIMIT after USAGE")
    }
  } else {
    Error(`Unexpected keyword "${keyword}" in linearity clause`)
  }
}

// ═══════════════════════════════════════════════════════════════════════
// Statement parsing
// ═══════════════════════════════════════════════════════════════════════

/// Parse a complete VQL-UT statement from the current token position.
///
/// This is the core of the recursive descent parser. It expects:
///   SELECT select_items FROM source [WHERE expr] [GROUP BY fields]
///   [HAVING expr] [ORDER BY order_items] [LIMIT n] [OFFSET n]
///   [PROOF ...] [EFFECTS ...] [AT ...] [CONSUME/USAGE ...]
///
/// The parser builds a statement record and infers the requestedLevel
/// from which extension clauses are present.
and parseStatementInner = (state: parserState): result<statement, string> => {
  // ── SELECT ──
  if !expectWord(state, "SELECT") {
    return parseError(state, "SELECT")
  }

  let selectItems = switch parseSelectItems(state) {
  | Ok(items) => items
  | Error(e) => return Error(e)
  }

  // ── FROM ──
  if !expectWord(state, "FROM") {
    return parseError(state, "FROM")
  }

  let source = switch parseSource(state) {
  | Ok(s) => s
  | Error(e) => return Error(e)
  }

  // ── WHERE (optional) ──
  let whereClause = if peekWord(state, "WHERE") {
    let _ = advance(state)
    switch parseExpr(state) {
    | Ok(e) => Some(e)
    | Error(e) => return Error(e)
    }
  } else {
    None
  }

  // ── GROUP BY (optional) ──
  let groupBy = if peekWord(state, "GROUP") {
    let _ = advance(state)
    if !expectWord(state, "BY") {
      return parseError(state, "BY after GROUP")
    }
    let fields = []
    switch parseFieldRef(state) {
    | Ok(ref) => {
        let _ = Array.push(fields, ref)
        while expectPunct(state, ",") {
          switch parseFieldRef(state) {
          | Ok(ref2) => {
              let _ = Array.push(fields, ref2)
            }
          | Error(_) => ()
          }
        }
      }
    | Error(e) => return Error(e)
    }
    fields
  } else {
    []
  }

  // ── HAVING (optional) ──
  let having = if peekWord(state, "HAVING") {
    let _ = advance(state)
    switch parseExpr(state) {
    | Ok(e) => Some(e)
    | Error(e) => return Error(e)
    }
  } else {
    None
  }

  // ── ORDER BY (optional) ──
  let orderBy = if peekWord(state, "ORDER") {
    let _ = advance(state)
    if !expectWord(state, "BY") {
      return parseError(state, "BY after ORDER")
    }
    let items: array<(fieldRef, bool)> = []
    switch parseFieldRef(state) {
    | Ok(ref) => {
        let asc = if expectWord(state, "DESC") {
          false
        } else {
          let _ = expectWord(state, "ASC") // consume optional ASC
          true
        }
        let _ = Array.push(items, (ref, asc))
        while expectPunct(state, ",") {
          switch parseFieldRef(state) {
          | Ok(ref2) => {
              let asc2 = if expectWord(state, "DESC") {
                false
              } else {
                let _ = expectWord(state, "ASC")
                true
              }
              let _ = Array.push(items, (ref2, asc2))
            }
          | Error(_) => ()
          }
        }
      }
    | Error(e) => return Error(e)
    }
    items
  } else {
    []
  }

  // ── LIMIT (optional) ──
  let limit = if peekWord(state, "LIMIT") {
    let _ = advance(state)
    switch advance(state) {
    | Some(TNumber(n)) => Some(n)
    | _ => return parseError(state, "number after LIMIT")
    }
  } else {
    None
  }

  // ── OFFSET (optional) ──
  let offset = if peekWord(state, "OFFSET") {
    let _ = advance(state)
    switch advance(state) {
    | Some(TNumber(n)) => Some(n)
    | _ => return parseError(state, "number after OFFSET")
    }
  } else {
    None
  }

  // ── VQL-UT extension clauses (optional, order-independent) ──
  let proofClause: ref<option<proofClause>> = ref(None)
  let effectDecl: ref<option<effectDecl>> = ref(None)
  let versionConst: ref<option<versionConstraint>> = ref(None)
  let linearAnnot: ref<option<linearAnnotation>> = ref(None)

  // Parse extension clauses in a loop — they can appear in any order
  let parsing = ref(true)
  while parsing.contents {
    switch peek(state) {
    | Some(TWord(w)) => {
        let upper = String.toUpperCase(w)
        if upper == "PROOF" && proofClause.contents == None {
          let _ = advance(state)
          switch parseProofClause(state) {
          | Ok(pc) => proofClause := Some(pc)
          | Error(e) => return Error(e)
          }
        } else if upper == "EFFECTS" && effectDecl.contents == None {
          let _ = advance(state)
          switch parseEffectClause(state) {
          | Ok(ed) => effectDecl := Some(ed)
          | Error(e) => return Error(e)
          }
        } else if upper == "AT" && versionConst.contents == None {
          let _ = advance(state)
          switch parseVersionClause(state) {
          | Ok(vc) => versionConst := Some(vc)
          | Error(e) => return Error(e)
          }
        } else if (upper == "CONSUME" || upper == "USAGE") && linearAnnot.contents == None {
          let _ = advance(state)
          switch parseLinearClause(state, upper) {
          | Ok(la) => linearAnnot := Some(la)
          | Error(e) => return Error(e)
          }
        } else if upper == "WITH" {
          // WITH SESSION <mode> — informational, skip for now
          let _ = advance(state)
          let _ = expectWord(state, "SESSION")
          let _ = advance(state) // skip mode name
        } else {
          parsing := false
        }
      }
    | _ => parsing := false
    }
  }

  // ── Compute requested safety level ──
  // The level is the highest applicable based on which clauses are present.
  let level = ref(ParseSafe)
  if proofClause.contents != None {
    level := maxSafetyLevel(level.contents, InjectionProof)
  }
  if effectDecl.contents != None {
    level := maxSafetyLevel(level.contents, EffectTracked)
  }
  if versionConst.contents != None {
    level := maxSafetyLevel(level.contents, TemporalSafe)
  }
  if linearAnnot.contents != None {
    level := maxSafetyLevel(level.contents, LinearSafe)
  }

  Ok({
    selectItems,
    source,
    whereClause,
    groupBy,
    having,
    orderBy,
    limit,
    offset,
    proofClause: proofClause.contents,
    effectDecl: effectDecl.contents,
    versionConst: versionConst.contents,
    linearAnnot: linearAnnot.contents,
    requestedLevel: level.contents,
  })
}

// ═══════════════════════════════════════════════════════════════════════
// Public API
// ═══════════════════════════════════════════════════════════════════════

/// Parse a VQL-UT query string into a typed Statement AST.
///
/// This is the main entry point for the parser. It tokenises the input
/// string, then runs the recursive descent parser to produce a Statement.
///
/// Returns Ok(statement) on success, or Error(message) with a
/// human-readable error description on failure.
///
/// The returned statement's `requestedLevel` field reflects the highest
/// safety level inferred from the extension clauses present:
///   - No extensions:     ParseSafe       (Level 0)
///   - PROOF clause:      InjectionProof  (Level 4)
///   - EFFECTS clause:    EffectTracked   (Level 7)
///   - AT VERSION clause: TemporalSafe    (Level 8)
///   - CONSUME/USAGE:     LinearSafe      (Level 9)
///
/// Example:
///   parse("SELECT * FROM HEXAD abc-123 WHERE GRAPH.name = 'hello' LIMIT 10")
///   // => Ok({ selectItems: [SelStar], source: SrcOctad("abc-123"), ... })
let parse = (input: string): result<statement, string> => {
  let tokens = tokenize(input)

  if Array.length(tokens) == 0 {
    return Error("Empty query")
  }

  let state = {tokens, pos: 0}

  switch parseStatementInner(state) {
  | Ok(stmt) => {
      // Warn if there are unconsumed tokens (but still return the statement)
      if state.pos < Array.length(state.tokens) {
        // Could be trailing tokens — for now, accept the parse
        Ok(stmt)
      } else {
        Ok(stmt)
      }
    }
  | Error(e) => Error(e)
  }
}

/// Tokenise a VQL-UT query string without parsing.
/// Useful for debugging and syntax highlighting.
///
/// Returns the array of tokens produced by the lexer.
let tokenizeOnly = (input: string): array<token> => tokenize(input)

/// Attempt to parse and return a human-readable description of the
/// parse result, useful for REPL or debugging output.
///
/// On success, reports the number of select items, source type,
/// and inferred safety level. On failure, reports the error message.
let parseAndDescribe = (input: string): string => {
  switch parse(input) {
  | Ok(stmt) => {
      let selectCount = Array.length(stmt.selectItems)
      let sourceDesc = switch stmt.source {
      | SrcOctad(id) => `HEXAD ${id}`
      | SrcFederation(pat) => `FEDERATION ${pat}`
      | SrcStore(id) => `STORE ${id}`
      }
      let levelNum = safetyLevelToInt(stmt.requestedLevel)
      `OK: ${Int.toString(selectCount)} select item(s) FROM ${sourceDesc}, safety level ${Int.toString(levelNum)}`
    }
  | Error(e) => `ERROR: ${e}`
  }
}
