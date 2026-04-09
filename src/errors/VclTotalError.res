// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

/// VCL-total error types matching the ABI error codes.
///
/// Each error carries a safety level where the failure occurred,
/// a human-readable message, and an optional source location.

/// Source location in a VCL-total query string.
type sourceLocation = {
  offset: int,
  line: int,
  column: int,
}

/// The 11 error categories matching VclTotalError in Types.idr.
type errorCode =
  | ParseError        // Level 0: syntax error
  | SchemaError       // Level 1: unresolved field reference
  | TypeError         // Level 2: incompatible types in comparison
  | NullError         // Level 3: nullable field used without guard
  | InjectionAttempt  // Level 4: raw string literal in unsafe position
  | ResultTypeError   // Level 5: unresolved result type (TAny in select)
  | CardinalityViolation // Level 6: unbounded result without LIMIT
  | EffectViolation   // Level 7: undeclared effect
  | TemporalBoundsExceeded // Level 8: version constraint violation
  | LinearityViolation // Level 9: use-count exceeded
  | InternalError     // Internal checker error

/// A VCL-total diagnostic error.
type diagnostic = {
  code: errorCode,
  level: int,        // Safety level (0-9) where the error occurred
  message: string,
  location: option<sourceLocation>,
  hint: option<string>,
}

/// Convert an error code to its ABI integer tag.
let errorCodeToInt = (code: errorCode): int =>
  switch code {
  | ParseError => 1
  | SchemaError => 2
  | TypeError => 3
  | NullError => 4
  | InjectionAttempt => 5
  | ResultTypeError => 6
  | CardinalityViolation => 7
  | EffectViolation => 8
  | TemporalBoundsExceeded => 9
  | LinearityViolation => 10
  | InternalError => 11
  }

/// Convert an ABI integer tag to an error code.
let errorCodeFromInt = (n: int): option<errorCode> =>
  switch n {
  | 1 => Some(ParseError)
  | 2 => Some(SchemaError)
  | 3 => Some(TypeError)
  | 4 => Some(NullError)
  | 5 => Some(InjectionAttempt)
  | 6 => Some(ResultTypeError)
  | 7 => Some(CardinalityViolation)
  | 8 => Some(EffectViolation)
  | 9 => Some(TemporalBoundsExceeded)
  | 10 => Some(LinearityViolation)
  | 11 => Some(InternalError)
  | _ => None
  }

/// Format a diagnostic as a human-readable string.
let formatDiagnostic = (d: diagnostic): string => {
  let loc = switch d.location {
  | Some({line, column, _}) => ` at ${Int.toString(line)}:${Int.toString(column)}`
  | None => ""
  }
  let hint = switch d.hint {
  | Some(h) => `\n  hint: ${h}`
  | None => ""
  }
  `[Level ${Int.toString(d.level)}] ${d.message}${loc}${hint}`
}
