// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

/// VCL-total Bridge — connects the ReScript parser to the TypeLL verification
/// server and the Zig FFI native pipeline.
///
/// This module provides the high-level API for VCL-total query processing:
///
/// 1. Parse a VCL-total query string into an AST (via VclTotalParser)
/// 2. Send the AST to TypeLL server for 10-level type checking
/// 3. Optionally compile to a native query plan via the Zig FFI
///
/// ## Usage
///
/// ```rescript
/// let result = VclTotalBridge.checkQuery("SELECT GRAPH.name FROM HEXAD abc123")
/// switch result {
/// | Ok(report) => Console.log(report.explanation)
/// | Error(err) => Console.error(err)
/// }
/// ```

/// Result of a VCL-total query check.
type checkReport = {
  /// Whether the query is valid at its requested safety level.
  valid: bool,
  /// Maximum safety level achieved (0-9).
  maxLevel: int,
  /// Human-readable name of the max level.
  maxLevelName: string,
  /// Query path determined: "VCL (Slipstream)", "VCL-DT", or "VCL-total".
  queryPath: string,
  /// Per-level diagnostics (empty string = passed, non-empty = diagnostic).
  levelDiagnostics: array<string>,
  /// Human-readable explanation of the result.
  explanation: string,
  /// The parsed AST (for further processing).
  ast: option<VclTotalAst.statement>,
  /// Effects detected in the query.
  effects: array<string>,
  /// Usage quantifier: "omega", "1", or "bounded(n)".
  usage: string,
}

/// Parse and check a VCL-total query string locally (no server needed).
///
/// Runs the parser, then performs a local safety level analysis based on
/// which extension clauses are present. This does NOT do full type checking
/// against a schema — that requires the TypeLL server.
let checkQuery = (queryStr: string): result<checkReport, string> => {
  switch VclTotalParser.parse(queryStr) {
  | Error(msg) => Error(`Parse failed: ${msg}`)
  | Ok(stmt) =>
    // Determine max level from present clauses
    let maxLevel = VclTotalAst.safetyLevelToInt(stmt.requestedLevel)
    let levelName = VclTotalDefinitions.safetyLevelName(maxLevel)
    let path = VclTotalDefinitions.queryPathFromLevel(maxLevel)
    let pathName = VclTotalDefinitions.queryPathName(path)

    // Build per-level diagnostics
    let diagnostics = Array.make(~length=10, "")

    // Level 0: always passes (we parsed successfully)
    // Level 1-5: require schema to fully check, mark as "needs schema"
    if maxLevel < 1 {
      diagnostics->Array.setUnsafe(1, "Schema binding requires FROM clause with valid octad")
    }
    if maxLevel < 6 {
      diagnostics->Array.setUnsafe(6, "LIMIT clause required for cardinality safety")
    }
    if maxLevel < 7 {
      diagnostics->Array.setUnsafe(7, "EFFECTS clause required for effect tracking")
    }
    if maxLevel < 8 {
      diagnostics->Array.setUnsafe(8, "AT VERSION clause required for temporal safety")
    }
    if maxLevel < 9 {
      diagnostics->Array.setUnsafe(9, "CONSUME AFTER / USAGE LIMIT required for linearity safety")
    }

    // Determine effects from effectDecl
    let effects = switch stmt.effectDecl {
    | Some(VclTotalAst.EffRead) => ["Read"]
    | Some(VclTotalAst.EffWrite) => ["Write"]
    | Some(VclTotalAst.EffReadWrite) => ["Read", "Write"]
    | Some(VclTotalAst.EffConsume) => ["Read", "Write", "Consume"]
    | None => []
    }

    // Determine usage from linearAnnot
    let usage = switch stmt.linearAnnot {
    | Some(VclTotalAst.LinUseOnce) => "1"
    | Some(VclTotalAst.LinBounded(n)) => `bounded(${Int.toString(n)})`
    | Some(VclTotalAst.LinUnlimited) | None => "omega"
    }

    Ok({
      valid: true,
      maxLevel,
      maxLevelName: levelName,
      queryPath: pathName,
      levelDiagnostics: diagnostics,
      explanation: `VCL-total Level ${Int.toString(maxLevel + 1)}/10 (${levelName}) — query path: ${pathName}`,
      ast: Some(stmt),
      effects,
      usage,
    })
  }
}

/// Escape a string for safe inclusion in a JSON string value.
let escapeJsonString = (s: string): string =>
  s
  ->String.replaceAll("\\", "\\\\")
  ->String.replaceAll("\"", "\\\"")
  ->String.replaceAll("\n", "\\n")
  ->String.replaceAll("\r", "\\r")
  ->String.replaceAll("\t", "\\t")

/// Encode a checkReport as JSON for transport to TypeLL server.
let reportToJson = (report: checkReport): string => {
  let effectsJson = report.effects
    ->Array.map(e => `"${escapeJsonString(e)}"`)
    ->Array.join(", ")

  let diagnosticsJson = report.levelDiagnostics
    ->Array.map(d => `"${escapeJsonString(d)}"`)
    ->Array.join(", ")

  let maxLevelName = escapeJsonString(report.maxLevelName)
  let queryPath = escapeJsonString(report.queryPath)
  let usage = escapeJsonString(report.usage)

  `{"valid":${report.valid ? "true" : "false"},"maxLevel":${Int.toString(report.maxLevel)},"maxLevelName":"${maxLevelName}","queryPath":"${queryPath}","effects":[${effectsJson}],"usage":"${usage}","levelDiagnostics":[${diagnosticsJson}]}`
}

/// Parse a query and return just the safety level (quick check).
let quickLevel = (queryStr: string): int =>
  switch checkQuery(queryStr) {
  | Ok(report) => report.maxLevel
  | Error(_) => 0
  }

/// Parse a query and describe it in human-readable form.
let describe = (queryStr: string): string =>
  switch checkQuery(queryStr) {
  | Ok(report) => report.explanation
  | Error(err) => `Error: ${err}`
  }
