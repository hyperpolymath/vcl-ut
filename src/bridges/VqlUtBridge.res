// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

/// VQL-UT Bridge — connects the ReScript parser to the TypeLL verification
/// server and the Zig FFI native pipeline.
///
/// This module provides the high-level API for VQL-UT query processing:
///
/// 1. Parse a VQL-UT query string into an AST (via VqlUtParser)
/// 2. Send the AST to TypeLL server for 10-level type checking
/// 3. Optionally compile to a native query plan via the Zig FFI
///
/// ## Usage
///
/// ```rescript
/// let result = VqlUtBridge.checkQuery("SELECT GRAPH.name FROM HEXAD abc123")
/// switch result {
/// | Ok(report) => Console.log(report.explanation)
/// | Error(err) => Console.error(err)
/// }
/// ```

/// Result of a VQL-UT query check.
type checkReport = {
  /// Whether the query is valid at its requested safety level.
  valid: bool,
  /// Maximum safety level achieved (0-9).
  maxLevel: int,
  /// Human-readable name of the max level.
  maxLevelName: string,
  /// Query path determined: "VQL (Slipstream)", "VQL-DT", or "VQL-UT".
  queryPath: string,
  /// Per-level diagnostics (empty string = passed, non-empty = diagnostic).
  levelDiagnostics: array<string>,
  /// Human-readable explanation of the result.
  explanation: string,
  /// The parsed AST (for further processing).
  ast: option<VqlUtAst.statement>,
  /// Effects detected in the query.
  effects: array<string>,
  /// Usage quantifier: "omega", "1", or "bounded(n)".
  usage: string,
}

/// Parse and check a VQL-UT query string locally (no server needed).
///
/// Runs the parser, then performs a local safety level analysis based on
/// which extension clauses are present. This does NOT do full type checking
/// against a schema — that requires the TypeLL server.
let checkQuery = (queryStr: string): result<checkReport, string> => {
  switch VqlUtParser.parse(queryStr) {
  | Error(msg) =>
    Ok({
      valid: false,
      maxLevel: 0,
      maxLevelName: "Parse-time safety",
      queryPath: "VQL (Slipstream)",
      levelDiagnostics: [`Parse error: ${msg}`],
      explanation: `Parse failed: ${msg}`,
      ast: None,
      effects: [],
      usage: "omega",
    })
  | Ok(stmt) =>
    // Determine max level from present clauses
    let maxLevel = VqlUtAst.safetyLevelToInt(stmt.requestedLevel)
    let levelName = VqlUtDefinitions.safetyLevelName(maxLevel)
    let path = VqlUtDefinitions.queryPathFromLevel(maxLevel)
    let pathName = VqlUtDefinitions.queryPathName(path)

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
    | Some(VqlUtAst.EffRead) => ["Read"]
    | Some(VqlUtAst.EffWrite) => ["Write"]
    | Some(VqlUtAst.EffReadWrite) => ["Read", "Write"]
    | Some(VqlUtAst.EffConsume) => ["Read", "Write", "Consume"]
    | None => []
    }

    // Determine usage from linearAnnot
    let usage = switch stmt.linearAnnot {
    | Some(VqlUtAst.LinUseOnce) => "1"
    | Some(VqlUtAst.LinBounded(n)) => `bounded(${Int.toString(n)})`
    | Some(VqlUtAst.LinUnlimited) | None => "omega"
    }

    Ok({
      valid: true,
      maxLevel,
      maxLevelName: levelName,
      queryPath: pathName,
      levelDiagnostics: diagnostics,
      explanation: `VQL-UT Level ${Int.toString(maxLevel + 1)}/10 (${levelName}) — query path: ${pathName}`,
      ast: Some(stmt),
      effects,
      usage,
    })
  }
}

/// Encode a checkReport as JSON for transport to TypeLL server.
let reportToJson = (report: checkReport): string => {
  let effectsJson = report.effects
    ->Array.map(e => `"${e}"`)
    ->Array.join(", ")

  let diagnosticsJson = report.levelDiagnostics
    ->Array.map(d => {
      let escaped = d->String.replaceAll("\"", "\\\"")
      `"${escaped}"`
    })
    ->Array.join(", ")

  `{"valid":${report.valid ? "true" : "false"},"maxLevel":${Int.toString(report.maxLevel)},"maxLevelName":"${report.maxLevelName}","queryPath":"${report.queryPath}","effects":[${effectsJson}],"usage":"${report.usage}","levelDiagnostics":[${diagnosticsJson}]}`
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
