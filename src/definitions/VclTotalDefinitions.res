// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

/// VCL-total Shared Definitions — constants, version info, and vocabulary.

/// ABI version (major, minor, patch)
let abiVersion = (0, 1, 0)

/// ABI version as a packed u32 (matching Zig's encoding)
let abiVersionPacked = {
  let (major, minor, patch) = abiVersion
  lor(lor(lsl(major, 16), lsl(minor, 8)), patch)
}

/// File extension for VCL-total queries
let fileExtension = ".vcltotal"

/// MIME type for VCL-total queries (application/vcl-total)
let mimeType = "application/vcl-total"

/// The 10 safety level names
let safetyLevelNames = [
  "Parse-time safety",
  "Schema-binding safety",
  "Type-compatible operations",
  "Null-safety",
  "Injection-proof safety",
  "Result-type safety",
  "Cardinality safety",
  "Effect-tracking safety",
  "Temporal safety",
  "Linearity safety",
]

/// Get the name of a safety level (0-9)
let safetyLevelName = (level: int): string =>
  switch safetyLevelNames->Array.get(level) {
  | Some(name) => name
  | None => "Unknown"
  }

/// Whether a safety level is in the "established" tier (0-5)
/// or "research-identified" tier (6-9)
let isEstablished = (level: int): bool => level <= 5

/// The 3 query paths
type queryPath = Slipstream | Dt | Ut

/// Determine query path from safety level
let queryPathFromLevel = (level: int): queryPath =>
  if level >= 7 {
    Ut
  } else if level >= 2 {
    Dt
  } else {
    Slipstream
  }

/// Query path display name
let queryPathName = (path: queryPath): string =>
  switch path {
  | Slipstream => "VCL (Slipstream)"
  | Dt => "VCL-DT"
  | Ut => "VCL-total"
  }

/// The 8 VeriSimDB modality names (uppercase, matching VCL syntax)
let modalityNames = [
  "GRAPH", "VECTOR", "TENSOR", "SEMANTIC",
  "DOCUMENT", "TEMPORAL", "PROVENANCE", "SPATIAL",
]

/// Reserved keywords in VCL-total (case-insensitive)
let keywords = [
  "SELECT", "FROM", "WHERE", "GROUP", "BY", "HAVING", "ORDER",
  "LIMIT", "OFFSET", "AND", "OR", "NOT", "IN", "LIKE", "AS",
  "HEXAD", "FEDERATION", "STORE", "PROOF", "ATTACHED", "WITNESS",
  "ASSERT", "EFFECTS", "AT", "LATEST", "VERSION", "BETWEEN",
  "CONSUME", "AFTER", "USE", "USAGE", "WITH", "SESSION",
  "COUNT", "SUM", "AVG", "MIN", "MAX",
]
