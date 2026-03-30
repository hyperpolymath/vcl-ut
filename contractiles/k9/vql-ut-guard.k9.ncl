# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# K9 Validator: VQL-UT Guard
# Ensures the VQL-UT language invariants stay provable and the bridges stay in sync with Idris2.

let vql_ut_guard = {
  name = "vql-ut-guard",
  version = "1.0.0",
  description = "Checks that the core Idris2 proofs, parser bridges, and schema artifacts exist and that no template placeholders remain.",

  checks = {
    checker_present = {
      description = "Idris2 Checker definition exists.",
      severity = "error",
      check_type = "file-exists",
      file = "src/core/Checker.idr",
    },

    grammar_present = {
      description = "Grammar specification file is present.",
      severity = "error",
      check_type = "file-exists",
      file = "src/core/Grammar.idr",
    },

    levels_present = {
      description = "Levels lattice file remains tracked.",
      severity = "warning",
      check_type = "file-exists",
      file = "src/core/Levels.idr",
    },

    schema_present = {
      description = "Schema validation proof exists.",
      severity = "warning",
      check_type = "file-exists",
      file = "src/core/Schema.idr",
    },

    bridge_present = {
      description = "ReScript bridge parser file is available.",
      severity = "error",
      check_type = "file-exists",
      file = "src/bridges/VqlUtParser.res",
    },

    no_template_placeholders = {
      description = "Template markers cannot creep into the codebase.",
      severity = "error",
      check_type = "file-pattern-guard",
      scope = ".",
      reject_patterns = ["{{PROJECT}}", "{{PLACEHOLDER}}"],
    },

    placeholder_fuzz_absent = {
      description = "Placeholder fuzz harnesses must be removed.",
      severity = "warning",
      check_type = "file-not-exists",
      file = "tests/fuzz/placeholder.txt",
    },
  },
}
in vql_ut_guard
