-- SPDX-License-Identifier: MPL-2.0
--
-- Example VCL (VeriSim Consonance Language) statements.
--
-- VCL statements are propositions and epistemic requests to a consonance
-- engine, not queries against a passive store (see README.adoc). The
-- read-style `SELECT ... FROM ...` surface below is the epistemic-inspection
-- convenience; `OCTAD <uuid>` is the preferred spelling and `HEXAD <uuid>` is
-- a legacy alias for the same fixed eight-slot Octad source. Neither spelling
-- selects a modality profile. VCL-total decides admissibility of any
-- proof-bearing statement before it affects live consonance state.

-- Epistemic inspection: read consonance state across modal witnesses.
SELECT GRAPH.*, DOCUMENT.*, VECTOR.* FROM OCTAD 'entity-001'

-- Inspect cross-modal drift between two witnesses.
SELECT * FROM OCTAD 'entity-001'
  WHERE DRIFT(VECTOR, DOCUMENT) > 0.3

-- The legacy spelling remains accepted by the current Rust parser.
-- Proof-bearing statement: VCL-total must discharge the attached obligation
-- (existence + provenance) before the result is admissible.
SELECT GRAPH.* FROM HEXAD 'entity-001'
  PROOF EXISTENCE(entity-001) AND PROVENANCE(entity-001)
