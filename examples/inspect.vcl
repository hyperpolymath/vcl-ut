-- SPDX-License-Identifier: MPL-2.0
--
-- Example VCL (VeriSim Consonance Language) statements.
--
-- VCL statements are propositions and epistemic requests to a consonance
-- engine, not queries against a passive store (see README.adoc). The
-- read-style `SELECT ... FROM ...` surface below is the epistemic-inspection
-- convenience; `HEXAD <uuid>` is the legacy keyword naming the octad source
-- (the eight modal witnesses). VCL-total decides admissibility of any
-- proof-bearing statement before it affects live consonance state.

-- Epistemic inspection: read consonance state across modal witnesses.
SELECT GRAPH.*, DOCUMENT.*, VECTOR.* FROM HEXAD 'entity-001'

-- Inspect cross-modal drift between two witnesses.
SELECT * FROM HEXAD 'entity-001'
  WHERE DRIFT(VECTOR, DOCUMENT) > 0.3

-- Proof-bearing statement: VCL-total must discharge the attached obligation
-- (existence + provenance) before the result is admissible.
SELECT GRAPH.* FROM HEXAD 'entity-001'
  PROOF EXISTENCE(entity-001) AND PROVENANCE(entity-001)
