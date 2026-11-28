import Main
import Lib.Cite.Report

/-!
Lists the citations that the proof of the Riemann hypothesis depends on: those of `@[cite]` and
Mathlib's cross-references. This file does not start with `module`, so the proofs of imported
theorems are loaded and `#citations` follows them. Run it from the root of the repository, with
`Main` and `Lib.Cite.Report` built:

    lake env lean scripts/cite/Citations.lean
-/

#citations riemannHypothesis
