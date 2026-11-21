import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QsBddAboveOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIterated
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLine

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_norm_qs_of_one_le_im : ∀ (b : ℕ → ℂ), PolyB b → ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖qs b τ‖ ≤ M := by
  atlas_forward_decl GlobalTheory.EisM.qs_bdd_above_one
