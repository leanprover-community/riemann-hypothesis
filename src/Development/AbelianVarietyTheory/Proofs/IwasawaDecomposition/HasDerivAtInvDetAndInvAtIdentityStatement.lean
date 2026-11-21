import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInvDetAndInvAtIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
import BuildAid.ForwardExisting

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_inv_det_and_inv_at_identity : ∀ (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (M' : Matrix (Fin n) (Fin n) ℂ), M 0 = 1 → (∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0) → HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 ∧ ∀ i j, HasDerivAt (fun t => (M t)⁻¹ i j) (-M' i j) 0 := by
  atlas_forward_decl GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv
