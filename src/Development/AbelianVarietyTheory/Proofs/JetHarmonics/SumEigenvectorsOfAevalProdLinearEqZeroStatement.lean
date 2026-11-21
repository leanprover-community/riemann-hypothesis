import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumEigenvectorsOfAevalProdLinearEqZero
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import BuildAid.ForwardExisting

open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_decomp_of_aeval_prod_eq_zero : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → Polynomial.aeval (-Ω) (∏ s, (Polynomial.X + Polynomial.C (ν s))) = 0 → ∀ w : N, ∃ v : Fin n → N, (∀ s, Ω (v s) = ν s • v s) ∧ w = ∑ s, v s := by
  atlas_forward_decl GlobalTheory.sum_eigenvectors_of_aeval_prod_linear_eq_zero
