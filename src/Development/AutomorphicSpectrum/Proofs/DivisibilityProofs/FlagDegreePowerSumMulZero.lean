import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Formalism.DegreeFormula.PointDegree.PowSum
import BuildAid.ForwardExisting

section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem degFl_pk_mul_eq_zero : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (k : ℕ) (G : RP Ψ N), 1 ≤ k → degFl (pk τ k * G) = 0 :=
  fun Ψ _ _ N τ k G hk => Formalism.DegreeFormula.degreePowerSumMulEqZero Ψ N τ k G hk

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_power_sum_mul_zero : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (k : ℕ) (G : RP Ψ N), 1 ≤ k → degFl (pk τ k * G) = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.degFl_pk_mul_eq_zero
