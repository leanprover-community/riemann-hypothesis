import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoords
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TransvMemZGam
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate

namespace GlobalTheory.MaxCuspCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem basis_exists (X : Data E r) (cu : CuspFD X ρ) : ∃ bs, IsZBasis X cu bs :=
  GlobalTheory.CuspCentre.latZ E r ρ Unit (fun _ => X) ⟨(), cu⟩


theorem chi_zero (X : Data E r) (γ : GL (Fin r) E) (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin 0
  have h1 := X.χ_add 0 0 γ hγ
  rw [add_zero] at h1
  have h0 : X.χ 0 γ ≠ 0 := fun h0 => by
    have := h γ hγ
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h2 : X.χ 0 γ * 1 = X.χ 0 γ * X.χ 0 γ := by rw [mul_one]; exact h1
  exact (mul_left_cancel₀ h0 h2).symm


theorem killed_zero (X : Data E r) (cu : CuspFD X (ρ + 1)) {c : ℝ} (hc : 0 ≤ c) :
    KilledFD X cu 0 c := by
  obtain ⟨a, ha, hΛ⟩ := exists_smul_mem X (cu.e 0)
  refine ⟨Pi.single 0 (a : E), ?_, ?_, by simpa [hq] using hc⟩
  · intro h
    have := congrFun h 0
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact ha (by exact_mod_cast this)
  · rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp)]
    simpa using hΛ




end GlobalTheory.MaxCuspCheck
