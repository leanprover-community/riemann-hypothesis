import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReLtOneOfZero
import Formalism.LandauZeroFreeBounds.Statement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrderNeTop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedExplicitFormula

section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ZeroFreeHalf

theorem inRegion_of_max {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 3 ≤ N) {ρ : ℂ}
    (h : 1 - c / 2 / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re) : Formalism.ZeroFreeDirichlet.InRegion c N ρ := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  set M := max (N : ℝ) (N * |ρ.im|) with hM
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hMN : (N : ℝ) ≤ M := le_max_left _ _
  have hMt : (N : ℝ) * |ρ.im| ≤ M := le_max_right _ _
  have hMpos : 0 < M := by linarith
  have ht := abs_nonneg ρ.im
  have hA : (N : ℝ) * (|ρ.im| + 2) ≤ M ^ 2 := by nlinarith
  have hA1 : 1 < (N : ℝ) * (|ρ.im| + 2) := by nlinarith
  have hL : 0 < Real.log ((N : ℝ) * (|ρ.im| + 2)) := Real.log_pos hA1
  have hle : Real.log ((N : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log M := by
    have e := Real.log_le_log (by linarith) hA
    rw [Real.log_pow] at e
    push_cast at e
    linarith
  have hdiv : c / (2 * Real.log M) ≤ c / Real.log ((N : ℝ) * (|ρ.im| + 2)) :=
    div_le_div_of_nonneg_left hc.le hL hle
  rw [div_div] at h
  linarith

theorem isRealChar_of_sq {N : ℕ} (χ : DirichletCharacter ℂ N) (h : χ ^ 2 = 1) : IsRealChar χ := by
  intro a
  by_cases ha : IsUnit a
  · have h2 : χ a * χ a = 1 := by
      rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, h, MulChar.one_apply ha]
    rcases mul_self_eq_one_iff.mp h2 with e | e <;> simp [e]
  · simp [MulChar.map_nonunit χ ha]

theorem ne_one_of_isPrimitive {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (hN : 3 ≤ N) : χ ≠ 1 := by
  intro h1
  rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hp
  omega

theorem main : Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∃ c : ℝ, 0 < c ∧ (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re → IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (LFunction χ) ρ = 1 ∧ ∀ ρ' : ℂ, LFunction χ ρ' = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧ (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)) := by
  intro hZ
  obtain ⟨c, hc, hZ⟩ := hZ
  refine ⟨c / 2, by positivity, ?_, ?_⟩
  · intro N _ χ hp hN ρ hρ hreg
    have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hp hN
    obtain ⟨hsq, -, him, hder, huniq⟩ :=
      hZ N χ ρ (inRegion_of_max hc hN hreg) ⟨Or.inl hχ1, hρ⟩
    refine ⟨isRealChar_of_sq χ hsq, him, ?_, ?_⟩
    · have han : AnalyticAt ℂ (LFunction χ) ρ :=
        (DirichletCharacter.differentiable_LFunction hχ1).analyticAt ρ
      simp [analyticOrderNatAt, han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hder]
    · intro ρ' hρ' hreg'
      exact (huniq χ ρ' (inRegion_of_max hc hN hreg') ⟨Or.inl hχ1, hρ'⟩).2
  · intro ρ hρ _ hre1
    by_contra hlt
    rw [not_le] at hlt
    have ht := abs_nonneg ρ.im
    have hR : Formalism.ZeroFreeDirichlet.InRegion c 1 ρ := by
      unfold Formalism.ZeroFreeDirichlet.InRegion
      have ha : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith)
      have hab : Real.log (|ρ.im| + 2) ≤ 2 * Real.log (|ρ.im| + 3) := by
        have e := Real.log_le_log (by linarith) (by linarith : |ρ.im| + 2 ≤ |ρ.im| + 3)
        have e2 : 0 ≤ Real.log (|ρ.im| + 3) := Real.log_nonneg (by linarith)
        linarith
      have hdiv := div_le_div_of_nonneg_left hc.le ha hab
      rw [div_div] at hlt
      simp only [Nat.cast_one, one_mul]
      linarith
    have hne : ρ ≠ 1 := by
      rintro rfl
      simp at hre1
    have hZ0 : Formalism.ZeroFreeDirichlet.IsLZero (1 : DirichletCharacter ℂ 1) ρ :=
      ⟨Or.inr hne, by rw [DirichletCharacter.LFunction_modOne_eq]; exact hρ⟩
    exact (hZ 1 1 ρ hR hZ0).2.1 rfl

end GlobalTheory.ZeroFreeHalf
end

section
open Complex DirichletCharacter

namespace GlobalTheory.LandauPageRegion

theorem inRegion_mono {c c' : ℝ} (h : c ≤ c') (q : ℕ) [NeZero q] {s : ℂ}
    (hs : Formalism.ZeroFreeDirichlet.InRegion c q s) : 1 - c' / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL : 0 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
    nlinarith
  have hdiv : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c' / Real.log ((q : ℝ) * (|s.im| + 2)) :=
    div_le_div_of_nonneg_right h hL
  have hs' : 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hs
  linarith

private theorem real_zero_of_mem_zeroFreeRegion {c₁ c₂ c₃ c : ℝ} (hc₁ : c ≤ c₁) (hc₂ : c ≤ c₂) (hc₃ : c ≤ c₃)
    (hA : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), χ ≠ 1 → LFunction χ s = 0 →
      (χ ^ 2 ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c₁ / Real.log (q * (|s.im| + 2)))
    (hC : ∀ (q : ℕ) [NeZero q] (s : ℂ), s ≠ 1 → LFunction (1 : DirichletCharacter ℂ q) s = 0 →
      s.re < 1 - c₃ / Real.log (q * (|s.im| + 2)))
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {s : ℂ}
    (hs : Formalism.ZeroFreeDirichlet.InRegion c q s) (hz : Formalism.ZeroFreeDirichlet.IsLZero χ s) :
    χ ≠ 1 ∧ χ ^ 2 = 1 ∧ s.im = 0 ∧ 1 - c₂ / Real.log (2 * q) ≤ s.re ∧
      LFunction χ (s.re : ℂ) = 0 ∧ s = (s.re : ℂ) := by
  obtain ⟨hne, hL⟩ := hz
  have h1 : χ ≠ 1 := by
    rintro rfl
    have hs1 : s ≠ 1 := hne.resolve_left (fun h => h rfl)
    have h3 := hC q s hs1 hL
    have h4 := inRegion_mono hc₃ q hs
    linarith
  have h2 : ¬ (χ ^ 2 ≠ 1 ∨ s.im ≠ 0) := by
    intro h
    have h3 := hA q χ s h1 hL h
    have h4 := inRegion_mono hc₁ q hs
    linarith
  push Not at h2
  obtain ⟨hsq, him⟩ := h2
  have hseq : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨h1, hsq, him, ?_, ?_, hseq⟩
  · have h4 := inRegion_mono hc₂ q hs
    rw [him, abs_zero, zero_add, mul_comm] at h4
    exact h4
  · rw [← hseq]
    exact hL

theorem main : Formalism.ZeroFreeDirichlet.ZFRDirichlet := by
  obtain ⟨c₁, hc₁, hA⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨c₂, hc₂, hB⟩ := GlobalTheory.RealZeroNearOne.main
  obtain ⟨c₃, hc₃, hC⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  refine ⟨min c₁ (min c₂ c₃), lt_min hc₁ (lt_min hc₂ hc₃), ?_⟩
  intro q _ χ s hs hz
  have m₁ : min c₁ (min c₂ c₃) ≤ c₁ := min_le_left _ _
  have m₂ : min c₁ (min c₂ c₃) ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have m₃ : min c₁ (min c₂ c₃) ≤ c₃ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨h1, hsq, him, hre, hL, hseq⟩ := real_zero_of_mem_zeroFreeRegion m₁ m₂ m₃ hA hC hs hz
  have hself := hB q χ χ s.re s.re h1 h1 hsq hsq hre hre hL hL
  refine ⟨hsq, h1, him, ?_, ?_⟩
  · rw [hseq]
    exact hself.2.2
  · intro χ' s' hs' hz'
    obtain ⟨h1', hsq', -, hre', hL', hseq'⟩ := real_zero_of_mem_zeroFreeRegion m₁ m₂ m₃ hA hC hs' hz'
    obtain ⟨hχ, hβ, -⟩ := hB q χ' χ s'.re s.re h1' h1 hsq' hsq hre' hre hL' hL
    refine ⟨hχ, ?_⟩
    rw [hseq', hseq, hβ]

end GlobalTheory.LandauPageRegion
end

section
open Complex DirichletCharacter Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ZerosNearOne

theorem density_and_regions : ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧
    (∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((∑ p ∈ T, analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C1 * Q ^ ((1 : ℝ) / 4)) ∧
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re → IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (LFunction χ) ρ = 1 ∧ ∀ ρ' : ℂ, LFunction χ ρ' = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.ZeroDensityMult.zero_density_mult
  obtain ⟨c, hc, H2, H3⟩ := GlobalTheory.ZeroFreeHalf.main GlobalTheory.LandauPageRegion.main
  exact ⟨C, c, hC, hc, H, H2, H3⟩

end GlobalTheory.ZerosNearOne
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.ZerosNearOne

theorem main : ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ D : D7, adm6 D C1 c := by
  obtain ⟨C, c, hC, hc, H⟩ := density_and_regions
  exact ⟨C, c, hC, hc, fun _ => H⟩

end GlobalTheory.ZerosNearOne
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.ZeroBounds

theorem explicit_formula_and_window_count :
    (∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm7 D C) ∧ ∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm11 D C := by
  obtain ⟨C, hC, h⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C', hC', h'⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  exact ⟨⟨C, hC, fun _ => h⟩, ⟨C', hC', fun _ => h'⟩⟩

end GlobalTheory.ZeroBounds
end

section
namespace GlobalTheory.ThinScaleLiterature

theorem litThin : Formalism.MainNotions.LitThin :=
  ⟨GlobalTheory.ZerosNearOne.main, GlobalTheory.ZeroBounds.explicit_formula_and_window_count⟩

end GlobalTheory.ThinScaleLiterature
end
