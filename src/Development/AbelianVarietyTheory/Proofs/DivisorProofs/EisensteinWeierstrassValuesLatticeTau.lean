import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOf
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.LatConst

theorem area_tauPair (τ : ℍ) : area (tauPair τ) = τ.im := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [area, h1, h2]
  simp [abs_of_pos τ.im_pos]

theorem wEta_one (τ : ℍ) : wEta (tauPair τ) 1 = EisensteinSeries.G2 τ := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  have h := (etaEisenstein (tauPair τ)).2
  rw [h1, h2] at h
  rw [h, one_mul, ← LegendreModelEllipticTorsion.tsum_e2Summand]
  refine tsum_congr fun m => ?_
  rw [EisensteinSeries.e2Summand]
  refine tsum_congr fun n => ?_
  simp [EisensteinSeries.eisSummand, zpow_ofNat]

theorem main : ∀ τ : ℍ, s2 (tauPair τ) = G2s τ ∧ area (tauPair τ) = τ.im := by
  intro τ
  refine ⟨?_, area_tauPair τ⟩
  have h := etaSplit (tauPair τ) 1
  rw [wEta_one, area_tauPair] at h
  rw [G2s, h]
  simp

end GlobalTheory.WpFam.LatConst
end
end

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.TauVal

theorem complex_div_pow_div_div_pow (a x k : ℂ) (n : ℕ) (hk : k ≠ 0) :
    a / k ^ n / (x / k) ^ n = a / x ^ n := by
  by_cases hx : x = 0
  · subst hx
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · simp [zero_pow h.ne']
  · rw [div_pow]; field_simp

theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [this, Complex.I_ne_zero]

theorem main : ∀ (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), IsTauOf Λ c τ → (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = s2 Λ / Ω ^ 2) ∧ ∀ (N : ℕ) (x : Fin 2 → ZMod N), wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = Λ.weierstrassP (c * tors N τ x) / Ω ^ 2 ∧ wpd N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 3 = Λ.derivWeierstrassP (c * tors N τ x) / Ω ^ 3 := by
  intro Λ c Ω τ h
  obtain ⟨_, hP, hD, hs, _⟩ := GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ h
  have hG := (GlobalTheory.WpFam.LatConst.main τ).1
  have hk := two_pi_I_ne_zero
  refine ⟨?_, fun N x => ⟨?_, ?_⟩⟩
  · rw [complex_div_pow_div_div_pow _ _ _ _ hk, hs, hG, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wp, complex_div_pow_div_div_pow _ _ _ _ hk, hP, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wpd, complex_div_pow_div_div_pow _ _ _ _ hk, hD, mul_pow, inv_mul_eq_div, div_div, mul_comm]

end GlobalTheory.WpFam.TauVal
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau : ∀ (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), IsTauOf Λ c τ → (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = s2 Λ / Ω ^ 2) ∧ ∀ (N : ℕ) (x : Fin 2 → ZMod N), wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = Λ.weierstrassP (c * tors N τ x) / Ω ^ 2 ∧ wpd N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 3 = Λ.derivWeierstrassP (c * tors N τ x) / Ω ^ 3 := by
  atlas_forward_decl GlobalTheory.WpFam.TauVal.main
end
