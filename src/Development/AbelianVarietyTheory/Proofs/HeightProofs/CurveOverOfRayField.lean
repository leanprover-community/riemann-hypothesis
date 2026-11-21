import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardEqIffStabilizer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurve

section Quadratic

variable {K : Type} [Field K] [NumberField K] {d : ℕ}

theorem norm_int_eq (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) (a : 𝓞 K) :
    ((Algebra.norm ℤ a : ℤ) : ℝ) = ‖φ a‖ ^ 2 := by
  rw [← GlobalTheory.QuadraticZeta.norm_eq_sq h2 hD φ, ← Algebra.coe_norm_int, Rat.cast_intCast]


theorem span_isPrime (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) {p : ℕ} (hp : p.Prime)
    {a : 𝓞 K} (ha : ‖φ a‖ ^ 2 = p) : (Ideal.span {a}).IsPrime := by
  refine Ideal.isPrime_of_irreducible_absNorm ?_
  have : Algebra.norm ℤ a = p := by
    have := (norm_int_eq h2 hD φ a).trans ha
    exact_mod_cast this
  rw [Ideal.absNorm_span_singleton, this, Int.natAbs_natCast]
  exact hp



end Quadratic

theorem ncard_congr {M R : Type} [Field M] [Field R] [NumberField M] [NumberField R] (e : M ≃+* R) (p : ℕ) :
    {v : HeightOneSpectrum (𝓞 M) | ((p : ℕ) : 𝓞 M) ∈ v.asIdeal}.ncard =
      {v : HeightOneSpectrum (𝓞 R) | ((p : ℕ) : 𝓞 R) ∈ v.asIdeal}.ncard := by
  refine Set.ncard_congr' (Equiv.subtypeEquiv
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)) fun Q => ?_)
  simp [HeightOneSpectrum.equivOfRingEquiv, HeightOneSpectrum.comap, Ideal.mem_comap]

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in

theorem _root_.GlobalTheory.FieldSize.RayExistCurve.finrank_adjoin {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    FiniteDimensional ℚ ℚ⟮r⟯ ∧ Module.finrank ℚ ℚ⟮r⟯ = 2 := by
  have hroot : aeval r (X ^ 2 + C (d : ℚ)) = 0 := by simp [hr]
  have hmon : (X ^ 2 + C (d : ℚ)).Monic := monic_X_pow_add_C _ (by norm_num)
  have hint : IsIntegral ℚ r := ⟨_, hmon, by simpa [aeval_def] using hroot⟩
  have hdeg : (X ^ 2 + C (d : ℚ)).natDegree = 2 := natDegree_X_pow_add_C
  have hirr : Irreducible (X ^ 2 + C (d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x hx
      have hx' : x ^ 2 + (d : ℚ) = 0 := by simpa using hx
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      nlinarith [sq_nonneg x]
  have hmin : minpoly ℚ r = X ^ 2 + C (d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]

theorem conj_eq_neg {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) : starRingEnd ℂ r = -r := by
  have h1 := congrArg Complex.re hr
  have h2 := congrArg Complex.im hr
  simp [sq] at h1 h2
  have h3 : (0 : ℝ) < d := by exact_mod_cast hd
  have h4 : r.re = 0 := by
    by_contra h
    have : r.im = 0 := mul_left_cancel₀ h (by linarith)
    rw [this] at h1
    nlinarith [mul_self_nonneg r.re]
  apply Complex.ext <;> simp [h4]

end GlobalTheory.FieldSize.RayExistCurve
