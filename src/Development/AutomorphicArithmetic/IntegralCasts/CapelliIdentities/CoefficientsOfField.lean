import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

section
open Polynomial

theorem UpperTheory.padicAlgCl_isIntegral_iff_norm_le_one :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l), IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ (1 : ℝ) := by
  intro l _ x
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hx
  have key : ‖x‖ ≤ (1 : ℝ) ↔ ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 :=
    spectralValue_le_one_iff hm
  rw [key]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact ((minpoly ℤ_[l] x).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]
end

section
open Polynomial

private theorem isIntegral_of_spectralNorm_le_one (l : ℕ) [Fact l.Prime] (L : Type*) [Field L]
    [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L]
    [IsScalarTower ℤ_[l] ℚ_[l] L] (x : L) (hx : spectralNorm ℚ_[l] L x ≤ 1) :
    IsIntegral ℤ_[l] x := by
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).mp hx
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

private theorem isIntegral_or_isIntegral_inv (l : ℕ) [Fact l.Prime] (L : Type*) [Field L]
    [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L]
    [IsScalarTower ℤ_[l] ℚ_[l] L] (x : L) :
    IsIntegral ℤ_[l] x ∨ IsIntegral ℤ_[l] x⁻¹ := by
  by_cases hx : spectralNorm ℚ_[l] L x ≤ 1
  · exact Or.inl (isIntegral_of_spectralNorm_le_one l L x hx)
  · refine Or.inr (isIntegral_of_spectralNorm_le_one l L x⁻¹ ?_)
    have hx1 : 1 < spectralNorm ℚ_[l] L x := not_le.mp hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [spectralNorm_zero] at hx1
      exact absurd hx1 (by norm_num)
    have hmul : spectralNorm ℚ_[l] L x * spectralNorm ℚ_[l] L x⁻¹ = 1 := by
      have h := spectralAlgNorm_mul (K := ℚ_[l]) (L := L) x x⁻¹
      rw [mul_inv_cancel₀ hx0, spectralAlgNorm_one] at h
      exact h.symm
    have h0 : 0 ≤ spectralNorm ℚ_[l] L x⁻¹ := spectralNorm_nonneg _
    nlinarith

private theorem isDiscreteValuationRing_integralClosure (l : ℕ) [Fact l.Prime] (L : Type*) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L] [IsScalarTower ℤ_[l] ℚ_[l] L] :
    IsDiscreteValuationRing (integralClosure ℤ_[l] L) := by
  have hD : IsDedekindDomain (integralClosure ℤ_[l] L) :=
    integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] L
  have hF : IsFractionRing (integralClosure ℤ_[l] L) L :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] L
  have hV : ValuationRing (integralClosure ℤ_[l] L) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _ L]
    intro x
    rcases isIntegral_or_isIntegral_inv l L x with h | h
    · exact Or.inl ⟨⟨x, h⟩, rfl⟩
    · exact Or.inr ⟨⟨x⁻¹, h⟩, rfl⟩
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] L)) := by
    intro a b hab
    have h : algebraMap ℤ_[l] L a = algebraMap ℤ_[l] L b :=
      congrArg (fun z : integralClosure ℤ_[l] L => (z : L)) hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] L, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] L b]
      at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] L).injective h)
  have hnf : ¬ IsField (integralClosure ℤ_[l] L) := fun h =>
    IsDiscreteValuationRing.not_isField ℤ_[l] (isField_of_isIntegral_of_isField hinj h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[l] L) hnf).out 0 1).mpr hV

theorem UpperTheory.integralClosure_isDVR :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] ↥K], IsDiscreteValuationRing ↥(integralClosure ℤ_[l] ↥K) := by
  intro l _ K _
  exact isDiscreteValuationRing_integralClosure l K
end

section
theorem UpperTheory.Reformulated.B.CoefficientsOfField.coef_of_field :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] ↥K],
    ∃ (c : UpperTheory.V.HV.Coef l),
      ∀ x ∈ K,
        ‖x‖ ≤ (1 : ℝ) → x ∈ c.O := by
  intro l _ K _
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  have hd : IsDiscreteValuationRing (integralClosure ℤ_[l] K) := UpperTheory.integralClosure_isDVR K
  have hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K _
  refine ⟨⟨(integralClosure ℤ_[l] K).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x hx h1 => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (isIntegral_algHom_iff f hf).1 ((UpperTheory.padicAlgCl_isIntegral_iff_norm_le_one x).2 h1)
end
