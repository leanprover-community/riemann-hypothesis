import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalExt

section
theorem UpperTheory.Gal.InertialTypesAlt.L.hilbert_ninety_frobenius_twisted_finite_algebra :
    UpperTheory.Gal.InertialTypesAlt.L.FrobeniusTwistedHilbertNinety := by
  intro F₀ F₁ _ _ _ _ _ sb hsb A _ _ _ τ hτ hd c hc
  classical
  have hfrob : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hsb]
  have hgen : ∀ t : F₁ ≃ₐ[F₀] F₁, t ∈ Subgroup.zpowers sb := by
    intro t
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F₀ F₁).2 t
    rw [← hi, ← hfrob]
    exact Subgroup.npow_mem_zpowers _ _
  have hG : UpperTheory.ConvolutionTheory.D.IsGal sb (Module.finrank F₀ F₁) := UpperTheory.ConvolutionTheory.D.galField F₀ F₁ sb hgen
  let S : Subring A := (τ : A →+* A).eqLocus (RingHom.id A)
  let f : F₀ →+* S := ((algebraMap F₁ A).comp (algebraMap F₀ F₁)).codRestrict S (fun z => by
    change τ (algebraMap F₁ A (algebraMap F₀ F₁ z)) = algebraMap F₁ A (algebraMap F₀ F₁ z)
    rw [hτ, AlgEquiv.commutes])
  letI : Algebra F₀ S := f.toAlgebra
  haveI : Module.Finite F₀ S := Module.Finite.of_finite
  let σ : A ≃ₐ[S] A := AlgEquiv.ofRingEquiv (f := τ) (fun r => r.2)
  have hpow : ∀ (j : ℕ) (x : A), (σ ^ j) x = τ^[j] x := by
    intro j x
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, Function.iterate_succ_apply']
      rfl
  have hpowF : ∀ (j : ℕ) (z : F₁), τ^[j] (algebraMap F₁ A z) = algebraMap F₁ A ((sb ^ j) z) := by
    intro j z
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, hτ, pow_succ', AlgEquiv.mul_apply]
  have hGal : UpperTheory.ConvolutionTheory.D.IsGal σ (Module.finrank F₀ F₁) := by
    refine ⟨hG.pos, AlgEquiv.ext fun x => ?_, Subtype.val_injective, fun r hr => ⟨⟨r, hr⟩, rfl⟩, ?_⟩
    · rw [hpow, hd]; rfl
    · obtain ⟨s, x, y, h⟩ := hG.sep
      refine ⟨s, fun i => algebraMap F₁ A (x i), fun i => algebraMap F₁ A (y i), fun j hj => ?_⟩
      simp only [hpow, hpowF, ← map_mul, ← map_sum]
      rw [h j hj]
      split_ifs <;> simp
  have hu : IsUnit c := by
    have h1 : c ∣ UpperTheory.Gal.InertialTypesAlt.L.itN τ (Module.finrank F₀ F₁) c :=
      Finset.dvd_prod_of_mem (fun i => τ^[i] c) (Finset.mem_range.2 hG.pos)
    rw [hc] at h1
    exact isUnit_of_dvd_one h1
  obtain ⟨z, hz⟩ := UpperTheory.ConvolutionTheory.D.h90 F₀ F₀ S A σ _ hGal hu.unit (by
    simp only [hpow, IsUnit.unit_spec]
    exact hc)
  exact ⟨z, hz⟩
end

section
private theorem UpperTheory.Gal.InertialTypesAlt.L.range_eq_ker_of_exact {U : Type} [CommGroup U] [Finite U]
    (N D : U →* U) (h1 : N.range ≤ D.ker) (h2 : N.ker = D.range) : N.range = D.ker := by
  apply Subgroup.eq_of_le_of_card_ge h1
  have c1 := Subgroup.card_mul_index N.ker
  have c2 := Subgroup.card_mul_index D.ker
  rw [Subgroup.index_ker, h2] at c1
  rw [Subgroup.index_ker] at c2
  have hp : 0 < Nat.card D.range := Nat.card_pos
  have e : Nat.card D.range * Nat.card N.range = Nat.card D.range * Nat.card D.ker := by
    nlinarith
  exact (Nat.eq_of_mul_eq_mul_left hp e).ge

theorem UpperTheory.Gal.InertialTypesAlt.L.normFin :
    UpperTheory.Gal.InertialTypesAlt.L.NormFin := by
  intro F₀ F₁ _ _ _ _ _ sb hsb A _ _ _ τ hτ hper x hx hfix
  have H := UpperTheory.Gal.InertialTypesAlt.L.hilbert_ninety_frobenius_twisted_finite_algebra F₀ F₁ sb hsb A τ hτ hper
  generalize Module.finrank F₀ F₁ = d at hper H ⊢
  have hit : ∀ i (a b : A), (⇑τ)^[i] (a * b) = (⇑τ)^[i] a * (⇑τ)^[i] b := by
    intro i
    induction i with
    | zero => intro a b; rfl
    | succ n ih => intro a b; simp only [Function.iterate_succ_apply', ih, map_mul]
  have hit1 : ∀ i, (⇑τ)^[i] (1 : A) = 1 := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_one]
  have hmul : ∀ a b : A, UpperTheory.Gal.InertialTypesAlt.L.itN τ d (a * b)
      = UpperTheory.Gal.InertialTypesAlt.L.itN τ d a * UpperTheory.Gal.InertialTypesAlt.L.itN τ d b := by
    intro a b
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, hit, Finset.prod_mul_distrib]
  have hone : UpperTheory.Gal.InertialTypesAlt.L.itN τ d 1 = 1 := by
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, hit1, Finset.prod_const_one]
  have hinv : ∀ a : A, τ (UpperTheory.Gal.InertialTypesAlt.L.itN τ d a) = UpperTheory.Gal.InertialTypesAlt.L.itN τ d a := by
    intro a
    have ha := hper a
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, map_prod]
    have e : ∀ i, τ ((⇑τ)^[i] a) = (⇑τ)^[i + 1] a :=
      fun i => (Function.iterate_succ_apply' _ _ _).symm
    simp only [e]
    cases d with
    | zero => simp
    | succ k =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => (⇑τ)^[i] a), ha]
      rfl
  have hτN : ∀ a : A, UpperTheory.Gal.InertialTypesAlt.L.itN τ d (τ a) = UpperTheory.Gal.InertialTypesAlt.L.itN τ d a := by
    intro a
    rw [← hinv a]
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, map_prod]
    exact Finset.prod_congr rfl (fun i _ => by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'])
  obtain ⟨N, hN⟩ : ∃ N : Aˣ →* Aˣ, ∀ u, (N u : A) = UpperTheory.Gal.InertialTypesAlt.L.itN τ d u :=
    ⟨Units.map { toFun := UpperTheory.Gal.InertialTypesAlt.L.itN τ d, map_one' := hone, map_mul' := hmul },
      fun u => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Aˣ →* Aˣ, ∀ u, (T u : A) = τ u :=
    ⟨Units.map (MonoidHomClass.toMonoidHom τ), fun u => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Aˣ →* Aˣ, ∀ u, D u = u / T u := ⟨MonoidHom.id _ / T, fun u => rfl⟩
  have hr : N.range ≤ D.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker, hD, div_eq_one]
    ext
    rw [hT, hN, hinv]
  have hk : N.ker = D.range := by
    ext c
    constructor
    · intro hc
      rw [MonoidHom.mem_ker, Units.ext_iff, hN, Units.val_one] at hc
      obtain ⟨y, hy⟩ := H c hc
      refine ⟨y, ?_⟩
      rw [hD, div_eq_iff_eq_mul]
      ext
      rw [Units.val_mul, hT]
      exact hy.symm
    · rintro ⟨y, rfl⟩
      rw [MonoidHom.mem_ker, hD, map_div, div_eq_one]
      ext
      rw [hN, hN, hT, hτN]
  have heq := UpperTheory.Gal.InertialTypesAlt.L.range_eq_ker_of_exact N D hr hk
  have hu : hx.unit ∈ D.ker := by
    rw [MonoidHom.mem_ker, hD, div_eq_one]
    ext
    rw [hT, IsUnit.unit_spec, hfix]
  rw [← heq] at hu
  obtain ⟨y, hy⟩ := hu
  exact ⟨y, by rw [← hN, hy, IsUnit.unit_spec]⟩
end
