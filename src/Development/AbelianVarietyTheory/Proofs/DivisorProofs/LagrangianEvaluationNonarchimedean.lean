import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUnramifiedAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledUniformization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackEllipticModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfSurjectiveOnPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFiniteFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLatticeOrderCoprimeIndex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismTrivialOnReducedKernel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isIntegral_j_of_isIntLattice : ∀ (d : ℕ) (Λ : PeriodPair), d.Prime → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    IsIntegral ℤ (1728 * Λ.g₂ ^ 3 / latDisc Λ) := by
  intro d Λ hd hΛ
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau Λ
  have hj := g₂_cube_div_eq_modularJ ha h
  have hL : latDisc Λ = Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 := rfl
  rw [hL, hj]
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hsq : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  have hwint : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    · simp [Polynomial.eval₂_add, hsq]
  refine isIntegral_modularJ_of_mul_mem (α := w) (fun m hm => ?_) fun x hx ↦ ?_
  · have := congrArg Complex.im hm
    simp [hw] at this
    exact hd.ne_zero this
  · have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ Λ.lattice := fun y ↦ by
      rw [h, Submodule.mem_span_pair]
      simp [mul_right_inj' ha]
    rw [key] at hx ⊢
    obtain ⟨hi, p, q, hpq⟩ := (hΛ _).1 hx
    rw [mul_left_comm]
    refine (hΛ _).2 ⟨hwint.mul hi, -(d : ℚ) * q, p, ?_⟩
    rw [hpq]
    push_cast
    linear_combination (q : ℂ) * hsq

end GlobalTheory
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.j_invariant_integral : ∀ (d : ℕ) (Λ : PeriodPair), d.Prime → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    IsIntegral ℤ (1728 * Λ.g₂ ^ 3 / latDisc Λ) := by
  atlas_forward_decl GlobalTheory.isIntegral_j_of_isIntLattice
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceRingCurve

theorem exists_isPlaceOver_le : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k : IntermediateField ℚ ℂ),
    FiniteDimensional ℚ k → ∃ R : Subring ℂ, IsPlaceOver l lam k R ∧ ∀ x ∈ R, x ∈ k := by
  intro l _ lam k hk
  haveI : NumberField k := { }
  have hle : k ≤ algebraicClosure ℚ ℂ := fun x hx =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨x, hx⟩ : k)).algHom k.val)
  let f : k →+* ℂ_[l] := lam.comp (IntermediateField.inclusion hle).toRingHom
  have hO : ∀ a : 𝓞 k, ‖f a‖ ≤ 1 := fun a =>
    GlobalTheory.PlaceRingExists.norm_le_one_of_isIntegral_int (by
      convert map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe a) using 1 <;>
        first | exact Subsingleton.elim _ _ | rfl)
  let P : Ideal (𝓞 k) :=
    { carrier := {a | ‖f a‖ < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
        calc ‖f c‖ * ‖f a‖ ≤ 1 * ‖f a‖ := by gcongr; exact hO c
          _ < 1 := by simpa using ha }
  have hmemP : ∀ a, a ∈ P ↔ ‖f a‖ < 1 := fun _ => Iff.rfl
  have hPp : P.IsPrime := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmemP]; simp
    · have e : ((a * b : 𝓞 k) : k) = (a : k) * b := rfl
      rw [hmemP, e, map_mul, norm_mul] at hab
      by_contra h
      push_neg at h
      rw [hmemP, hmemP, not_lt, not_lt] at h
      nlinarith [hO a, hO b]
  have hlP : ((l : ℕ) : 𝓞 k) ∈ P := by
    have e : (((l : ℕ) : 𝓞 k) : k) = ((l : ℕ) : k) := by simp
    rw [hmemP, e, map_natCast]; exact GlobalTheory.PlaceRingExists.norm_prime_lt_one l
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hlP
    exact (Fact.out : l.Prime).ne_zero hlP
  have hS : P.primeCompl ≤ nonZeroDivisors (𝓞 k) := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra.ofField k P.primeCompl hS
  haveI : IsLocalization.AtPrime A P := Localization.subalgebra.isLocalization_ofField k _ hS
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 k) hP0 A
  haveI : IsFractionRing A k := Localization.subalgebra.isFractionRing_ofField k _ hS
  have hS1 : ∀ s : 𝓞 k, s ∈ P.primeCompl → ‖f s‖ = 1 := fun s hs =>
    le_antisymm (hO s) (not_lt.1 hs)
  have hA : ∀ x : k, x ∈ A ↔ ‖f x‖ ≤ 1 := by
    intro x
    constructor
    · rintro ⟨r, s, hs, rfl⟩
      rw [map_mul, map_inv₀, norm_mul, norm_inv]
      change ‖f (r : k)‖ * ‖f (s : k)‖⁻¹ ≤ 1
      rw [hS1 s hs, inv_one, _root_.mul_one]; exact hO r
    · intro hx
      by_cases hx0 : x = 0
      · rw [hx0]; exact zero_mem A
      rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩
      · rw [← ha]; exact a.2
      · obtain ⟨r, s, hs, hrs⟩ := a.2
        have ha' : (a : k) = x⁻¹ := ha
        rw [ha'] at hrs
        have hs0 : (s : k) ≠ 0 := by
          intro h0; apply hs; rw [show s = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]; exact P.zero_mem
        have hr0 : (r : k) ≠ 0 := by
          intro h0
          have h0' : algebraMap (𝓞 k) k r = 0 := h0
          rw [h0', zero_mul, inv_eq_zero] at hrs; exact hx0 hrs
        have hxe : x = (s : k) * (r : k)⁻¹ := by
          rw [← inv_inv x, hrs, mul_inv, inv_inv, mul_comm]
        have hr1 : ‖f r‖ = 1 := by
          refine le_antisymm (hO r) ?_
          have := hx
          rw [hxe, map_mul, map_inv₀, norm_mul, norm_inv] at this
          change ‖f (s : k)‖ * ‖f (r : k)‖⁻¹ ≤ 1 at this
          rw [hS1 s hs, _root_.one_mul] at this
          have hpos : 0 < ‖f (r : k)‖ := norm_pos_iff.2 ((map_ne_zero f).2 hr0)
          rwa [inv_le_one₀ hpos] at this
        exact ⟨s, r, fun h => by have h' := (hmemP r).1 h; rw [hr1] at h'; exact lt_irrefl _ h', hxe⟩

  let g : k →+* ℂ := k.val.toRingHom
  let R : Subring ℂ := A.toSubring.map g
  let e : A.toSubring ≃+* R := Subring.equivMapOfInjective A.toSubring g g.injective
  haveI : IsDiscreteValuationRing A.toSubring := inferInstanceAs (IsDiscreteValuationRing A)
  haveI : IsDiscreteValuationRing R := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  refine ⟨R, ⟨this, ?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨x, hxA, rfl⟩ := Subring.mem_map.1 hz
    refine ⟨hle x.2, ?_⟩
    rw [Real.rpow_zero]
    exact (hA x).1 hxA
  · rintro z hz ⟨h, hn⟩
    rw [Real.rpow_zero] at hn
    exact Subring.mem_map.2 ⟨⟨z, hz⟩, (hA _).2 hn, rfl⟩
  · intro z hz
    obtain ⟨x, -, rfl⟩ := Subring.mem_map.1 hz
    exact x.2

theorem norm_natCast_eq_one {l : ℕ} [Fact l.Prime] {n : ℕ} (h : l.Coprime n) : ‖((n : ℕ) : ℂ_[l])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[l]) = ((algebraMap ℚ_[l] (PadicAlgCl l) (n : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) := by simp
  rw [e, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
  exact h

theorem norm_natCast_le {l : ℕ} [Fact l.Prime] (n : ℕ) : ‖((n : ℕ) : ℂ_[l])‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one _ n

theorem norm_add_of_lt {l : ℕ} [Fact l.Prime] {x y : ℂ_[l]} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem deuring_norm {l : ℕ} [Fact l.Prime] (hl : l ≠ 3) {a j : ℂ_[l]} (hj : ‖j‖ ≤ 1)
    (h : (a * (a ^ 3 - 24)) ^ 3 = j * (a ^ 3 - 27)) : ‖a‖ ≤ 1 ∧ 1 ≤ ‖a ^ 3 - 27‖ := by
  have h3 : ‖(3 : ℂ_[l])‖ = 1 := by
    exact_mod_cast norm_natCast_eq_one (l := l) (n := 3) ((Nat.coprime_primes Fact.out Nat.prime_three).2 hl)
  have h24 : ‖(-24 : ℂ_[l])‖ ≤ 1 := by rw [norm_neg]; exact_mod_cast norm_natCast_le (l := l) 24
  have h27 : ‖(27 : ℂ_[l])‖ = 1 := by rw [show (27 : ℂ_[l]) = 3 ^ 3 by norm_num, norm_pow, h3, one_pow]
  have hn := congrArg norm h
  rw [mul_pow, norm_mul, norm_mul, norm_pow (a ^ 3 - 24)] at hn
  constructor
  · by_contra ha
    have ht : 1 < ‖a ^ 3‖ := by rw [norm_pow]; exact one_lt_pow₀ (not_le.1 ha) (by norm_num)
    have e1 : ‖a ^ 3 - 24‖ = ‖a ^ 3‖ := by rw [sub_eq_add_neg]; exact norm_add_of_lt (h24.trans_lt ht)
    have e2 : ‖a ^ 3 - 27‖ = ‖a ^ 3‖ := by
      rw [sub_eq_add_neg]; exact norm_add_of_lt (by rw [norm_neg, h27]; exact ht)
    rw [e1, e2] at hn
    have h1 : 1 < ‖a ^ 3‖ ^ 3 := one_lt_pow₀ ht (by norm_num)
    nlinarith
  · by_contra hd
    have hd := not_le.1 hd
    have e1 : ‖a ^ 3 - 24‖ = 1 := by
      rw [show a ^ 3 - 24 = 3 + (a ^ 3 - 27) by ring, norm_add_of_lt (by rw [h3]; exact hd), h3]
    have e2 : ‖a ^ 3‖ = 1 := by
      rw [show a ^ 3 = 27 + (a ^ 3 - 27) by ring, norm_add_of_lt (by rw [h27]; exact hd), h27]
    rw [e1, e2] at hn
    nlinarith [norm_nonneg j, norm_nonneg (a ^ 3 - 27)]

theorem legendre_norm {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {a j : ℂ_[l]} (hj : ‖j‖ ≤ 1)
    (h : (16 * (a * (a - 1) + 1)) ^ 3 = j * (16 * (a * (a - 1)) ^ 2)) :
    ‖a‖ ≤ 1 ∧ 1 ≤ ‖16 * (a * (a - 1)) ^ 2‖ := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    exact_mod_cast norm_natCast_eq_one (l := l) (n := 2) ((Nat.coprime_primes Fact.out Nat.prime_two).2 hl)
  have h16 : ‖(16 : ℂ_[l])‖ = 1 := by rw [show (16 : ℂ_[l]) = 2 ^ 4 by norm_num, norm_pow, h2, one_pow]
  have hn := congrArg norm h
  simp only [norm_pow, norm_mul (16 : ℂ_[l]), norm_mul j, h16, _root_.one_mul] at hn ⊢
  set b := a * (a - 1) with hb
  constructor
  · by_contra ha
    have ha := not_le.1 ha
    have e0 : ‖a - 1‖ = ‖a‖ := by rw [sub_eq_add_neg]; exact norm_add_of_lt (by rw [norm_neg, norm_one]; exact ha)
    have ht : 1 < ‖b‖ := by rw [hb, norm_mul, e0]; nlinarith
    rw [norm_add_of_lt (by rw [norm_one]; exact ht)] at hn
    have h1 : 0 < ‖b‖ ^ 2 := by positivity
    nlinarith
  · by_contra hd
    have hd := not_le.1 hd
    have hb1 : ‖b‖ < 1 := by
      by_contra h'
      exact absurd hd (not_lt.2 (one_le_pow₀ (not_lt.1 h')))
    rw [add_comm, norm_add_of_lt (by rw [norm_one]; exact hb1), norm_one] at hn
    nlinarith [norm_nonneg j, sq_nonneg ‖b‖]

theorem descend (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (j : algebraicClosure ℚ ℂ)
    (V : WeierstrassCurve (algebraicClosure ℚ ℂ)) (h₁ : ‖lam V.a₁‖ ≤ 1) (h₂ : ‖lam V.a₂‖ ≤ 1) (h₃ : ‖lam V.a₃‖ ≤ 1)
    (h₄ : ‖lam V.a₄‖ ≤ 1) (h₆ : ‖lam V.a₆‖ ≤ 1) (hΔ : 1 ≤ ‖lam V.Δ‖) (hc : V.c₄ ^ 3 = j * V.Δ) :
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ) (W : WeierstrassCurve R₁), FiniteDimensional ℚ k₁ ∧
      IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧ IsUnit W.Δ ∧
      ((W.c₄ : R₁) : ℂ) ^ 3 = (j : ℂ) * ((W.Δ : R₁) : ℂ) := by
  let S : Set ℂ := {(V.a₁ : ℂ), (V.a₂ : ℂ), (V.a₃ : ℂ), (V.a₄ : ℂ), (V.a₆ : ℂ)}
  haveI : Finite S := (Set.toFinite S).to_subtype
  have hi : ∀ x : algebraicClosure ℚ ℂ, IsIntegral ℚ (x : ℂ) := fun x => (mem_algebraicClosure_iff.1 x.2).isIntegral
  have hk : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro x (rfl | rfl | rfl | rfl | rfl) <;> exact hi _)
  obtain ⟨R, hR, hRk⟩ := exists_isPlaceOver_le l lam _ hk
  have hm : ∀ x : algebraicClosure ℚ ℂ, (x : ℂ) ∈ IntermediateField.adjoin ℚ S → ‖lam x‖ ≤ 1 → (x : ℂ) ∈ R :=
    fun x hx hn => hR.2.2 _ hx ⟨x.2, by rw [Real.rpow_zero]; exact hn⟩
  have hs : ∀ x ∈ S, x ∈ IntermediateField.adjoin ℚ S := fun x hx => IntermediateField.subset_adjoin ℚ S hx
  let W : WeierstrassCurve R :=
    ⟨⟨_, hm _ (hs _ (by simp [S])) h₁⟩, ⟨_, hm _ (hs _ (by simp [S])) h₂⟩, ⟨_, hm _ (hs _ (by simp [S])) h₃⟩,
      ⟨_, hm _ (hs _ (by simp [S])) h₄⟩, ⟨_, hm _ (hs _ (by simp [S])) h₆⟩⟩
  have hW : W.map R.subtype = V.map (algebraMap (algebraicClosure ℚ ℂ) ℂ) := rfl
  have eΔ : ((W.Δ : R) : ℂ) = (V.Δ : ℂ) := by
    have := congrArg WeierstrassCurve.Δ hW
    rwa [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ] at this
  have ec : ((W.c₄ : R) : ℂ) = (V.c₄ : ℂ) := by
    have := congrArg WeierstrassCurve.c₄ hW
    rwa [WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₄] at this
  have h0 : V.Δ ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hΔ; exact absurd hΔ (by norm_num)
  refine ⟨_, R, W, hk, hR, hRk, ?_, ?_⟩
  · have hmem : ((V.Δ⁻¹ : algebraicClosure ℚ ℂ) : ℂ) ∈ R := by
      refine hm _ ?_ ?_
      · rw [IntermediateField.coe_inv, ← eΔ]; exact inv_mem (hRk _ W.Δ.2)
      · rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ hΔ
    refine IsUnit.of_mul_eq_one ⟨_, hmem⟩ (Subtype.ext ?_)
    change ((W.Δ : R) : ℂ) * ((V.Δ⁻¹ : algebraicClosure ℚ ℂ) : ℂ) = 1
    rw [eΔ, ← IntermediateField.coe_mul, mul_inv_cancel₀ h0]; rfl
  · rw [eΔ, ec]; exact_mod_cast congrArg (fun x : algebraicClosure ℚ ℂ => (x : ℂ)) hc

open Polynomial in

theorem exists_curve : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (J : ℂ), IsIntegral ℤ J →
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ) (W : WeierstrassCurve R₁), FiniteDimensional ℚ k₁ ∧
      IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧ IsUnit W.Δ ∧ ((W.c₄ : R₁) : ℂ) ^ 3 = J * ((W.Δ : R₁) : ℂ) := by
  intro l _ lam J hJ
  haveI : IsAlgClosed (algebraicClosure ℚ ℂ) := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  have hJQ : IsIntegral ℚ J := hJ.tower_top
  let j : algebraicClosure ℚ ℂ := ⟨J, mem_algebraicClosure_iff.2 hJQ.isAlgebraic⟩
  have hjZ : IsIntegral ℤ j :=
    (isIntegral_algHom_iff ((algebraicClosure ℚ ℂ).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hJ
  have hj : ‖lam j‖ ≤ 1 := GlobalTheory.PlaceRingExists.norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int lam hjZ using 1 <;> first | exact Subsingleton.elim _ _ | rfl)
  by_cases hl : l = 3
  · have hd : ((C 16 * (X * (X - C 1) + C 1)) ^ 3 - C j * (C 16 * (X * (X - C 1)) ^ 2) :
        (algebraicClosure ℚ ℂ)[X]).degree = 6 := by compute_degree!
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ (hd.trans_ne (by decide))
    have hα' : (16 * (α * (α - 1) + 1)) ^ 3 = j * (16 * (α * (α - 1)) ^ 2) := by
      simpa [sub_eq_zero] using hα
    have hn := legendre_norm (l := l) (by omega) hj (a := lam α) (by simpa [map_ofNat] using congrArg lam hα')
    let V : WeierstrassCurve (algebraicClosure ℚ ℂ) := ⟨0, -(1 + α), 0, α, 0⟩
    have eΔ : V.Δ = 16 * (α * (α - 1)) ^ 2 := by
      simp only [V, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    have ec : V.c₄ = 16 * (α * (α - 1) + 1) := by
      simp only [V, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      ring
    refine descend l lam j V (by simp [V]) ?_ (by simp [V]) hn.1 (by simp [V]) ?_ (by rw [eΔ, ec, hα'])
    · change ‖lam (-(1 + α))‖ ≤ 1
      rw [map_neg, norm_neg, map_add, map_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hn.1)
    · rw [eΔ]; simpa only [map_mul, map_pow, map_sub, map_one, map_ofNat] using hn.2
  · have hd : ((X * (X ^ 3 - C 24)) ^ 3 - C j * (X ^ 3 - C 27) : (algebraicClosure ℚ ℂ)[X]).degree = 12 := by
      compute_degree!
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ (hd.trans_ne (by decide))
    have hα' : (α * (α ^ 3 - 24)) ^ 3 = j * (α ^ 3 - 27) := by
      simpa [sub_eq_zero] using hα
    have hn := deuring_norm (l := l) hl hj (a := lam α) (by simpa [map_ofNat] using congrArg lam hα')
    let V : WeierstrassCurve (algebraicClosure ℚ ℂ) := ⟨α, 0, 1, 0, 0⟩
    have eΔ : V.Δ = α ^ 3 - 27 := by
      simp only [V, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    have ec : V.c₄ = α * (α ^ 3 - 24) := by
      simp only [V, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      ring
    refine descend l lam j V hn.1 (by simp [V]) (by simp [V]) (by simp [V]) (by simp [V]) ?_ (by rw [eΔ, ec, hα'])
    rw [eΔ]; simpa only [map_mul, map_pow, map_sub, map_ofNat] using hn.2

end GlobalTheory.PlaceRingCurve
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_model_good_reduction : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (J : ℂ), IsIntegral ℤ J →
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ) (W : WeierstrassCurve R₁), FiniteDimensional ℚ k₁ ∧
      IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧ IsUnit W.Δ ∧ ((W.c₄ : R₁) : ℂ) ^ 3 = J * ((W.Δ : R₁) : ℂ) := by
  atlas_forward_decl GlobalTheory.PlaceRingCurve.exists_curve
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatticeFibre

open GlobalTheory.HolUnifScale in

theorem exists_holUnif_rescale {A : Over (Sp ℂ)} [GrpObj A] {Lb : LB A.left} {n : ℕ} (u : HolUnif A Lb n)
    (w₀ : Fin n → ℂ) (hn : n = 1) (v : epsR ℂ ⟶ A) (hw : u.IsDiff w₀ v) (hw0 : w₀ ≠ 0) (Λ : PeriodPair) {c : ℂ}
    (hc : c ≠ 0) (hL : ∀ z : ℂ, z ∈ Λ.lattice ↔ (c⁻¹ * z) • w₀ ∈ u.Λ) :
    ∃ u' : HolUnif A Lb 1, (∀ w, w ∈ u'.Λ ↔ w 0 ∈ Λ.lattice) ∧ u'.IsDiff (fun _ ↦ c) v := by
  subst hn
  have h0 : w₀ 0 ≠ 0 := fun h ↦ hw0 (funext fun j ↦ by rw [Subsingleton.elim j 0]; exact h)
  have h : ∀ j : Fin 1, (fun _ : Fin 1 ↦ w₀ 0 / c) j ≠ 0 := fun _ ↦ div_ne_zero h0 hc
  refine ⟨rescale u _ h, fun w ↦ ?_, ?_⟩
  · refine (mem_latPull u _ h w).trans ?_
    rw [hL, scale_apply]
    have e : (fun j : Fin 1 ↦ w₀ 0 / c * w j) = (c⁻¹ * w 0) • w₀ := by
      funext j
      rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
  · have key : ∀ W, (rescale u _ h).IsDiff W v ↔ u.IsDiff (fun j ↦ w₀ 0 / c * W j) v := by
      intro W
      unfold HolUnif.IsDiff
      have hf : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
          (fun z ↦ valAt' ((rescale u _ h).ex z).left U f) = (fun z ↦ valAt' (u.ex z).left U f) ∘ scale _ h :=
        fun _ _ ↦ rfl
      simp only [hf, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
      rfl
    rw [key]
    have e : (fun _ : Fin 1 ↦ w₀ 0 / c * c) = w₀ := by
      funext j
      rw [Subsingleton.elim j 0, div_mul_cancel₀ _ hc]
    rw [e]
    exact hw

theorem exists_fibre_holUnif : ∀ (R₁ : Subring ℂ) (W : WeierstrassCurve R₁), IsUnit W.Δ → ∀ (Λ : PeriodPair) (c : ℂ), c ≠ 0 →
    ((W.c₄ : R₁) : ℂ) = 12 * c ^ 4 * Λ.g₂ → ((W.c₆ : R₁) : ℂ) = 216 * c ^ 6 * Λ.g₃ →
      ∃ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left)
        (u : HolUnif A' L' 1) (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A'),
        IsAbelianScheme A' ∧ SmoothOfRelativeDimension 1 A'.hom ∧ IsGrpPullback A' P.A (spMap R₁.subtype) φ' ∧
        (∀ w, w ∈ u.Λ ↔ w 0 ∈ Λ.lattice) ∧ IsTangent v ∧ IsTangent v' ∧
        v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left ∧ u.IsDiff (fun _ ↦ c) v' := by
  intro R₁ W hΔ Λ c hc h4 h6
  obtain ⟨P, v, Lf, ⟨hg, hv, -, hs⟩, hinv⟩ :=
    GlobalTheory.exists_polAV_latticeFamily GlobalTheory.thetaUnifAV_all GlobalTheory.polBaseChange_holds R₁ W hΔ
  obtain ⟨P', φ', h⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds R₁.subtype P
  obtain ⟨v', hv', -⟩ := GlobalTheory.existsUnique_isVecOver h.2.1.1 v
  have ht : IsTangent v := hv.1 0
  have ht' : IsTangent v' := hv'.isTangent h.2.1 ht
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, Hm, χ, -, -, -, hd, -⟩ := GlobalTheory.thetaUnifAV_all P' rig hrig
  obtain ⟨w, hw, -⟩ := hd v' ht'
  obtain ⟨hw0, hL⟩ := hs R₁.subtype P' φ' v' u w h hv' hw
  obtain ⟨e4, e6, -⟩ := hinv R₁.subtype
  have H := GlobalTheory.isHomothetic_scalePeriods Λ c⁻¹ (inv_ne_zero hc)
  have e : (Lf R₁.subtype).lattice = (GlobalTheory.scalePeriods Λ c⁻¹ (inv_ne_zero hc)).lattice := by
    refine GlobalTheory.lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_
    · refine mul_left_cancel₀ (by norm_num : (12 : ℂ) ≠ 0) ?_
      rw [← e4, H.g₂_eq, inv_pow, inv_inv, ← _root_.mul_assoc]
      exact h4
    · refine mul_left_cancel₀ (by norm_num : (216 : ℂ) ≠ 0) ?_
      rw [← e6, H.g₃_eq, inv_pow, inv_inv, ← _root_.mul_assoc]
      exact h6
  have hg' : P'.g = 1 := h.1.trans hg
  obtain ⟨u', hu', hd'⟩ := exists_holUnif_rescale u w hg' v' hw hw0 Λ hc
    (fun z ↦ by rw [← hL, e]; exact (H z).symm)
  exact ⟨P, P'.A, inferInstance, φ', P'.L, u', v, v', P'.isAb, hg' ▸ P'.smoothDim, h.2.1, hu', ht, ht', hv', hd'⟩

end GlobalTheory.LatticeFibre
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_curve_abelian_scheme_model : ∀ (R₁ : Subring ℂ) (W : WeierstrassCurve R₁), IsUnit W.Δ → ∀ (Λ : PeriodPair) (c : ℂ), c ≠ 0 →
    ((W.c₄ : R₁) : ℂ) = 12 * c ^ 4 * Λ.g₂ → ((W.c₆ : R₁) : ℂ) = 216 * c ^ 6 * Λ.g₃ →
      ∃ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left)
        (u : HolUnif A' L' 1) (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A'),
        IsAbelianScheme A' ∧ SmoothOfRelativeDimension 1 A'.hom ∧ IsGrpPullback A' P.A (spMap R₁.subtype) φ' ∧
        (∀ w, w ∈ u.Λ ↔ w 0 ∈ Λ.lattice) ∧ IsTangent v ∧ IsTangent v' ∧
        v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left ∧ u.IsDiff (fun _ ↦ c) v' := by
  atlas_forward_decl GlobalTheory.LatticeFibre.exists_fibre_holUnif
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMPlaceCurve

theorem sz_of_pow {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {y : ℂ} {n : ℕ} (hn : 0 < n)
    (h : Sz l lam 0 (y ^ n)) : Sz l lam 0 y := by
  obtain ⟨hy, hn'⟩ := h
  have ha : IsAlgebraic ℚ y := IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.1 hy)
  have hy' : y ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.2 ha
  refine ⟨hy', ?_⟩
  rw [Real.rpow_zero] at hn' ⊢
  have e : (⟨y ^ n, hy⟩ : algebraicClosure ℚ ℂ) = (⟨y, hy'⟩ : algebraicClosure ℚ ℂ) ^ n := rfl
  rw [e, map_pow, norm_pow] at hn'
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 hn'

theorem exists_curve : GlobalTheory.Published.SerreTateGoodReductionSt →
  ∀ (d : ℕ) (Λ : PeriodPair), d.Prime → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ), FiniteDimensional ℚ k₁ ∧ IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧
      ∃ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left)
        (u : HolUnif A' L' 1) (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A') (t : ℂ),
        IsAbelianScheme A' ∧ SmoothOfRelativeDimension 1 A'.hom ∧ IsGrpPullback A' P.A (spMap R₁.subtype) φ' ∧
        (∀ w, w ∈ u.Λ ↔ w 0 ∈ Λ.lattice) ∧ IsTangent v ∧ IsTangent v' ∧
        v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left ∧
        u.IsDiff (fun _ ↦ t) v' ∧ t ≠ 0 ∧ Sz l lam 0 ((t * Ω)⁻¹) := by
  intro _ d Λ hd hΛ l _ lam Ω hΩ
  have hJ := GlobalTheory.T.j_invariant_integral d Λ hd hΛ
  obtain ⟨k₁, R₁, W, hk, hpl, hsub, hΔ, hj⟩ := GlobalTheory.T.weierstrass_model_good_reduction l lam _ hJ
  have hD : latDisc Λ ≠ 0 := g₂_cube_sub_g₃_sq_ne_zero Λ
  have hΔ0 : ((W.Δ : R₁) : ℂ) ≠ 0 := by
    intro h0
    exact hΔ.ne_zero (Subtype.ext h0)
  have hrel : 1728 * ((W.Δ : R₁) : ℂ) = ((W.c₄ : R₁) : ℂ) ^ 3 - ((W.c₆ : R₁) : ℂ) ^ 2 := by
    have := congrArg (fun x : R₁ ↦ (x : ℂ)) W.c_relation
    push_cast at this
    exact this
  have hΔ' : (((W.c₄ : R₁) : ℂ) / 12) ^ 3 - 27 * (((W.c₆ : R₁) : ℂ) / 216) ^ 2 = ((W.Δ : R₁) : ℂ) := by
    linear_combination -hrel / 1728
  have e : Λ.g₂ ^ 3 * ((((W.c₄ : R₁) : ℂ) / 12) ^ 3 - 27 * (((W.c₆ : R₁) : ℂ) / 216) ^ 2) =
      (((W.c₄ : R₁) : ℂ) / 12) ^ 3 * (Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2) := by
    rw [hΔ', div_pow, hj]
    unfold latDisc at hD ⊢
    field_simp
    ring
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq hD (by rw [hΔ']; exact hΔ0) e
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by rintro rfl; exact hu (by simpa using hc.symm)
  have h4 : ((W.c₄ : R₁) : ℂ) = 12 * c ^ 4 * Λ.g₂ := by
    rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; linear_combination 12 * h2
  have h6 : ((W.c₆ : R₁) : ℂ) = 216 * c ^ 6 * Λ.g₃ := by
    rw [show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; linear_combination 216 * h3
  obtain ⟨P, A', _, φ', L', uu, v, v', h1, h2', h3', h4', h5, h6', h7, h8⟩ := GlobalTheory.T.elliptic_curve_abelian_scheme_model R₁ W hΔ Λ c hc0 h4 h6
  have hΩ0 : Ω ≠ 0 := by rintro rfl; apply hD; rw [← hΩ]; norm_num
  have key : (c * Ω) ^ 12 = ((W.Δ : R₁) : ℂ) := by
    rw [← hΔ', h4, h6, mul_pow, hΩ]
    unfold latDisc
    ring
  refine ⟨k₁, R₁, hk, hpl, hsub, P, A', inferInstance, φ', L', uu, v, v', c, h1, h2', h3', h4', h5, h6', h7, h8, hc0, ?_⟩
  obtain ⟨w, hw⟩ := hΔ
  refine sz_of_pow (n := 12) (by norm_num) ?_
  have e2 : ((c * Ω)⁻¹) ^ 12 = ((w⁻¹ : R₁ˣ) : R₁) := by
    rw [inv_pow, key, ← hw]
    have := congrArg (fun x : R₁ ↦ (x : ℂ)) w.mul_inv
    simp only [Subring.coe_mul, Subring.coe_one] at this ⊢
    exact (eq_inv_of_mul_eq_one_right this).symm
  rw [e2]
  exact hpl.2.1 _ (w⁻¹ : R₁ˣ).1.2

end GlobalTheory.CMPlaceCurve
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_curve_good_reduction_model : GlobalTheory.Published.SerreTateGoodReductionSt →
  ∀ (d : ℕ) (Λ : PeriodPair), d.Prime → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ), FiniteDimensional ℚ k₁ ∧ IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧
      ∃ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left)
        (u : HolUnif A' L' 1) (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A') (t : ℂ),
        IsAbelianScheme A' ∧ SmoothOfRelativeDimension 1 A'.hom ∧ IsGrpPullback A' P.A (spMap R₁.subtype) φ' ∧
        (∀ w, w ∈ u.Λ ↔ w 0 ∈ Λ.lattice) ∧ IsTangent v ∧ IsTangent v' ∧
        v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left ∧
        u.IsDiff (fun _ ↦ t) v' ∧ t ≠ 0 ∧ Sz l lam 0 ((t * Ω)⁻¹) := by
  atlas_forward_decl GlobalTheory.CMPlaceCurve.exists_curve
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_pullback_elliptic_model : ∀ (R : Type) [CommRing R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (A' : Over (Sp ℂ)) [GrpObj A']
    (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left) (u : HolUnif A' L' 1) (v : epsR R ⟶ P.A) (v' : epsR ℂ ⟶ A') (t : ℂ)
    (S : Set ℂ), IsAbelianScheme A' → SmoothOfRelativeDimension 1 A'.hom → IsGrpPullback A' P.A (spMap σ) φ' →
    (∀ w, w ∈ u.Λ ↔ w 0 ∈ S) → IsTangent v → IsTangent v' → v'.left ≫ φ' = spMap (Chart.dualMapR σ) ≫ v.left →
    u.IsDiff (fun _ ↦ t) v' → ∀ (g : ℕ) (j₀ : Fin g),
    ∃ (P₀ : Out.PolAV (Sp R)) (A₀ : Over (Sp ℂ)) (_ : GrpObj A₀) (φ₀ : A₀.left ⟶ P₀.A.left) (L₀ : LB A₀.left)
      (u₀ : HolUnif A₀ L₀ g) (v₀ : epsR R ⟶ P₀.A) (v₀' : epsR ℂ ⟶ A₀),
      IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom ∧ IsGrpPullback A₀ P₀.A (spMap σ) φ₀ ∧
      (∀ w, w ∈ u₀.Λ ↔ ∀ j, w j ∈ S) ∧ IsTangent v₀ ∧ IsTangent v₀' ∧
      v₀'.left ≫ φ₀ = spMap (Chart.dualMapR σ) ≫ v₀.left ∧ u₀.IsDiff (Pi.single j₀ t) v₀' := by
  first | exact @GlobalTheory.PowFibre.exists_pow | exact GlobalTheory.PowFibre.exists_pow | (intros; apply GlobalTheory.PowFibre.exists_pow <;> assumption)
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMPowerIsogeny

theorem exists_mem_condQ {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣) {l : ℕ} (hl : l.Prime)
    (Q : Finset (HeightOneSpectrum (OF E))) (hQ : ∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) :
    condQ 𝔣 Q ≠ ⊥ ∧ ∃ m : ℕ, ¬ l ∣ m ∧ ((l ^ a0 𝔣 l * m : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  have hc : condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  refine ⟨hc, ?_⟩
  have hN : Ideal.absNorm (condQ 𝔣 Q) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  obtain ⟨k, m, hlm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.one_lt.ne'
  refine ⟨m, hlm, ?_⟩
  set x : OF E := ((l ^ a0 𝔣 l * m : ℕ) : OF E) with hx
  let J : Ideal (OF E) := Submodule.comap (LinearMap.mulRight (OF E) x) (condQ 𝔣 Q)
  have hJ : ∀ r, r ∈ J ↔ r * x ∈ condQ 𝔣 Q := fun r => Iff.rfl
  by_contra hne
  have hJt : J ≠ ⊤ := fun h => hne (by simpa using (hJ 1).1 (h ▸ Submodule.mem_top))
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJt
  have hlk : ((l : OF E)) ^ k ∈ J := by
    rw [hJ, hx]
    have h1 := Ideal.absNorm_mem (condQ 𝔣 Q)
    rw [hkm] at h1
    have h2 := Ideal.mul_mem_left _ ((l : OF E) ^ a0 𝔣 l) h1
    convert h2 using 1
    push_cast; ring
  have hlP : (l : OF E) ∈ P := hP.isPrime.mem_of_pow_mem k (hJP hlk)
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hlP))
  let v : HeightOneSpectrum (OF E) := ⟨P, hP.isPrime, hP0⟩
  obtain ⟨J', hJ', hnd⟩ := (FiniteMultiplicity.of_prime_left v.prime h𝔣.1).exists_eq_pow_mul_and_not_dvd
  have hle : expIn 𝔣 v ≤ a0 𝔣 l := by
    refine le_csSup ⟨2, ?_⟩ ⟨v, hlP, rfl⟩
    rintro _ ⟨w, -, rfl⟩
    by_cases hw : w.asIdeal ∣ 𝔣
    · exact (h𝔣.2.2 w hw).2.1
    · rw [expIn, multiplicity_eq_zero.2 hw]; omega
  have hnd' : ¬ (J' * ∏ q ∈ Q, q.asIdeal) ≤ P := by
    intro h
    rcases hP.isPrime.mul_le.1 h with h | h
    · exact hnd (Ideal.dvd_iff_le.2 h)
    · obtain ⟨q, hq, hqP⟩ := (Ideal.IsPrime.prod_le hP.isPrime).1 h
      exact hQ q hq (by rw [q.isMaximal.eq_of_le hP.ne_top hqP]; exact hlP)
  refine hnd' fun r hr => hJP ?_
  rw [hJ, hx, condQ]
  have h1 : (l : OF E) ^ a0 𝔣 l ∈ v.asIdeal ^ multiplicity v.asIdeal 𝔣 :=
    Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hlP _)
  have h2 := Ideal.mul_mem_right (m : OF E) _ (Ideal.mul_mem_mul h1 hr)
  rw [← _root_.mul_assoc, ← hJ'] at h2
  convert h2 using 1
  push_cast; ring

theorem sz_inv_pow_mul (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (a m : ℕ) (hm : ¬ l ∣ m) :
    Sz l lam a (((l ^ a * m : ℕ) : ℂ)⁻¹) := by
  refine ⟨inv_mem (natCast_mem _ _), ?_⟩
  have e : (⟨((l ^ a * m : ℕ) : ℂ)⁻¹, inv_mem (natCast_mem _ _)⟩ : algebraicClosure ℚ ℂ) =
      ((l ^ a * m : ℕ) : algebraicClosure ℚ ℂ)⁻¹ := Subtype.ext (by simp)
  have hn : ∀ n : ℕ, ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := fun n => by
    rw [← norm_algebraMap' ℂ_[l] (n : ℚ_[l]), map_natCast]
  have h1 : ‖(m : ℚ_[l])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
  rw [e, map_inv₀, map_natCast, norm_inv, hn, Nat.cast_mul, norm_mul, h1, Nat.cast_pow, norm_pow, Padic.norm_p]
  simp

theorem exists_separating (E : Type) [Field E] [NumberField E] :
    ∃ θ : 𝓞 E, ∀ σ τ : E →+* ℂ, σ θ = τ θ → σ = τ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨m, hm, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α)).exists_integral_multiple
  refine ⟨⟨m • α, hint⟩, fun σ τ h => ?_⟩
  have h1 : σ α = τ α := by
    have h2 : σ (m • α) = τ (m • α) := h
    rw [map_zsmul, map_zsmul] at h2
    exact smul_right_injective ℂ hm h2
  have h3 : σ.toRatAlgHom = τ.toRatAlgHom := by
    have := (Field.primitive_element_iff_algHom_eq_of_eval' ℚ ℂ (fun x => IsAlgClosed.splits _) α).1 hα
    exact this h1
  exact RingHom.ext fun x => DFunLike.congr_fun h3 x

theorem exists_kill (A B : CategoryTheory.Over (Sp ℂ)) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (ψ : A ⟶ B) [IsMonHom ψ] [IsFinite ψ.left] :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : CategoryTheory.Over (Sp ℂ)) (x : T ⟶ A), x ≫ ψ = 1 → x ^ n = 1 := by
  have := hB.proper
  have := hA.proper
  have := hA.comm
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := GlobalTheory.IsogenyModel.exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main ℂ Z hZ inferInstance
  refine ⟨N, hN, fun T x hx => ?_⟩
  have h1 : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
  rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

theorem exists_isogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 →
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ))
    (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (A' : Over (Sp ℂ)) [GrpObj A'] (L' : LB A'.left)
    (u : HolUnif A' L' (Module.finrank ℚ (FR E))), IsAbelianScheme A' →
    SmoothOfRelativeDimension (Module.finrank ℚ (FR E)) A'.hom → (∀ w, w ∈ u.Λ ↔ ∀ j, w j ∈ Λ.lattice) →
    ∀ j₀ : Fin (Module.finrank ℚ (FR E)),
    ∃ (α : A' ⟶ X.A) (M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ)) (n N : ℕ),
      IsMonHom α ∧ IsFinite α.left ∧ Flat α.left ∧ Surjective α.left ∧ 1 ≤ N ∧
      (∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1) ∧ (∀ w, U.u.ex (M w) = u.ex w ≫ α) ∧
      M (Pi.single j₀ 1) = (fun _ ↦ (n : ℂ)) ∧ 0 < n ∧ Sz l lam (a0 𝔣 l) ((n : ℂ)⁻¹) := by
  intro E _ _ _ _ I _ d φ hφ 𝔣 Λ h𝔣 hΛ l _ Q _ hQ y hy lam 𝔠 X U A' _ L' u hA' hg hu j₀
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨-, -, -, -, -, -, hCM, ω, -, hω⟩ := hφ
  obtain ⟨hc, m, hm, hmc⟩ := exists_mem_condQ h𝔣 hl Q hQ
  obtain ⟨m', hm', -, hm'L⟩ := GlobalTheory.CMVal.LatLoc.lattice_near_orderC E _ hc l hl y hy
  have hmm : ¬ l ∣ m * m' := fun h =>
    (hl.dvd_mul.1 h).elim hm ((Nat.Prime.coprime_iff_not_dvd hl).1 hm'.symm)
  set n : ℕ := l ^ a0 𝔣 l * (m * m') with hn
  have hn0 : 0 < n := Nat.mul_pos (pow_pos hl.pos _) (Nat.pos_of_ne_zero fun h => hmm (h ▸ dvd_zero l))
  have hnL : ∀ b : 𝓞 E, (n : E) * (b : E) ∈ lattice (condQ 𝔣 Q) y := fun b => by
    have h1 := hm'L (((l ^ a0 𝔣 l * m : ℕ) : E) * (b : E)) (mem_orderC.2 ⟨0, _, Ideal.mul_mem_right b _
      (Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) hmc), by rw [map_zero, zero_add, map_mul, map_natCast, map_natCast]⟩)
    convert h1 using 1
    rw [hn]; push_cast; ring
  obtain ⟨θ, hθ⟩ := exists_separating E
  have hinj : Function.Injective fun k => φ (U.e k) (θ : E) := fun k k' h => by
    have h1 := hθ _ _ h
    exact U.e.injective ((hCM (φ (U.e k))).unique (Or.inl rfl) (Or.inl h1))
  let z : Fin (Module.finrank ℚ (FR E)) := ⟨0, j₀.pos⟩
  let s := Equiv.swap j₀ z
  let V : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ :=
    (n : ℂ) • (Matrix.vandermonde fun k => φ (U.e k) (θ : E)).submatrix id s
  have hV : V.det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_permute']
    refine mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn0.ne')) (mul_ne_zero ?_ ?_)
    · exact_mod_cast Units.ne_zero _
    · exact Matrix.det_vandermonde_ne_zero_iff.2 hinj
  have hVe : ∀ x k, Matrix.toLin' V x k = ∑ j, (n : ℂ) * φ (U.e k) (θ : E) ^ (s j : ℕ) * x j := fun x k => rfl
  have hsurj : Function.Surjective (Matrix.toLin' V) := fun w =>
    ⟨V⁻¹.mulVec w, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hV),
      Matrix.one_mulVec]⟩
  have hlift : ∀ x ∈ Λ.lattice, ∃ b : 𝓞 E, ∀ i, φ i (b : E) = x := fun x hx => by
    obtain ⟨hint, a, b, hab⟩ := (hΛ x).1 hx
    have h1 : ∀ i, φ i ((a : E) + (b : E) * ω) = x := fun i => by
      rw [map_add, map_mul, map_ratCast, map_ratCast, hω, hab]
    refine ⟨⟨(a : E) + (b : E) * ω, ?_⟩, h1⟩
    rw [← h1 (U.e j₀)] at hint
    exact (isIntegral_algHom_iff (φ (U.e j₀)).toIntAlgHom (φ (U.e j₀)).injective).1 hint
  have hM : ∀ x ∈ u.Λ, Matrix.toLin' V x ∈ U.u.Λ := fun x hx => by
    choose b hb using fun j => hlift (x j) ((hu x).1 hx j)
    refine (U.lat _).2 ⟨_, hnL (∑ j, θ ^ (s j : ℕ) * b j), funext fun k => ?_⟩
    have e : ((∑ j, θ ^ (s j : ℕ) * b j : 𝓞 E) : E) = ∑ j, (θ : E) ^ (s j : ℕ) * (b j : E) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_sum, map_mul, map_pow]
    rw [hVe, e, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, Pi.zero_apply, zero_mul, add_zero, map_mul, map_natCast, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hb, _root_.mul_assoc]
  obtain ⟨α, hα, hαe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A' X.A _ hA' X.ab hg X.dim L' _ u U.u
    (Matrix.toLin' V) hM
  haveI : Surjective α.left := GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points A' X.A α hA' X.ab fun p => by
    obtain ⟨w, rfl⟩ := U.u.ex_onto p
    obtain ⟨w', rfl⟩ := hsurj w
    exact ⟨u.ex w', (hαe w').symm⟩
  obtain ⟨hfin, hflat⟩ := GlobalTheory.SurjHomFlat.finite_flat A' X.A _ hA' X.ab hg X.dim α
  obtain ⟨N, hN, hkill⟩ := exists_kill A' X.A hA' X.ab α
  refine ⟨α, Matrix.toLin' V, n, N, hα, hfin, hflat, inferInstance, hN, hkill, hαe, funext fun k => ?_, hn0,
    sz_inv_pow_mul l lam _ _ hmm⟩
  rw [hVe, Finset.sum_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero]) (by simp), Pi.single_eq_same,
    show s j₀ = z from Equiv.swap_apply_left _ _]
  simp [z]

end GlobalTheory.CMPowerIsogeny
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_lattice_l_adic_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 →
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ))
    (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (A' : Over (Sp ℂ)) [GrpObj A'] (L' : LB A'.left)
    (u : HolUnif A' L' (Module.finrank ℚ (FR E))), IsAbelianScheme A' →
    SmoothOfRelativeDimension (Module.finrank ℚ (FR E)) A'.hom → (∀ w, w ∈ u.Λ ↔ ∀ j, w j ∈ Λ.lattice) →
    ∀ j₀ : Fin (Module.finrank ℚ (FR E)),
    ∃ (α : A' ⟶ X.A) (M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ)) (n N : ℕ),
      IsMonHom α ∧ IsFinite α.left ∧ Flat α.left ∧ Surjective α.left ∧ 1 ≤ N ∧
      (∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1) ∧ (∀ w, U.u.ex (M w) = u.ex w ≫ α) ∧
      M (Pi.single j₀ 1) = (fun _ ↦ (n : ℂ)) ∧ 0 < n ∧ Sz l lam (a0 𝔣 l) ((n : ℂ)⁻¹) := by
  atlas_forward_decl GlobalTheory.CMPowerIsogeny.exists_isogeny
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotModel

theorem mem_or_inv_mem {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {k : IntermediateField ℚ ℂ}
    (hk : FiniteDimensional ℚ k) {R : Subring ℂ} (hR : IsPlaceOver l lam k R) {x : ℂ} (hx : x ∈ k) :
    x ∈ R ∨ x⁻¹ ∈ R := by
  have halg : x ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff']
    exact (IntermediateField.isIntegral_iff (x := (⟨x, hx⟩ : k))).1 (Algebra.IsIntegral.isIntegral _)
  rcases le_total ‖lam ⟨x, halg⟩‖ 1 with h | h
  · exact Or.inl (hR.2.2 x hx ⟨halg, by simpa using h⟩)
  · refine Or.inr (hR.2.2 _ (inv_mem hx) ⟨inv_mem halg, ?_⟩)
    have : (⟨x⁻¹, inv_mem halg⟩ : algebraicClosure ℚ ℂ) = (⟨x, halg⟩ : algebraicClosure ℚ ℂ)⁻¹ := rfl
    rw [this, map_inv₀, norm_inv, Real.rpow_zero]
    exact inv_le_one_of_one_le₀ h

theorem exists_place (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k : IntermediateField ℚ ℂ)
    (hk : FiniteDimensional ℚ k) : ∃ R : Subring ℂ, IsPlaceOver l lam k R ∧ ∀ x ∈ R, x ∈ k := by
  obtain ⟨S, hS, hS1, hS2⟩ := GlobalTheory.PlaceRingExists.exists_isPlaceOver l lam k hk
  let R : Subring ℂ := S ⊓ k.toSubfield.toSubring
  have hRS : R ≤ S := inf_le_left
  let j : R →+* S := Subring.inclusion hRS
  have hj : Function.Injective j := Subring.inclusion_injective hRS
  have hdvd : ∀ a b : R, j a ∣ j b → a ∣ b := by
    rintro a b ⟨c, hc⟩
    by_cases ha : a = 0
    · subst ha
      have : b = 0 := hj (by simpa using hc)
      simp [this]
    · have ha' : (a : ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
      have hc' : (b : ℂ) = a * c := congrArg Subtype.val hc
      have hck : (c : ℂ) ∈ k := by
        have : (c : ℂ) = (a : ℂ)⁻¹ * b := by rw [hc']; field_simp
        rw [this]
        exact mul_mem (inv_mem a.2.2) b.2.2
      exact ⟨⟨c, c.2, hck⟩, Subtype.ext hc'⟩
  have hunit : ∀ a : R, IsUnit (j a) → IsUnit a := fun a h =>
    isUnit_of_dvd_one (hdvd a 1 (by simpa using h.dvd))
  haveI : IsLocalRing R := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (j a) with h | h
    · exact Or.inl (hunit a h)
    · exact Or.inr (hunit _ (by simpa using h))
  haveI : IsPrincipalIdealRing R := ⟨fun I => by
    obtain ⟨a, ha, hmin⟩ := (InvImage.wf (fun a : R => IsDiscreteValuationRing.addVal S (j a))
      (wellFounded_lt (α := ℕ∞))).has_min (I : Set R) ⟨0, I.zero_mem⟩
    refine ⟨a, le_antisymm (fun b hb => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ha)⟩
    exact Ideal.mem_span_singleton.2 (hdvd a b (IsDiscreteValuationRing.addVal_le_iff_dvd.1
      (not_lt.1 (hmin b hb))))⟩
  refine ⟨R, ⟨⟨?_⟩, fun x hx => hS1 x hx.1, fun x hx hs => ⟨hS2 x hx hs, hx⟩⟩, fun x hx => hx.2⟩
  intro hbot
  have hl : (l : R) ≠ 0 := by
    intro h
    have : (l : ℂ) = 0 := by simpa using congrArg Subtype.val h
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hu : IsUnit (l : R) := by
    by_contra hn
    have : (l : R) ∈ IsLocalRing.maximalIdeal R := hn
    rw [hbot] at this
    exact hl this
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  obtain ⟨hb1, hb2⟩ := hS1 b b.2.1
  have hb' : (l : algebraicClosure ℚ ℂ) * ⟨b, hb1⟩ = 1 := Subtype.ext (by simpa using congrArg Subtype.val hb)
  have h1 := congrArg (fun z => ‖lam z‖) hb'
  simp only [map_mul, map_natCast, norm_mul, map_one, norm_one] at h1
  have h2 := GlobalTheory.PlaceRingExists.norm_prime_lt_one l
  rw [Real.rpow_zero] at hb2
  nlinarith [norm_nonneg (lam ⟨b, hb1⟩), norm_nonneg ((l : ℂ_[l]))]

theorem exists_field_of_finite (k₁ : IntermediateField ℚ ℂ) (hk : FiniteDimensional ℚ k₁) (R₁ : Subring ℂ)
    (hR : ∀ x ∈ R₁, x ∈ k₁) (S : Type) [CommRing S] (a : R₁ →+* S) (ha : a.Finite) :
    ∃ k : IntermediateField ℚ ℂ, FiniteDimensional ℚ k ∧ k₁ ≤ k ∧
      ∀ φ : S →+* ℂ, φ.comp a = R₁.subtype → ∀ s, φ s ∈ k := by
  classical
  letI := a.toAlgebra
  haveI : Module.Finite R₁ S := ha
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule R₁ S).FG)
  have hint : ∀ s : S, IsIntegral R₁ s := fun s => Algebra.IsIntegral.isIntegral s
  choose p hp1 hp2 using hint
  let Z : Finset ℂ := t.biUnion fun s => ((p s).map R₁.subtype).roots.toFinset
  have hZ : ∀ z ∈ (Z : Set ℂ), IsIntegral ℚ z := by
    intro z hz
    obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.1 hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((hp1 s).map _).ne_zero] at hs
    have h1 : IsIntegral k₁ z := by
      refine ⟨(p s).map (R₁.subtype.codRestrict k₁ fun x => hR x x.2), (hp1 s).map _, ?_⟩
      rw [Polynomial.eval₂_map]
      rw [Polynomial.IsRoot, Polynomial.eval_map] at hs
      exact hs
    exact isIntegral_trans z h1
  haveI := IntermediateField.finiteDimensional_adjoin hZ
  refine ⟨k₁ ⊔ IntermediateField.adjoin ℚ (Z : Set ℂ), IntermediateField.finiteDimensional_sup _ _,
    le_sup_left, fun φ hφ s => ?_⟩
  have hs : s ∈ Submodule.span R₁ (t : Set S) := by rw [ht]; trivial
  induction hs using Submodule.span_induction with
  | mem x hx =>
    refine (le_sup_right : _ ≤ k₁ ⊔ _) (IntermediateField.subset_adjoin _ _ ?_)
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((hp1 x).map _).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← hφ, ← Polynomial.hom_eval₂]
    have := hp2 x
    rw [show algebraMap R₁ S = a from rfl] at this
    rw [this, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    have : φ (algebraMap R₁ S r) = r := congrArg (fun f : R₁ →+* ℂ => f r) hφ
    rw [this]
    exact (le_sup_left : _ ≤ k₁ ⊔ _) (hR r r.2)

theorem exists_field_of_isFinite (k₁ : IntermediateField ℚ ℂ) (hk : FiniteDimensional ℚ k₁) (R₁ : Subring ℂ)
    (hR : ∀ x ∈ R₁, x ∈ k₁) (X : Scheme.{0}) (f : X ⟶ Sp R₁) [IsFinite f] :
    ∃ k : IntermediateField ℚ ℂ, FiniteDimensional ℚ k ∧ k₁ ≤ k ∧
      ∀ x : Sp ℂ ⟶ X, x ≫ f = spMap R₁.subtype → ∃ y : Sp k ⟶ X, spMap (algebraMap k ℂ) ≫ y = x := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let a : CommRingCat.of R₁ ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f)
  have ha : Spec.map a = X.isoSpec.inv ≫ f := Spec.map_preimage _
  have hfin : a.hom.Finite := by
    have : IsFinite (Spec.map a) := by rw [ha]; infer_instance
    exact (IsFinite.SpecMap_iff a).1 this
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_field_of_finite k₁ hk R₁ hR Γ(X, ⊤) a.hom hfin
  refine ⟨k, hk1, hk2, fun x hx => ?_⟩
  let φ : Γ(X, ⊤) ⟶ CommRingCat.of ℂ := Spec.preimage (x ≫ X.isoSpec.hom)
  have hφ : Spec.map φ = x ≫ X.isoSpec.hom := Spec.map_preimage _
  have hcomp : φ.hom.comp a.hom = R₁.subtype := by
    have : a ≫ φ = CommRingCat.ofHom R₁.subtype := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, ha, Category.assoc, Iso.hom_inv_id_assoc, hx]
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨Spec.map (CommRingCat.ofHom (φ.hom.codRestrict k (hk3 φ.hom hcomp))) ≫ X.isoSpec.inv, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, Iso.comp_inv_eq, ← hφ]
  rfl

theorem epi_field (k K : Type) [Field k] [Field K] (t : Sp k ⟶ Sp K) : Epi t :=
  Flat.epi_of_flat_of_surjective t

theorem kill (A Y Y' : Over (Sp ℂ)) [GrpObj A] [GrpObj Y] [GrpObj Y'] (hA : IsAbelianScheme A)
    [IsSeparated Y'.hom] (u : A ⟶ Y) (f : A ⟶ Y') [IsFinite u.left] [Flat u.left] (N : ℕ) (hN : 1 ≤ N)
    (hu : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ^ N = 1)
    (h : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ u = 1 → x ≫ f = 1) :
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ≫ f = 1 := by
  let Z : Over (Sp ℂ) := pullback u η
  let i : Z ⟶ A := pullback.fst u η
  have hP : IsPullback i (toUnit Z) u η := by
    have := IsPullback.of_hasPullback u (η : 𝟙_ _ ⟶ Y)
    rwa [toUnit_unique (pullback.snd u η) (toUnit Z)] at this
  have hP' : IsPullback i.left Z.hom u.left (η : 𝟙_ _ ⟶ Y).left := by
    have := hP.map (Over.forget _)
    simpa using this
  haveI : IsFinite Z.hom := MorphismProperty.of_isPullback (P := @IsFinite) hP' inferInstance
  haveI : Flat Z.hom := MorphismProperty.of_isPullback (P := @Flat) hP' inferInstance
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have h1 : IsUnit ((N : ℕ) : ℂ) := (Nat.cast_ne_zero.2 (by omega) : ((N : ℕ) : ℂ) ≠ 0).isUnit
    simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨-, -, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective _ A N hA hunit
  have hi : i ≫ (𝟙 A ^ N) = toUnit Z ≫ η := by
    rw [comp_pow, Category.comp_id, hu Z i (by rw [hP.w, Hom.one_def]), Hom.one_def]
  have hi' : i.left ≫ (𝟙 A ^ N).left = Z.hom ≫ (η : 𝟙_ _ ⟶ A).left := by
    simpa using congrArg (fun z => z.left) hi
  let j := pullback.lift i.left Z.hom hi'
  haveI : Mono (η : 𝟙_ _ ⟶ Y) := ⟨fun a b _ => toUnit_unique a b⟩
  haveI : Mono i := inferInstanceAs (Mono (pullback.fst u η))
  haveI : Mono i.left := inferInstanceAs (Mono ((Over.forget _).map i))
  haveI : Mono (j ≫ pullback.fst _ _) := by rw [pullback.lift_fst]; infer_instance
  haveI : Mono j := mono_of_mono j (pullback.fst _ _)
  haveI : FormallyUnramified j := inferInstance
  haveI : FormallyUnramified Z.hom := by
    rw [← pullback.lift_snd i.left Z.hom hi']
    haveI : Etale (pullback.snd (𝟙 A ^ N).left (η : 𝟙_ _ ⟶ A).left) := inferInstance
    exact MorphismProperty.comp_mem @FormallyUnramified j _ inferInstance inferInstance
  haveI : Etale Z.hom := Etale.of_formallyUnramified_of_flat _
  haveI : AlgebraicGeometry.IsReduced Z.left := isReduced_of_smooth_of_isReduced Z.hom
  exact KernelKill.comp_eq_one_of_kill_closedPoints A Y Y' Z u f i hP h

theorem exists_iso (A Y Y' : Over (Sp ℂ)) [GrpObj A] [GrpObj Y] [GrpObj Y'] (hA : IsAbelianScheme A)
    [IsSeparated Y.hom] [IsSeparated Y'.hom] (u : A ⟶ Y) (f : A ⟶ Y') [IsMonHom u] [IsMonHom f]
    [IsFinite u.left] [Flat u.left] [Surjective u.left] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    (N : ℕ) (hN : 1 ≤ N)
    (hu : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ^ N = 1)
    (hf : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ f = 1 → x ^ N = 1)
    (h : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ u = 1 ↔ x ≫ f = 1) :
    ∃ e : Y ≅ Y', IsMonHom e.hom ∧ u ≫ e.hom = f := by
  obtain ⟨⟨a, ha, hua⟩, eu⟩ := exists_monHom_factor_of_flat_surjective _ A Y Y' u f inferInstance inferInstance
    inferInstance inferInstance inferInstance (kill A Y Y' hA u f N hN hu fun x => (h x).1)
  obtain ⟨⟨b, hb, hfb⟩, ef⟩ := exists_monHom_factor_of_flat_surjective _ A Y' Y f u inferInstance inferInstance
    inferInstance inferInstance inferInstance (kill A Y' Y hA f u N hN hf fun x => (h x).2)
  refine ⟨⟨a, b, ?_, ?_⟩, ha, hua⟩
  · rw [← cancel_epi u, reassoc_of% hua, hfb, Category.comp_id]
  · rw [← cancel_epi f, reassoc_of% hfb, hua, Category.comp_id]

theorem exists_field_model (K : Type) [Field K] (t : Sp ℂ ⟶ Sp K) (P : Out.PolAV (Sp K))
    (A' : Over (Sp ℂ)) [GrpObj A'] (φ : A'.left ⟶ P.A.left) (hφ : IsGrpPullback A' P.A t φ)
    (B : Over (Sp ℂ)) [GrpObj B] (α : A' ⟶ B) (N : ℕ) (hB : IsAbelianScheme B) [IsMonHom α] [IsFinite α.left]
    [Flat α.left] [Surjective α.left] (hN : 1 ≤ N)
    (hα : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1)
    (hrat : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A', x ^ N = 1 →
      ∃ c : 𝟙_ (Over (Sp K)) ⟶ P.A, x.left ≫ φ = t ≫ c.left) :
    ∃ (B₀ : Over (Sp K)) (_ : GrpObj B₀) (ψ : P.A ⟶ B₀) (q : B.left ⟶ B₀.left), IsAbelianScheme B₀ ∧
      IsMonHom ψ ∧ IsFinite ψ.left ∧ Flat ψ.left ∧ Surjective ψ.left ∧
      (∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ N = 1) ∧
      IsGrpPullback B B₀ t q ∧ α.left ≫ q = φ ≫ ψ.left := by
  haveI := P.isAb.comm
  haveI := P.isAb.proper
  haveI := hB.proper
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback P.isAb hφ
  obtain ⟨e, he⟩ : ∃ e : (𝟙_ (Over (Sp ℂ)) ⟶ A') ≃* (Over.mk t ⟶ P.A), ∀ x, (e x).left = x.left ≫ φ :=
    exists_mulEquiv_of_isGrpPullback hφ (𝟙 _) t (Category.id_comp _).symm
  have hjinj : ∀ (k : Type) [Field k] (s : Sp k ⟶ Sp K) (c c' : 𝟙_ (Over (Sp K)) ⟶ P.A),
      toUnit (Over.mk s) ≫ c = toUnit (Over.mk s) ≫ c' → c = c' := by
    intro k _ s c c' h
    haveI := epi_field k K s
    ext1
    have := congrArg (fun z => z.left) h
    rw [← cancel_epi s]
    simpa using this
  let j : (𝟙_ (Over (Sp K)) ⟶ P.A) →* (Over.mk t ⟶ P.A) :=
    { toFun := fun c => toUnit _ ≫ c, map_one' := comp_one _, map_mul' := fun a b => comp_mul _ a b }
  let m : (𝟙_ (Over (Sp K)) ⟶ P.A) →* (𝟙_ (Over (Sp ℂ)) ⟶ B) :=
    (IsMonHom.monoidHom α _).comp (e.symm.toMonoidHom.comp j)
  let C := m.ker
  have hC : ∀ c, c ∈ C ↔ e.symm (toUnit _ ≫ c) ≫ α = 1 := fun c => Iff.rfl
  have hCN : ∀ c ∈ C, (toUnit (Over.mk t) ≫ c) ^ N = 1 := by
    intro c hc
    apply e.symm.injective
    rw [map_pow, map_one]
    exact hα _ _ ((hC c).1 hc)
  have hCN' : ∀ c ∈ C, c ^ N = 1 := by
    intro c hc
    apply hjinj ℂ t
    rw [comp_pow, hCN c hc, comp_one]
  haveI : Finite C := by
    have hcard := (firstFiveLaws.1.mulN (Sp K) P N hN).2.2.2.2 ℂ t (Nat.cast_ne_zero.2 (by omega))
    haveI : Finite {x : Over.mk t ⟶ P.A // x ^ N = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
    refine Finite.of_injective
      (fun c : C => (⟨toUnit _ ≫ c.1, hCN c.1 c.2⟩ : {x : Over.mk t ⟶ P.A // x ^ N = 1})) ?_
    intro c c' h
    exact Subtype.ext (hjinj ℂ t _ _ (congrArg Subtype.val h))
  letI : CommGroup C := { (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Hom.commMonoid.mul_comm a.1 b.1) }
  obtain ⟨B₀, _, ψ, hB₀, hψ, hfin, het, hsurj, -, hker⟩ :=
    exists_quotient_by_finite_group_of_sections K P C C.subtype (fun k _ _ s c h =>
      Subtype.ext (hjinj k s _ _ (h.trans (comp_one _).symm)))
  haveI := hB₀.proper
  haveI : IsMonHom (𝟙 P.A ^ N) := by
    have hne : ((N : ℕ) : K) ≠ 0 := by
      intro h0
      have := congrArg (Spec.preimage t).hom h0
      rw [map_natCast, map_zero, Nat.cast_eq_zero] at this
      omega
    refine (abelianScheme_id_pow_finite_etale_surjective _ P.A N P.isAb ?_).1
    simpa using hne.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨g', hg', hψg, -⟩ := HkFactor.exists_unique_factor (Sp K) P.A B₀ P.A ψ (𝟙 P.A ^ N) P.isAb hB₀
    inferInstance hψ hfin het hsurj inferInstance (fun k _ _ s x hx => by
      obtain ⟨c, rfl⟩ := (hker k s x).1 hx
      rw [Category.assoc, comp_pow, Category.comp_id]
      exact (congrArg (toUnit _ ≫ ·) (hCN' c.1 c.2)).trans (comp_one _))
  have hψN : ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ N = 1 := by
    intro T x hx
    have : x ≫ ψ ≫ g' = 1 := by rw [reassoc_of% hx, one_comp]
    rwa [hψg, comp_pow, Category.comp_id] at this
  obtain ⟨B', _, q', hq'⟩ := FlagTan.exists_isGrpPullback B₀ t
  obtain ⟨π, hπ, hπw⟩ := HomDescent.exists_isMonHom_pull hφ hq' ψ
  have hsq : IsPullback φ π.left ψ.left q' := by
    refine IsPullback.of_bot ?_ hπw.symm hq'.1
    simpa using hφ.1
  haveI : IsFinite π.left := MorphismProperty.of_isPullback (P := @IsFinite) hsq hfin
  haveI : Flat π.left := MorphismProperty.of_isPullback (P := @Flat) hsq inferInstance
  haveI : Surjective π.left := MorphismProperty.of_isPullback (P := @Surjective) hsq hsurj
  haveI := (PolPull.isAbelianScheme_of_isGrpPullback hB₀ hq').proper
  have hπN : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ π = 1 → x ^ N = 1 := by
    intro T x hx
    obtain ⟨eA, heA⟩ : ∃ e : (T ⟶ A') ≃* (Over.mk (T.hom ≫ t) ⟶ P.A), ∀ x, (e x).left = x.left ≫ φ :=
      exists_mulEquiv_of_isGrpPullback hφ T.hom _ rfl
    obtain ⟨eB, heB⟩ : ∃ e : (T ⟶ B') ≃* (Over.mk (T.hom ≫ t) ⟶ B₀), ∀ x, (e x).left = x.left ≫ q' :=
      exists_mulEquiv_of_isGrpPullback hq' T.hom _ rfl
    apply eA.injective
    rw [map_pow, map_one]
    apply hψN
    have : eA x ≫ ψ = eB (x ≫ π) := by
      ext1
      rw [heB, Over.comp_left, Over.comp_left, heA, Category.assoc, Category.assoc, hπw]
    rw [this, hx, map_one]
  obtain ⟨eB, heB⟩ : ∃ e : (𝟙_ (Over (Sp ℂ)) ⟶ B') ≃* (Over.mk t ⟶ B₀), ∀ x, (e x).left = x.left ≫ q' :=
    exists_mulEquiv_of_isGrpPullback hq' (𝟙 _) t (Category.id_comp _).symm
  obtain ⟨β, hβ, hαβ⟩ := exists_iso A' B B' hA' α π N hN hα hπN (fun x => by
    have h1 : e x ≫ ψ = eB (x ≫ π) := by
      ext1
      rw [heB, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, hπw]
    have h2 : x ≫ π = 1 ↔ e x ≫ ψ = 1 := by rw [h1, map_eq_one_iff _ eB.injective]
    rw [h2, hker ℂ t]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := hrat x (hα _ x hx)
      have h3 : e x = toUnit _ ≫ c := by
        ext1
        rw [he, hc]
        simp
      refine ⟨⟨c, (hC c).2 ?_⟩, h3⟩
      rw [← h3, e.symm_apply_apply, hx]
    · rintro ⟨c, hc⟩
      have := (hC c.1).1 c.2
      change e x = toUnit _ ≫ c.1 at hc
      rwa [← hc, e.symm_apply_apply] at this)
  refine ⟨B₀, inferInstance, ψ, β.hom.left ≫ q', hB₀, hψ, hfin, inferInstance, hsurj, hψN,
    ((isGrpPullback_of_iso β).comp hq').congr (Category.id_comp _) rfl, ?_⟩
  rw [← Category.assoc, ← Over.comp_left, hαβ, hπw]

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem dualMapR_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : (Chart.dualMapR g).comp (Chart.dualMapR f) = Chart.dualMapR (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem dualMapR_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_polPull {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (g : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f g := by
  obtain ⟨P', g, hg, -, hmul, -⟩ := firstFiveLaws.1.polBaseChange S S' f P
  refine ⟨P', g, hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have h1 : x₀ = Out.toBase hg.w x := by ext1; exact hx
  have h2 : y₀ = Out.toBase hg.w y := by ext1; exact hy
  rw [h1, h2, ← hmul]
  rfl

theorem exists_quotModel : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ),
    FiniteDimensional ℚ k₁ → IsPlaceOver l lam k₁ R₁ → (∀ x ∈ R₁, x ∈ k₁) →
    ∀ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) [GrpObj A'] (φ' : A'.left ⟶ P.A.left),
    IsGrpPullback A' P.A (spMap R₁.subtype) φ' →
    ∀ (B : Over (Sp ℂ)) [GrpObj B] (α : A' ⟶ B) (N : ℕ), IsAbelianScheme B → IsMonHom α → IsFinite α.left →
    Flat α.left → Surjective α.left → 1 ≤ N → (∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1) →
    ∃ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ ∧ IsPlaceOver l lam k₀ R₀ ∧
      (∀ x ∈ R₀, x ∈ k₀) ∧
      ∃ (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (p₀ : B.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
        IsAbelianScheme G₀ ∧ IsGrpPullback B G₀ (spMap R₀.subtype) p₀ ∧ IsMonHom Ψ₀ ∧ IsFinite Ψ₀.left ∧
        Flat Ψ₀.left ∧ Surjective Ψ₀.left ∧
        ∀ (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A'), IsTangent v →
          v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left →
          ∃ v₀ : epsR R₀ ⟶ G₀, IsTangent v₀ ∧ (v' ≫ α).left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left := by
  intro l _ lam k₁ R₁ hk₁ hR₁ hRk₁ P A' _ φ' hφ' B _ α N hB hα hfin hflat hsurj hN hker
  haveI := hR₁.1
  obtain ⟨hNfin, -⟩ := firstFiveLaws.1.mulN (Sp R₁) P N hN
  obtain ⟨K, hK, hk₁K, hdesc⟩ := exists_field_of_isFinite k₁ hk₁ R₁ hRk₁ _
    (pullback.snd (𝟙 P.A ^ N).left (η : 𝟙_ _ ⟶ P.A).left)
  obtain ⟨R₀, hR₀, hR₀K⟩ := exists_place l lam K hK
  haveI := hR₀.1
  have hle : R₁ ≤ R₀ := fun x hx => hR₀.2.2 x (hk₁K (hRk₁ x hx)) (hR₁.2.1 x hx)
  let inc : R₁ →+* R₀ := Subring.inclusion hle
  let a : R₀ →+* K := R₀.subtype.codRestrict K fun x => hR₀K x x.2
  letI : Algebra R₀ K := a.toAlgebra
  haveI : IsFractionRing R₀ K := by
    haveI : FaithfulSMul R₀ K := (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h =>
      Subtype.ext (congrArg (fun z : K => (z : ℂ)) h)
    refine IsFractionRing.of_field _ _ fun z => ?_
    rcases mem_or_inv_mem hK hR₀ z.2 with h | h
    · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
    · refine ⟨1, ⟨(z : ℂ)⁻¹, h⟩, ?_⟩
      have : algebraMap R₀ K ⟨(z : ℂ)⁻¹, h⟩ = z⁻¹ := Subtype.ext rfl
      rw [this, map_one, one_div, inv_inv]
  let t : Sp ℂ ⟶ Sp K := spMap (algebraMap K ℂ)
  haveI := epi_field ℂ K t
  have hta : t ≫ spMap (algebraMap R₀ K) = spMap R₀.subtype := spMap_comp _ _
  have htai : t ≫ spMap (algebraMap R₀ K) ≫ spMap inc = spMap R₁.subtype := by
    rw [reassoc_of% hta, spMap_comp]; rfl
  obtain ⟨P₀, g₀, hg₀⟩ := exists_polPull (spMap inc) P
  obtain ⟨PK, gK, hgK⟩ := exists_polPull (spMap (algebraMap R₀ K)) P₀
  have hg := hgK.comp hg₀
  let φ : A'.left ⟶ PK.A.left := hg.1.lift φ' (A'.hom ≫ t) (by rw [hφ'.1.w, Category.assoc, htai])
  have hφ1 : φ ≫ gK ≫ g₀ = φ' := hg.1.lift_fst _ _ _
  have hφ2 : φ ≫ PK.A.hom = A'.hom ≫ t := hg.1.lift_snd _ _ _
  have hφ : IsGrpPullback A' PK.A t φ := hg.cancel (hφ'.congr htai.symm hφ1.symm) hφ2
  obtain ⟨BK, _, ψ, q, hBK, hψ, hψfin, hψflat, hψsurj, hψN, hq, hαq⟩ :=
    exists_field_model K t PK A' φ hφ B α N hB hN hker (fun x hx => by
      obtain ⟨e, he⟩ : ∃ e : (𝟙_ (Over (Sp ℂ)) ⟶ A') ≃* (Over.mk (spMap R₁.subtype) ⟶ P.A),
          ∀ x, (e x).left = x.left ≫ φ' :=
        exists_mulEquiv_of_isGrpPullback hφ' (𝟙 _) _ (Category.id_comp _).symm
      have h1 : e x ≫ (𝟙 P.A ^ N) = toUnit _ ≫ η := by
        rw [comp_pow, Category.comp_id, ← map_pow, hx, map_one, Hom.one_def]
      have h2 : (x.left ≫ φ') ≫ (𝟙 P.A ^ N).left = spMap R₁.subtype ≫ (η : 𝟙_ _ ⟶ P.A).left := by
        rw [← he]
        simpa using congrArg (fun z => z.left) h1
      obtain ⟨y, hy⟩ := hdesc (pullback.lift _ _ h2) (pullback.lift_snd _ _ _)
      have hy1 : t ≫ y ≫ pullback.fst _ _ = x.left ≫ φ' := by
        rw [← Category.assoc, hy, pullback.lift_fst]
      have hxw : x.left ≫ A'.hom = 𝟙 _ := Over.w x
      have hy2 : (y ≫ pullback.fst _ _) ≫ P.A.hom = 𝟙 _ ≫ spMap (algebraMap R₀ K) ≫ spMap inc := by
        rw [← cancel_epi t, ← Category.assoc, hy1, Category.assoc, hφ'.1.w, reassoc_of% hxw,
          Category.id_comp, htai]
      refine ⟨Over.homMk (hg.1.lift _ _ hy2) (hg.1.lift_snd _ _ _), ?_⟩
      change x.left ≫ φ = t ≫ hg.1.lift _ _ hy2
      refine hg.1.hom_ext ?_ ?_
      · rw [Category.assoc, hφ1, Category.assoc, hg.1.lift_fst, hy1]
      · rw [Category.assoc, hφ2, Category.assoc, hg.1.lift_snd, reassoc_of% hxw]
        exact (Category.comp_id _).symm)
  obtain ⟨G₀, _, φB, Ψ, hG₀, hφB, hΨ, hΨfin, hΨflat, hΨsurj, hΨw⟩ :=
    exists_abelianScheme_model_of_isogeny_dedekind firstFiveLaws.1 R₀ K P₀ PK.A BK gK ψ N hgK hBK hψ hψfin
      hψflat hψsurj hN hψN
  refine ⟨K, R₀, hK, hR₀, hR₀K, G₀, inferInstance, q ≫ φB, P₀, Ψ, hG₀, (hq.comp hφB).congr hta rfl, hΨ, hΨfin,
    hΨflat, hΨsurj, fun v v' hv hvv' => ?_⟩
  obtain ⟨w, hw, -⟩ := existsUnique_isVecOver hg₀.1 v
  refine ⟨w ≫ Ψ, HomLinear.isTangent_comp Ψ (hw.isTangent hg₀ hv), ?_⟩
  have hw' : w.left ≫ g₀ = spMap (Chart.dualMapR inc) ≫ v.left := hw
  have hww : w.left ≫ P₀.A.hom = spMap (algebraMap R₀ (DualNumber R₀)) := Over.w w
  have hv'w : v'.left ≫ A'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v'
  have key : v'.left ≫ φ ≫ gK = spMap (Chart.dualMapR R₀.subtype) ≫ w.left := by
    refine hg₀.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hφ1, hvv', Category.assoc, hw', ← Category.assoc, spMap_comp,
        dualMapR_comp]
      rfl
    · rw [Category.assoc, Category.assoc, hgK.1.w, reassoc_of% hφ2, hta, reassoc_of% hv'w, Category.assoc, hww,
        spMap_comp, spMap_comp, dualMapR_algebraMap]
  rw [Over.comp_left, Over.comp_left, Category.assoc, reassoc_of% hαq, hΨw, ← Category.assoc φ,
    ← Category.assoc, key, Category.assoc]

end GlobalTheory.QuotModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_good_reduction_extension : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ),
    FiniteDimensional ℚ k₁ → IsPlaceOver l lam k₁ R₁ → (∀ x ∈ R₁, x ∈ k₁) →
    ∀ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) [GrpObj A'] (φ' : A'.left ⟶ P.A.left),
    IsGrpPullback A' P.A (spMap R₁.subtype) φ' →
    ∀ (B : Over (Sp ℂ)) [GrpObj B] (α : A' ⟶ B) (N : ℕ), IsAbelianScheme B → IsMonHom α → IsFinite α.left →
    Flat α.left → Surjective α.left → 1 ≤ N → (∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1) →
    ∃ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ ∧ IsPlaceOver l lam k₀ R₀ ∧
      (∀ x ∈ R₀, x ∈ k₀) ∧
      ∃ (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (p₀ : B.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
        IsAbelianScheme G₀ ∧ IsGrpPullback B G₀ (spMap R₀.subtype) p₀ ∧ IsMonHom Ψ₀ ∧ IsFinite Ψ₀.left ∧
        Flat Ψ₀.left ∧ Surjective Ψ₀.left ∧
        ∀ (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A'), IsTangent v →
          v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left →
          ∃ v₀ : epsR R₀ ⟶ G₀, IsTangent v₀ ∧ (v' ≫ α).left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left := by
  atlas_forward_decl GlobalTheory.QuotModel.exists_quotModel
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LatModel.exists_isogModel : GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 →
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X),
    ∃ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ ∧ IsPlaceOver l lam k₀ R₀ ∧
      (∀ x ∈ R₀, x ∈ k₀) ∧
      ∃ (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (p₀ : X.A.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
        IsAbelianScheme G₀ ∧ IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ ∧ IsMonHom Ψ₀ ∧ IsFinite Ψ₀.left ∧
        Flat Ψ₀.left ∧ Surjective Ψ₀.left ∧
        ∀ i : I, ∃ (v₀ : epsR R₀ ⟶ G₀) (v' : X.Lie) (W : Fin (Module.finrank ℚ (FR E)) → ℂ),
          IsTangent v₀ ∧ v'.hom.left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left ∧ U.u.IsDiff W v'.hom ∧
          W (U.e.symm i) ≠ 0 ∧ Sz l lam (a0 𝔣 l) ((W (U.e.symm i) * Ω)⁻¹) := by
  intro hST hAD E _ _ _ _ I _ d φ hF 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy lam Ω hΩ 𝔠 X U
  have hf : 0 < Module.finrank ℚ (FR E) := Module.finrank_pos
  let j₀ : Fin (Module.finrank ℚ (FR E)) := ⟨0, hf⟩
  obtain ⟨k₁, R₁, hk₁, hR₁, hR₁k, P₁, A₁, _, φ₁, L₁, u₁, v₁, v₁', t, hA₁, hdim₁, hpb₁, hΛ₁, hv₁, hv₁', hvv₁, hd₁, ht, hsz⟩ :=
    GlobalTheory.T.elliptic_curve_good_reduction_model hST d Λ hF.1 hΛ l lam Ω hΩ
  obtain ⟨P, A', _, φ', L', u, v, v', hA', hdim, hpb, hΛu, hv, hv', hvv, hd⟩ :=
    GlobalTheory.T.tangent_pullback_elliptic_model R₁ R₁.subtype P₁ A₁ φ₁ L₁ u₁ v₁ v₁' t Λ.lattice hA₁ hdim₁ hpb₁ hΛ₁ hv₁ hv₁' hvv₁ hd₁
      (Module.finrank ℚ (FR E)) j₀
  obtain ⟨α, M, n, N, hα, hfin, hflat, hsurj, hN, hker, hM, hMj, hn, hszn⟩ :=
    GlobalTheory.T.integral_lattice_l_adic_reduction E I d φ hF 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam 𝔠 X U A' L' u hA' hdim hΛu j₀
  obtain ⟨k₀, R₀, hk₀, hR₀, hR₀k, G₀, _, p₀, P₀, Ψ₀, hG₀, hp₀, hΨ, hΨf, hΨfl, hΨs, htan⟩ :=
    GlobalTheory.T.isogeny_good_reduction_extension l lam k₁ R₁ hk₁ hR₁ hR₁k P A' φ' hpb X.A α N X.ab hα hfin hflat hsurj hN hker
  refine ⟨k₀, R₀, hk₀, hR₀, hR₀k, G₀, inferInstance, p₀, P₀, Ψ₀, hG₀, hp₀, hΨ, hΨf, hΨfl, hΨs, fun i ↦ ?_⟩
  obtain ⟨v₀, hv₀, hc⟩ := htan v v' hv hvv
  have hαt : IsTangent (v' ≫ α) := GlobalTheory.HomLinear.isTangent_comp α hv'
  have hW : M (Pi.single j₀ t) = fun _ ↦ t * (n : ℂ) := by
    have : (Pi.single j₀ t : Fin (Module.finrank ℚ (FR E)) → ℂ) = t • Pi.single j₀ 1 := by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rw [this, map_smul, hMj]
    rfl
  refine ⟨v₀, GlobalTheory.Serre.Lie.mk X.rm (v' ≫ α) hαt, M (Pi.single j₀ t), hv₀, ?_, ?_, ?_, ?_⟩
  · simpa using hc
  · simpa using GlobalTheory.HomLinear.isDiff_comp u U.u α M hM hv' hd
  · rw [hW]
    exact mul_ne_zero ht (by exact_mod_cast hn.ne')
  · rw [hW]
    have e : (t * (n : ℂ) * Ω)⁻¹ = (n : ℂ)⁻¹ * (t * Ω)⁻¹ := by
      rw [show t * (n : ℂ) * Ω = (n : ℂ) * (t * Ω) by ring, _root_.mul_inv]
    rw [e]
    simpa using GlobalTheory.LatValRam.sz_mul hszn hsz
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_lattice_l_adic_congruence : GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 →
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X),
    ∃ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ ∧ IsPlaceOver l lam k₀ R₀ ∧
      (∀ x ∈ R₀, x ∈ k₀) ∧
      ∃ (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (p₀ : X.A.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
        IsAbelianScheme G₀ ∧ IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ ∧ IsMonHom Ψ₀ ∧ IsFinite Ψ₀.left ∧
        Flat Ψ₀.left ∧ Surjective Ψ₀.left ∧
        ∀ i : I, ∃ (v₀ : epsR R₀ ⟶ G₀) (v' : X.Lie) (W : Fin (Module.finrank ℚ (FR E)) → ℂ),
          IsTangent v₀ ∧ v'.hom.left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left ∧ U.u.IsDiff W v'.hom ∧
          W (U.e.symm i) ≠ 0 ∧ Sz l lam (a0 𝔣 l) ((W (U.e.symm i) * Ω)⁻¹) := by
  atlas_forward_decl GlobalTheory.LatModel.exists_isogModel
end
end
