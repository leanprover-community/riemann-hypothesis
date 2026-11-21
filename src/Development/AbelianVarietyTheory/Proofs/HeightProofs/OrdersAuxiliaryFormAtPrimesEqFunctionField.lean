import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.CurveInj
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountQAtStGenericSectionPrimes
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRatioFormsAtPoints
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RealisationValuesEqValuedPointOrders
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsIntegralIffMemSpanOneTmulIntegralClosure
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemIntegralClosureOfMemSpan
import BuildAid.ForwardExisting
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import Development.AbelianVarietyTheory.Proofs.HeightProofs.GaussRingCompletionRename
import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.ExistsMulEqMapOfIsAlgebraic

section
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory

def valCentreOn {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) : Ideal S where
  carrier := {a | 0 < u (a : A)}
  add_mem' := fun {a b} ha hb => by
    have := u.map_add (a : A) (b : A)
    exact lt_of_lt_of_le (lt_min ha hb) this
  zero_mem' := by
    change 0 < u ((0 : S) : A)
    simp
  smul_mem' := fun c a ha => by
    change 0 < u ((c : A) * (a : A))
    rw [u.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (h0 _ c.2))

theorem mem_valCentreOn {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) (a : S) :
    a ∈ valCentreOn S u h0 ↔ 0 < u (a : A) := Iff.rfl

theorem valCentreOn_isPrime {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (S : Subalgebra O A) (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) :
    (valCentreOn S u h0).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_valCentreOn]
    simp
  · rw [mem_valCentreOn] at hab
    rw [mem_valCentreOn, mem_valCentreOn]
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    rw [MulMemClass.coe_mul, u.map_mul] at hab
    exact absurd hab (not_lt.2 (add_nonpos hc.1 hc.2))

theorem addVal_eq_of_associated_loc {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ζ : Pts O A) (u : AddValuation A (WithTop ℤ))
    (hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0) (a b : As O A)
    (hab : Associated (algebraMap (As O A) (Loc ζ) a) (algebraMap (As O A) (Loc ζ) b)) :
    u (a : A) = u (b : A) := by
  obtain ⟨w, hw⟩ := hab
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj ζ.asIdeal.primeCompl (w : Loc ζ)
  have ht : IsUnit (algebraMap (As O A) (Loc ζ) t) := IsLocalization.map_units _ t
  have hs : s ∉ ζ.asIdeal := by
    have h1 : IsUnit (algebraMap (As O A) (Loc ζ) s) := by
      have := w.isUnit.mul ht
      simpa only [hst] using this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal s).1 h1
  have h2 : algebraMap (As O A) (Loc ζ) (a * s) = algebraMap (As O A) (Loc ζ) (b * t) := by
    rw [map_mul, map_mul, ← hw, mul_assoc]
    exact congrArg _ hst.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
  have h3 := congrArg (fun x : As O A => u (x : A)) hc
  simp only [MulMemClass.coe_mul, AddValuation.map_mul] at h3
  rw [hz _ c.2, hz _ hs, hz _ t.2] at h3
  simpa using h3

theorem exists_pt_ord_eq_addValuation : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] (ϖ : O), IsUnif A ϖ → ∀ [∀ ζ : Pts O A, IsDVRAt ζ] (u : AddValuation A (WithTop ℤ)), (∀ a ∈ As O A, 0 ≤ u a) → 0 < u (algebraMap O A ϖ) → (∃ a, u a = 1) → ∃ ζ : Pts O A, ∀ a, ord ϖ ζ a = u a := by
  intro O A _ _ _ _ _ ϖ h hD u h0 hϖ h1
  haveI hP := valCentreOn_isPrime (As O A) u h0
  have hcm : ((valCentreOn (As O A) u h0).comap (algebraMap O (As O A))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal O ≤
        (valCentreOn (As O A) u h0).comap (algebraMap O (As O A)) := by
      rw [h.irreducible.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
        mem_valCentreOn]
      exact hϖ
    have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
    rw [← this]
    infer_instance
  have hmax : (valCentreOn (As O A) u h0).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hcm
  let ζ : Pts O A := ⟨valCentreOn (As O A) u h0, hmax⟩
  have hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0 := fun s hs =>
    le_antisymm (not_lt.1 hs) (h0 _ s.2)
  refine ⟨ζ, ?_⟩
  haveI : IsDVRAt ζ := hD ζ
  haveI : IsDomain (Loc ζ) := IsDVRAt.isDomain
  haveI : IsDiscreteValuationRing (Loc ζ) := IsDVRAt.isDVR
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ)
  obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj ζ.asIdeal.primeCompl p
  have hπ : Irreducible (algebraMap (As O A) (Loc ζ) π) := by
    have ht : IsUnit (algebraMap (As O A) (Loc ζ) t) := IsLocalization.map_units _ t
    have : Associated p (algebraMap (As O A) (Loc ζ) π) := ⟨ht.unit, hπt⟩
    exact this.irreducible hp
  have hπpos : 0 < u (π : A) := by
    by_contra hc
    exact hπ.not_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal π).2 hc)
  have key : ∀ a : As O A, (vL ζ a = ⊤ ∧ u (a : A) = ⊤) ∨
      ∃ n : ℕ, vL ζ a = n ∧ u (a : A) = n • u (π : A) := by
    intro a
    by_cases ha : algebraMap (As O A) (Loc ζ) a = 0
    · refine Or.inl ⟨(vL_eq_top_iff ζ a).2 ha, ?_⟩
      rw [addVal_eq_of_associated_loc ζ u hz a 0 (by rw [ha, map_zero])]
      simp
    · obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
      refine Or.inr ⟨n, ?_, ?_⟩
      · rw [vL_eq_addVal]
        exact IsDiscreteValuationRing.addVal_def _ w hπ n hw
      · rw [addVal_eq_of_associated_loc ζ u hz a (π ^ n)
          (by rw [hw, map_pow]; exact associated_unit_mul_left _ _ w.isUnit)]
        rw [SubmonoidClass.coe_pow, u.map_pow]
  have hϖtop : u (algebraMap O A ϖ) ≠ ⊤ := by
    intro ht
    obtain ⟨v, hv⟩ := h.isUnit.exists_right_inv
    have := congrArg u hv
    rw [u.map_mul, ht, top_add, u.map_one] at this
    exact WithTop.top_ne_zero this
  have hϖe : u (algebraMap O A ϖ) = ep ϖ ζ • u (π : A) := by
    rcases key (algebraMap O (As O A) ϖ) with ⟨_, h2⟩ | ⟨n, h2, h3⟩
    · exact absurd h2 hϖtop
    · rw [← coe_ep ζ h, Nat.cast_inj] at h2
      rw [h2]
      exact h3
  have hmtop : u (π : A) ≠ ⊤ := by
    intro ht
    apply hϖtop
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ep_pos ζ h).ne'
    rw [hϖe, hk, succ_nsmul, ht, add_top]
  obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.1 hmtop
  have hM0 : 0 < M := by
    rw [← hM] at hπpos
    exact_mod_cast hπpos
  have key2 : ∀ x : A, (ord ϖ ζ x = ⊤ ∧ u x = ⊤) ∨
      ∃ z : ℤ, ord ϖ ζ x = z ∧ u x = ((z * M : ℤ) : WithTop ℤ) := by
    intro x
    obtain ⟨k, hk⟩ := h.denom x
    have e1 := ord_pow_smul ζ h k x
    rw [ord_of_mem ζ h hk] at e1
    have e2 : u (ϖ ^ k • x) = (((k : ℤ) * (ep ϖ ζ : ℤ) * M : ℤ) : WithTop ℤ) + u x := by
      rw [Algebra.smul_def, map_pow, u.map_mul, u.map_pow, hϖe, ← hM, ← WithTop.coe_nsmul,
        ← WithTop.coe_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_assoc]
    rcases key ⟨_, hk⟩ with ⟨h2, h3⟩ | ⟨n, h2, h3⟩
    · left
      rw [h2, ENat.map_top, eq_comm, WithTop.add_eq_top] at e1
      change u (ϖ ^ k • x) = ⊤ at h3
      rw [h3, eq_comm, WithTop.add_eq_top] at e2
      exact ⟨e1.resolve_left WithTop.coe_ne_top, e2.resolve_left WithTop.coe_ne_top⟩
    · right
      rw [h2, ENat.map_natCast] at e1
      change u (ϖ ^ k • x) = _ at h3
      rw [h3, ← hM, ← WithTop.coe_nsmul, nsmul_eq_mul] at e2
      refine ⟨n - k * ep ϖ ζ, ?_, ?_⟩
      · generalize ord ϖ ζ x = y at e1
        cases y with
        | top => simp at e1
        | coe y =>
          rw [← WithTop.coe_add, WithTop.coe_inj] at e1
          rw [WithTop.coe_inj]
          linarith
      · generalize u x = y at e2
        cases y with
        | top => exact absurd (e2.trans (add_top _)) WithTop.coe_ne_top
        | coe y =>
          rw [← WithTop.coe_add, WithTop.coe_inj] at e2
          rw [WithTop.coe_inj]
          linarith
  have hM1 : M = 1 := by
    obtain ⟨a, ha⟩ := h1
    rcases key2 a with ⟨_, h3⟩ | ⟨z, _, h3⟩
    · rw [ha] at h3
      exact absurd h3 WithTop.one_ne_top
    · rw [ha, ← WithTop.coe_one, WithTop.coe_inj] at h3
      exact Int.eq_one_of_mul_eq_one_left hM0.le h3.symm
  intro a
  rcases key2 a with ⟨h2, h3⟩ | ⟨z, h2, h3⟩
  · rw [h2, h3]
  · rw [h2, h3, hM1, mul_one]

end GlobalTheory
end

section
section
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory.ResDegPlace

open IsLocalRing

theorem finrank_eq_of_surjective {S₀ S k K k' K' : Type*} [CommRing S₀] [CommRing S] [Field k]
    [Field K] [Field k'] [Field K'] [Algebra k K] [Algebra k' K'] (j : S₀ →+* S)
    (p₀ : S₀ →+* k) (q₀ : S₀ →+* k') (p : S →+* K) (q : S →+* K')
    (hp₀ : Function.Surjective p₀) (hq₀ : Function.Surjective q₀)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hker : ∀ x, p x = 0 ↔ q x = 0)
    (h₁ : ∀ r, algebraMap k K (p₀ r) = p (j r)) (h₂ : ∀ r, algebraMap k' K' (q₀ r) = q (j r)) :
    Module.finrank k K = Module.finrank k' K' := by
  have hk : RingHom.ker p = RingHom.ker q := by
    ext x; simp only [RingHom.mem_ker]; exact hker x
  have hk₀ : RingHom.ker p₀ = RingHom.ker q₀ := by
    ext x
    simp only [RingHom.mem_ker]
    rw [← map_eq_zero_iff _ (algebraMap k K).injective, h₁, hker, ← h₂,
      map_eq_zero_iff _ (algebraMap k' K').injective]
  let e : K ≃+* K' := (RingHom.quotientKerEquivOfSurjective hp).symm.trans
    ((Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective hq))
  let e₀ : k ≃+* k' := (RingHom.quotientKerEquivOfSurjective hp₀).symm.trans
    ((Ideal.quotEquivOfEq hk₀).trans (RingHom.quotientKerEquivOfSurjective hq₀))
  have he : ∀ x, e (p x) = q x := fun x => by
    have : (RingHom.quotientKerEquivOfSurjective hp).symm (p x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [e, RingEquiv.trans_apply, this]; rfl
  have he₀ : ∀ x, e₀ (p₀ x) = q₀ x := fun x => by
    have : (RingHom.quotientKerEquivOfSurjective hp₀).symm (p₀ x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [e₀, RingEquiv.trans_apply, this]; rfl
  refine Algebra.finrank_eq_of_equiv_equiv e₀ e ?_
  ext y
  obtain ⟨r, rfl⟩ := hp₀ y
  change algebraMap k' K' (e₀ (p₀ r)) = e (algebraMap k K (p₀ r))
  rw [he₀, h₂, h₁, he]

theorem mem_maximalIdeal_vRing {L : Type*} [Field L] (w : AddValuation L (WithTop ℤ))
    (x : vRing w) : x ∈ maximalIdeal (vRing w) ↔ 0 < w (x : L) := by
  have hunit : IsUnit x ↔ w (x : L) = 0 :=
    (Valuation.valuationSubring.integers (w : Valuation L _)).isUnit_iff_valuation_eq_one
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
  exact ⟨fun h => lt_of_le_of_ne x.2 (Ne.symm h), fun h => h.ne'⟩

theorem exists_eq_of_nonneg {R F L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] {w : AddValuation L (WithTop ℤ)} (hw : w ∈ ValPl.PlacesOver R L)
    (x : F) (hx : 0 ≤ w (algebraMap F L x)) : ∃ a : R, algebraMap R F a = x := by
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [map_zero, hx0]⟩
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, ha⟩
  · by_cases hau : IsUnit a
    · obtain ⟨u, rfl⟩ := hau
      refine ⟨↑u⁻¹, ?_⟩
      rw [map_units_inv, ha, inv_inv]
    · exfalso
      have hpos := ((hw.2 a).2).2 hau
      rw [IsScalarTower.algebraMap_apply R F L, ha, map_inv₀] at hpos
      have hxL : algebraMap F L x ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F L).injective]; exact hx0
      have hs : w (algebraMap F L x) + w (algebraMap F L x)⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ hxL, AddValuation.map_one]
      have := ValPl.wt_add_eq_zero hx hpos.le hs
      rw [this, zero_add] at hs
      rw [hs] at hpos
      exact lt_irrefl _ hpos

section
variable {O A : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}

theorem ord_pos_iff (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (a : As O A) :
    0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
  rw [ord_of_mem ζ h a.2, ← not_not (a := a ∈ ζ.asIdeal), ← vL_eq_zero_iff ζ a]
  change 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe n =>
    rw [ENat.map_natCast, WithTop.coe_pos]
    simp [Nat.pos_iff_ne_zero]

theorem exists_approx (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (x : A) (hx : 0 ≤ ord ϖ ζ x) :
    ∃ a : As O A, 0 < ord ϖ ζ ((a : A) - x) := by
  obtain ⟨n, hn⟩ := h.denom x
  have h1 := hx
  rw [ord_eq ζ h hn, ordAt_nonneg_iff ζ h, vL_eq_addVal, vL_eq_addVal,
    IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
  obtain ⟨c, hc⟩ := h1
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective ζ.asIdeal.primeCompl c
  have h2 : algebraMap (As O A) (Loc ζ) (⟨ϖ ^ n • x, hn⟩ * (s : As O A)) =
      algebraMap (As O A) (Loc ζ) (algebraMap O (As O A) ϖ ^ n * b) := by
    rw [map_mul, hc, mul_assoc, IsLocalization.mk'_spec, ← map_mul]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
  have h3 : (algebraMap O A ϖ) ^ n * ((((t : As O A) : A) * ((s : As O A) : A)) * x) =
      (algebraMap O A ϖ) ^ n * (((t : As O A) : A) * (b : A)) := by
    have := congrArg Subtype.val ht
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Algebra.smul_def, map_pow] at this
    have e : ((algebraMap O (As O A) ϖ : As O A) : A) = algebraMap O A ϖ := rfl
    rw [e] at this
    linear_combination this
  have h4 := (h.isUnit.pow n).mul_right_inj.1 h3
  obtain ⟨d, i, hi, hdi⟩ := Ideal.IsMaximal.exists_inv ζ.isMaximal (t * s).2
  refine ⟨d * (t * b), ?_⟩
  have h5 : ((d * (t * b) : As O A) : A) - x = ((-i : As O A) : A) * x := by
    have := congrArg Subtype.val hdi
    simp only [Submonoid.coe_mul, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one,
      NegMemClass.coe_neg] at this ⊢
    linear_combination x * this - (d : A) * h4
  rw [h5, ord_mul ζ h]
  exact add_pos_of_pos_of_nonneg ((ord_pos_iff h ζ _).2 (ζ.asIdeal.neg_mem hi)) hx

end

theorem pos_of_sub_pos {S : Type*} [CommRing S] (u : AddValuation S (WithTop ℤ)) {x y : S}
    (h : 0 < u (x - y)) (hy : 0 < u y) : 0 < u x := by
  have := u.map_lt_add h hy
  rwa [sub_add_cancel] at this

theorem fdeg_eq_finrank_residueField : ∀ (R R' F : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F], Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif A ϖ → ∀ (ζ : Pts R' A) [IsDVRAt ζ] (w : AddValuation L (WithTop ℤ)), w ∈ ValPl.PlacesOver R L → ∀ (S : Type) [CommRing S] (u : AddValuation S (WithTop ℤ)) (Ψ : A →+* S) (ι : L →+* S), Function.Surjective Ψ → (∀ r : R, Ψ (algebraMap R' A (algebraMap R R' r)) = ι (algebraMap R L r)) → (∀ g, u (ι g) = w g) → (∀ a, ord ϖ ζ a = u (Ψ a)) → (∀ x, 0 ≤ u x → ∃ g, 0 ≤ w g ∧ 0 < u (x - ι g)) → fdeg ζ = (letI := resAlg (F := F) w; Module.finrank (IsLocalRing.ResidueField ((vRing w).comap (algebraMap F L))) (IsLocalRing.ResidueField (vRing w))) := by
  intro R R' F _ _ _ _ _ _ _ _ _ _ _ hRR L _ _ _ _ A _ _ ϖ h ζ _ w hw S _ u Ψ ι hΨ hcomp hι hord
    hres
  letI := resAlg (F := F) w
  let T : Subring (As R' A × vRing w) :=
    { carrier := {z | 0 < u (Ψ (z.1 : A) - ι (z.2 : L))}
      mul_mem' := by
        intro z z' hz hz'
        change 0 < u (Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2))
        have e : Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2) =
            (Ψ (z'.1 : A) - ι (z'.2 : L)) * Ψ z.1 + (Ψ (z.1 : A) - ι (z.2 : L)) * ι z'.2 := by
          rw [map_mul, map_mul]; ring
        rw [e]
        refine u.map_lt_add ?_ ?_
        · rw [u.map_mul, ← hord]
          exact add_pos_of_pos_of_nonneg hz' (ord_nonneg ζ h z.1.2)
        · rw [u.map_mul, hι]
          exact add_pos_of_pos_of_nonneg hz z'.2.2
      one_mem' := by
        change 0 < u (Ψ 1 - ι 1)
        simp
      add_mem' := by
        intro z z' hz hz'
        change 0 < u (Ψ ((z.1 : A) + z'.1) - ι ((z.2 : L) + z'.2))
        rw [map_add, map_add, add_sub_add_comm]
        exact u.map_lt_add hz hz'
      zero_mem' := by
        change 0 < u (Ψ 0 - ι 0)
        simp
      neg_mem' := by
        intro z hz
        change 0 < u (Ψ (-(z.1 : A)) - ι (-(z.2 : L)))
        rw [map_neg, map_neg, ← neg_sub', u.map_neg]
        exact hz }
  have hT : ∀ z : T, 0 < u (Ψ (z.1.1 : A) - ι (z.1.2 : L)) := fun z => z.2
  let jw : R →+* vRing w := (algebraMap R L).codRestrict (vRing w) (fun r => (hw.2 r).1)
  let j : R →+* T := (((algebraMap R' (As R' A)).comp (algebraMap R R')).prod jw).codRestrict T
    (fun r => by
      change 0 < u (Ψ (algebraMap R' A (algebraMap R R' r)) - ι (algebraMap R L r))
      rw [hcomp, sub_self]; simp)
  have hOw : ∀ a : R, algebraMap R F a ∈ (vRing w).comap (algebraMap F L) := fun a => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact (hw.2 a).1
  let φ : R →+* (vRing w).comap (algebraMap F L) := (algebraMap R F).codRestrict _ hOw
  let p : T →+* ResidueField (Loc ζ) := ((residue (Loc ζ)).comp (algebraMap (As R' A) (Loc ζ))).comp
    ((RingHom.fst _ _).comp T.subtype)
  let q : T →+* ResidueField (vRing w) := (residue (vRing w)).comp
    ((RingHom.snd _ _).comp T.subtype)
  refine finrank_eq_of_surjective j ((residue R').comp (algebraMap R R')) ((residue _).comp φ) p q
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro y
    obtain ⟨y, rfl⟩ := hRR y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨r, rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := exists_eq_of_nonneg hw (x : F) x.2
    exact ⟨a, congrArg (residue _) (Subtype.ext ha)⟩
  · intro y
    haveI := ζ.isMaximal
    obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective ζ.asIdeal y
    obtain ⟨g, hg, hag⟩ := hres (Ψ a) (by rw [← hord]; exact ord_nonneg ζ h a.2)
    exact ⟨⟨(a, ⟨g, hg⟩), hag⟩, rfl⟩
  · intro y
    obtain ⟨g, rfl⟩ := residue_surjective y
    obtain ⟨x, hx⟩ := hΨ (ι g)
    obtain ⟨a, ha⟩ := exists_approx h ζ x (by rw [hord, hx, hι]; exact g.2)
    rw [hord, map_sub, hx] at ha
    exact ⟨⟨(a, g), ha⟩, rfl⟩
  · intro z
    change residue (Loc ζ) (algebraMap (As R' A) (Loc ζ) z.1.1) = 0 ↔ residue (vRing w) z.1.2 = 0
    rw [residue_eq_zero_iff, residue_eq_zero_iff, mem_maximalIdeal_vRing,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Loc ζ) ζ.asIdeal, ← ord_pos_iff h, hord, ← hι]
    refine ⟨pos_of_sub_pos u ?_, pos_of_sub_pos u (hT z)⟩
    rw [← neg_sub, u.map_neg]
    exact hT z
  · intro r
    rfl
  · intro r
    change residue (vRing w) (comapIncl (vRing w) (algebraMap F L) (φ r)) = residue (vRing w) (jw r)
    congr 1
    exact Subtype.ext (IsScalarTower.algebraMap_apply R F L r).symm

end GlobalTheory.ResDegPlace
end

open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fdeg_eq_finrank_residueField_alt : ∀ (R R' F : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F], Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif A ϖ → ∀ (ζ : Pts R' A) [IsDVRAt ζ] (w : AddValuation L (WithTop ℤ)), w ∈ ValPl.PlacesOver R L → ∀ (S : Type) [CommRing S] (u : AddValuation S (WithTop ℤ)) (Ψ : A →+* S) (ι : L →+* S), Function.Surjective Ψ → (∀ r : R, Ψ (algebraMap R' A (algebraMap R R' r)) = ι (algebraMap R L r)) → (∀ g, u (ι g) = w g) → (∀ a, ord ϖ ζ a = u (Ψ a)) → (∀ x, 0 ≤ u x → ∃ g, 0 ≤ w g ∧ 0 < u (x - ι g)) → fdeg ζ = (letI := resAlg (F := F) w; Module.finrank (IsLocalRing.ResidueField ((vRing w).comap (algebraMap F L))) (IsLocalRing.ResidueField (vRing w))) := by
  atlas_forward_decl GlobalTheory.ResDegPlace.fdeg_eq_finrank_residueField
end

section
section
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory

namespace CoverPlaces

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}

theorem ord_pos_iff (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (a : As O A) :
    0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
  rw [ord_of_mem ζ h a.2, ← not_iff_not, ← vL_eq_zero_iff]
  change ¬ 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe j =>
    rw [ENat.map_natCast, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    simp

theorem surjective_of_detect [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {T : Type} [Finite T]
    (Z : T → Pts O A) (hZ : ∀ x, (∀ t, 0 ≤ ord ϖ (Z t) x) → x ∈ As O A) :
    Function.Surjective Z := by
  classical
  cases nonempty_fintype T
  intro ζ
  by_contra hne
  have hex : ∀ t, ∃ a ∈ (Z t).asIdeal, a ∉ ζ.asIdeal := by
    intro t
    by_contra hc
    push Not at hc
    exact hne ⟨t, MaximalSpectrum.ext ((Z t).isMaximal.eq_of_le ζ.isMaximal.ne_top hc)⟩
  choose a ha ha' using hex
  haveI := ζ.isMaximal.isPrime
  have hb : ∏ t, a t ∉ ζ.asIdeal := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨t, -, ht⟩
    exact ha' t ht
  have hbt : ∀ t, ∏ t, a t ∈ (Z t).asIdeal := fun t =>
    Ideal.prod_mem _ (Finset.mem_univ t) (ha t)
  generalize ∏ t, a t = b at hb hbt
  obtain ⟨v, hv⟩ := h.isUnit.exists_right_inv
  set n : ℕ := ∑ t, ep ϖ (Z t) with hn
  have hx : v * (b : A) ^ n ∈ As O A := by
    apply hZ
    intro t
    have h1 : ord ϖ (Z t) (algebraMap O A ϖ * (v * (b : A) ^ n)) = n • ord ϖ (Z t) b := by
      rw [← mul_assoc, hv, one_mul, ord_pow _ h]
    rw [ord_mul _ h, ord_unif _ h] at h1
    have h2 := (ord_pos_iff h (Z t) b).2 (hbt t)
    have h3 : ep ϖ (Z t) ≤ n :=
      Finset.single_le_sum (f := fun t => ep ϖ (Z t)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have h4 := ep_pos (Z t) h
    generalize ord ϖ (Z t) (v * (b : A) ^ n) = p at h1
    generalize ord ϖ (Z t) (b : A) = q at h1 h2
    generalize ep ϖ (Z t) = e at h1 h3 h4
    induction p using WithTop.recTopCoe with
    | top => exact le_top
    | coe p =>
      induction q using WithTop.recTopCoe with
      | top =>
        obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hm, succ_nsmul, add_top, ← WithTop.coe_add] at h1
        exact absurd h1 WithTop.coe_ne_top
      | coe q =>
        rw [← WithTop.coe_add, ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul] at h1
        have h5 : 0 < q := by exact_mod_cast h2
        have h6 : (e : ℤ) ≤ n := by exact_mod_cast h3
        have h7 : 0 ≤ p := by nlinarith
        exact_mod_cast h7
  have hp : b ^ n = algebraMap O (As O A) ϖ * ⟨_, hx⟩ := by
    apply Subtype.ext
    change (b : A) ^ n = algebraMap O A ϖ * (v * (b : A) ^ n)
    rw [← mul_assoc, hv, one_mul]
  exact hb (ζ.isMaximal.isPrime.mem_of_pow_mem n (hp ▸ Ideal.mul_mem_right _ _ (unif_mem h ζ)))

theorem isIntegral_of_forall {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Finite ι]
    {S : ι → Type} [∀ c, CommRing (S c)] [∀ c, Algebra R (S c)] (Ψ : ∀ c, A →ₐ[R] S c)
    (hΨ : ∀ a, (∀ c, Ψ c a = 0) → a = 0) (x : A) (hx : ∀ c, IsIntegral R (Ψ c x)) :
    IsIntegral R x := by
  classical
  cases nonempty_fintype ι
  choose p hp hp0 using hx
  refine ⟨∏ c, p c, Polynomial.monic_prod_of_monic _ _ fun c _ => hp c, hΨ _ fun c => ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_algHom_apply, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [Polynomial.aeval_def]; exact hp0 c)

end CoverPlaces

open CoverPlaces in

theorem exists_equiv_pts_places_baseChange : ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (ι : Type) [Finite ι] (L : ι → Type) [∀ c, Field (L c)] [∀ c, Algebra F (L c)] [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)] [∀ c, IsScalarTower R F (L c)] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif A ϖ → ∀ [∀ ζ : Pts R' A, IsDVRAt ζ] (Ψ : ∀ c, A →ₐ[R'] F' ⊗[F] L c), (∀ c, Function.Surjective (Ψ c)) → (∀ a, (∀ c, Ψ c a = 0) → a = 0) → (∀ c c', c ≠ c' → ∃ a, Ψ c a = 0 ∧ Ψ c' a = 1) → ∃ e : Pts R' A ≃ Σ c, ValPl.PlacesOver R (L c), ∀ ζ, fdeg ζ = (letI := resAlg (F := F) (e ζ).2.1; Module.finrank (IsLocalRing.ResidueField ((vRing (e ζ).2.1).comap (algebraMap F (L (e ζ).1)))) (IsLocalRing.ResidueField (vRing (e ζ).2.1))) ∧ ∃ u : AddValuation (F' ⊗[F] L (e ζ).1) (WithTop ℤ), (∀ g, u ((1 : F') ⊗ₜ[F] g) = (e ζ).2.1 g) ∧ ∀ a, ord ϖ ζ a = u (Ψ (e ζ).1 a) := by
  intro R R' F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax hres ι _ L _ _ _ _ _ _ A _ _ ϖ hϖ _ Ψ
    hsurj hinj hsep
  choose w' hw1 hw2 hw3 hw4 using fun c =>
    exists_unique_place_baseChange R R' F F' hmax hres (L c)
      (isIntegral_iff_mem_span_one_tmul_integralClosure R R' F F' hmax hres (L c))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hex : ∀ t : Σ c, ValPl.PlacesOver R (L c), ∃ ζ : Pts R' A,
      ∀ a, ord ϖ ζ a = w' t.1 t.2 (Ψ t.1 a) := by
    rintro ⟨c, w⟩
    refine exists_pt_ord_eq_addValuation R' A ϖ hϖ ((w' c w).comap (Ψ c).toRingHom) ?_ ?_ ?_
    · intro a ha
      exact (hw2 c _).1 (IsIntegral.map (Ψ c) ha) w
    · have hm : ϖ ∈ Ideal.span {algebraMap R R' π} := by
        rw [← PlaceExt.maximalIdeal_eq_span hmax hπ]
        exact hϖ.irreducible.not_isUnit
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hm
      change 0 < w' c w (Ψ c (algebraMap R' A ϖ))
      rw [AlgHom.commutes, ← hr, map_mul, AddValuation.map_mul, PlaceExt.algebraMap_eq_one_tmul,
        hw1]
      exact lt_of_lt_of_le ((w.2.2 π).2.2 hπ.not_isUnit)
        (le_add_of_nonneg_left ((hw2 c _).1 isIntegral_algebraMap w))
    · obtain ⟨g, hg⟩ := w.2.1.2
      obtain ⟨a, ha⟩ := hsurj c ((1 : F') ⊗ₜ[F] g)
      refine ⟨a, ?_⟩
      change w' c w (Ψ c a) = 1
      rw [ha, hw1, hg]
  choose Z hZ using hex
  have hZinj : Function.Injective Z := by
    rintro ⟨c, w⟩ ⟨c', w₂⟩ he
    have h1 : ∀ a, w' c w (Ψ c a) = w' c' w₂ (Ψ c' a) := fun a => by
      rw [← hZ ⟨c, w⟩ a, he, hZ]
    obtain rfl : c = c' := by
      by_contra hc
      obtain ⟨a, h0, h1'⟩ := hsep c c' hc
      have := h1 a
      rw [h0, h1', AddValuation.map_zero, AddValuation.map_one] at this
      exact WithTop.top_ne_zero this
    congr 1
    apply Subtype.ext
    apply AddValuation.ext
    intro g
    obtain ⟨a, ha⟩ := hsurj c ((1 : F') ⊗ₜ[F] g)
    rw [← hw1, ← hw1, ← ha, h1]
  haveI : ∀ c, Finite (ValPl.PlacesOver R (L c)) := fun c => by
    haveI := integralClosure.isDedekindDomain R F (L c)
    haveI := integralClosure.isFractionRing_of_finite_extension (A := R) F (L c)
    exact (ValPl.placesOver_finite (F := F) R (L c)).to_subtype
  have hZsurj : Function.Surjective Z := by
    refine surjective_of_detect hϖ Z fun x hx => ?_
    refine isIntegral_of_forall Ψ hinj x fun c => (hw2 c _).2 fun w => ?_
    have := hx ⟨c, w⟩
    rwa [hZ] at this
  refine ⟨(Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm, fun ζ => ?_⟩
  have hζ : Z ((Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm ζ) = ζ :=
    (Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).apply_symm_apply ζ
  generalize (Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm ζ = t at hζ ⊢
  subst hζ
  obtain ⟨c, w⟩ := t
  refine ⟨?_, w' c w, hw1 c w, hZ ⟨c, w⟩⟩
  refine T.fdeg_eq_finrank_residueField_alt R R' F hres (L c) A ϖ hϖ _ w.1 w.2 (F' ⊗[F] L c) (w' c w) (Ψ c).toRingHom
    (Algebra.TensorProduct.includeRight : L c →ₐ[F] F' ⊗[F] L c).toRingHom (hsurj c) ?_
    (hw1 c w) (hZ ⟨c, w⟩) (hw3 c w)
  intro r
  exact ((Ψ c).commutes _).trans (PlaceExt.algebraMap_eq_one_tmul r)

end GlobalTheory
end

open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_coverPoints_places_baseChange : ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (ι : Type) [Finite ι] (L : ι → Type) [∀ c, Field (L c)] [∀ c, Algebra F (L c)] [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)] [∀ c, IsScalarTower R F (L c)] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif A ϖ → ∀ [∀ ζ : Pts R' A, IsDVRAt ζ] (Ψ : ∀ c, A →ₐ[R'] F' ⊗[F] L c), (∀ c, Function.Surjective (Ψ c)) → (∀ a, (∀ c, Ψ c a = 0) → a = 0) → (∀ c c', c ≠ c' → ∃ a, Ψ c a = 0 ∧ Ψ c' a = 1) → ∃ e : Pts R' A ≃ Σ c, ValPl.PlacesOver R (L c), ∀ ζ, fdeg ζ = (letI := resAlg (F := F) (e ζ).2.1; Module.finrank (IsLocalRing.ResidueField ((vRing (e ζ).2.1).comap (algebraMap F (L (e ζ).1)))) (IsLocalRing.ResidueField (vRing (e ζ).2.1))) ∧ ∃ u : AddValuation (F' ⊗[F] L (e ζ).1) (WithTop ℤ), (∀ g, u ((1 : F') ⊗ₜ[F] g) = (e ζ).2.1 g) ∧ ∀ a, ord ϖ ζ a = u (Ψ (e ζ).1 a) := by
  atlas_forward_decl GlobalTheory.exists_equiv_pts_places_baseChange
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.GaussCompletion

theorem exists_gaussRing_map :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ) (σ : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N' ≃ Idx D j N), ∃ (f : ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la →+* Op X la N) (φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N), f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la)) = IsLocalRing.maximalIdeal (Op X la N) ∧ (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧ (∀ o, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la o) = algebraMap (Op X la N) (Kp X la N) (f o)) ∧ (∀ a : B.KO, φ (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧ ∀ q, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = algebraMap (Op X la N) (Kp X la N) (Tv X la N (σ q)) := by
  intro D B P j X la N D' N' σ
  obtain ⟨f, φ, h1, h2, h3, h4, h5, h6, h7⟩ := gaussRing_completion_rename D B P j X la N D' N' σ
  refine ⟨f, φ, h1, h2, h3, h4, h5, fun a => ?_, h7⟩
  rw [IsScalarTower.algebraMap_apply B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N')
    (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'), MvPolynomial.algebraMap_eq]
  exact h6 a

end GlobalTheory.GaussCompletion
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussRing_map_to_completion : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ) (σ : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N' ≃ Idx D j N), ∃ (f : ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la →+* Op X la N) (φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N), f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la)) = IsLocalRing.maximalIdeal (Op X la N) ∧ (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧ (∀ o, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la o) = algebraMap (Op X la N) (Kp X la N) (f o)) ∧ (∀ a : B.KO, φ (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧ ∀ q, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = algebraMap (Op X la N) (Kp X la N) (Tv X la N (σ q)) := by
  atlas_forward_decl GlobalTheory.GaussCompletion.exists_gaussRing_map
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory

theorem exists_away_algHom_ker {K R Q : Type*} [CommRing K] [CommRing R] [CommRing Q] [Algebra K R] [Algebra K Q]
    {n : ℕ} (Ψ : R →ₐ[K] Q) (a : Fin (n + 1) → R) (hs : Function.Surjective Ψ)
    (hk : RingHom.ker Ψ = Ideal.span (Set.range fun i : Fin n => a i.succ)) (hu : IsUnit (Ψ (a 0))) :
    ∃ χ : Localization.Away (a 0) →ₐ[K] Q, Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span (Set.range fun i : Fin n =>
        algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) ∧
      ∀ r, χ (algebraMap R (Localization.Away (a 0)) r) = Ψ r := by
  have hunit : ∀ y : Submonoid.powers (a 0), IsUnit (Ψ y) := by
    rintro ⟨_, m, rfl⟩
    simpa using hu.pow m
  let χ : Localization.Away (a 0) →ₐ[K] Q := IsLocalization.liftAlgHom (M := Submonoid.powers (a 0)) hunit
  have hχ : ∀ r, χ (algebraMap R (Localization.Away (a 0)) r) = Ψ r := fun r => by
    simp [χ]
  refine ⟨χ, fun q => ?_, le_antisymm ?_ ?_, hχ⟩
  · obtain ⟨r, rfl⟩ := hs q
    exact ⟨_, hχ r⟩
  · intro z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers (a 0)) z
    have hr : r ∈ RingHom.ker Ψ := by
      rw [RingHom.mem_ker] at hz ⊢
      have := congrArg χ hrs
      rw [map_mul, hz, zero_mul, hχ] at this
      exact this.symm
    rw [hk] at hr
    have hle : Ideal.span (Set.range fun i : Fin n => a i.succ) ≤
        (Ideal.span (Set.range fun i : Fin n =>
          algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))).comap
          (algebraMap R (Localization.Away (a 0))) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have e : algebraMap R (Localization.Away (a 0)) (a i.succ) =
          algebraMap R (Localization.Away (a 0)) (a 0) *
            (algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) := by
        rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
      show algebraMap R (Localization.Away (a 0)) (a i.succ) ∈ Ideal.span _
      rw [e]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have h2 := hle hr
    rw [Ideal.mem_comap] at h2
    simp only at hrs
    rw [← hrs] at h2
    exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units _ s)).1 h2
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have : Ψ (a i.succ) = 0 := by
      rw [← RingHom.mem_ker, hk]
      exact Ideal.subset_span ⟨i, rfl⟩
    show χ _ = 0
    rw [map_mul, hχ, this, zero_mul]

open ReciprocityTheory.ChartRestriction.G.T0 in

theorem genericSection_away_quotient {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K']
    [Algebra K Kl] [Algebra Kl K'] {Dd m D' N' : ℕ} (hD : D' + 1 = Dd + 1) (eN : Fin (N' + 1) ≃ Fin m)
    (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (KTf K D' N') (OmS Ω D' N')]
    [FiniteDimensional (KTf K D' N') (OmS Ω D' N')] [Algebra (KTf K D' N') K']
    (t : Fin (Dd + 1) × Fin m → K') (v : Fin m → Ω)
    (hs : ∀ p : KTp K D' N', algebraMap (KTf K D' N') (OmS Ω D' N') (algebraMap (KTp K D' N') (KTf K D' N') p) =
      sHom j₀ x p)
    (hK : ∀ a : K, algebraMap (KTf K D' N') K' (algebraMap K (KTf K D' N') a) = algebraMap Kl K' (algebraMap K Kl a))
    (ht : ∀ q : TVar D' N', algebraMap (KTf K D' N') K' (algebraMap (KTp K D' N') (KTf K D' N') (MvPolynomial.X q)) =
      t (Fin.cast hD q.1, eN q.2))
    (hv : v (eN j₀) ≠ 0) (hx : ∀ k, x k * v (eN j₀) = v (eN (j₀.succAbove k)))
    (a : Fin (Dd + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω)) (ha : ∀ i, a i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) :
    ∃ χ : Localization.Away (a 0) →ₐ[K'] K' ⊗[KTf K D' N'] OmS Ω D' N', Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) ∧
      ∀ ω : Ω, χ (algebraMap (K' ⊗[Kl] (Kl ⊗[K] Ω)) (Localization.Away (a 0)) ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω))) =
        (1 : K') ⊗ₜ[KTf K D' N'] algebraMap Ω (OmS Ω D' N') ω := by
  obtain rfl : D' = Dd := by omega
  letI : Algebra K K' := ((algebraMap Kl K').comp (algebraMap K Kl)).toAlgebra
  haveI : IsScalarTower K Kl K' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (KTf K D' N') K' := IsScalarTower.of_algebraMap_eq fun c => (hK c).symm
  obtain ⟨Φ, hΦ, hsurj, hker, hunit⟩ := genericSection_quotient K Ω K' D' N' j₀ x
    (fun q => t (q.1, eN q.2)) (fun k => v (eN k) / v (eN j₀)) hs (fun q => (ht q).symm) (div_self hv)
    (fun k => by rw [div_eq_iff hv, hx])
  let Φ' : K' ⊗[K] Ω →ₐ[K'] K' ⊗[KTf K D' N'] OmS Ω D' N' :=
    { Φ with
      commutes' := fun c => by
        show Φ (c ⊗ₜ[K] 1) = c ⊗ₜ 1
        rw [hΦ, map_one] }
  let e : K' ⊗[Kl] (Kl ⊗[K] Ω) ≃ₐ[K'] K' ⊗[K] Ω := Algebra.TensorProduct.cancelBaseChange K Kl K' K' Ω
  have he : ∀ (c : K') (ω : Ω), e (c ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω)) = c ⊗ₜ[K] ω := fun c ω => by
    simp [e]
  let u : K' ⊗[K] Ω := (1 : K') ⊗ₜ[K] v (eN j₀)
  have hu : IsUnit u :=
    (IsUnit.mk0 _ hv).map (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Ω))
  have hea : ∀ i, e (a i) = u * ∑ k, t (i, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀)) := fun i => by
    rw [ha, map_sum, Finset.mul_sum, ← Equiv.sum_comp eN]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [he, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_div_cancel₀ _ hv]
  have hΨ : ∀ r, (Φ'.comp e.toAlgHom) r = Φ (e r) := fun _ => rfl
  obtain ⟨χ, h1, h2, h3⟩ := exists_away_algHom_ker (Φ'.comp e.toAlgHom) a (hsurj.comp e.surjective)
    (by
      apply le_antisymm
      · intro r hr
        have hr' : e r ∈ RingHom.ker Φ := hr
        rw [hker] at hr'
        have hle : Ideal.span (Set.range fun i : Fin D' =>
            (∑ k, t (i.succ, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀)) : K' ⊗[K] Ω)) ≤
            (Ideal.span (Set.range fun i : Fin D' => a i.succ)).comap e.symm := by
          rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          have h0 : a i.succ ∈ Ideal.span (Set.range fun i : Fin D' => a i.succ) := Ideal.subset_span ⟨i, rfl⟩
          rw [← e.symm_apply_apply (a i.succ), hea, map_mul,
            Ideal.unit_mul_mem_iff_mem _ (hu.map e.symm)] at h0
          exact h0
        have := hle hr'
        rwa [Ideal.mem_comap, AlgEquiv.symm_apply_apply] at this
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        show Φ (e (a i.succ)) = 0
        have : Φ (∑ k, t (i.succ, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀))) = 0 := by
          rw [← RingHom.mem_ker, hker]
          exact Ideal.subset_span ⟨i, rfl⟩
        rw [hea, map_mul, this, mul_zero])
    (by rw [hΨ, hea, map_mul]; exact (hu.map Φ).mul hunit)
  exact ⟨χ, h1, h2, fun ω => by rw [h3, hΨ, he, hΦ]⟩

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) {wL : WeightFamilies.Wt D j}
  (w : Fin N → B.Cusp j wL)

theorem componentRing_sec_eq_sum (i : Fin (WeightFamilies.dimY D j + 1)) :
    rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) =
      ∑ k, algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k)) ⊗ₜ[X.Kl la]
        ((1 : X.Kl la) ⊗ₜ[B.KO] gF (X.inc wL (w k))) := by
  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem componentRing_map_sectionIdeal : Ideal.map (phiZ X la N Ω gF w) (Jid X la w) =
    Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ)) *
        IsLocalization.Away.invSelf (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) := by
  have key : ∀ {R : Type} [CommRing R] {a b c : R}, a * b = 1 → a * c = 1 → b = c :=
    fun {_} _ {_} {b} {c} h1 h2 => by linear_combination c * h1 - b * h2
  rw [Jid, Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  show phiZ X la N Ω gF w (sfr X la w i.succ) = _
  rw [phiZ_apply, coe_sfr, frac_apply, pow_one, map_mul, lwZ_alg]
  congr 1
  have h1 := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h1
  exact key h1 (IsLocalization.Away.mul_invSelf _)

end Rec

theorem componentRing_away_quotient :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (D' N' : ℕ) (hD : D' + 1 = WeightFamilies.dimY D j + 1) (eN : Fin (N' + 1) ≃ Fin N) (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [FiniteDimensional (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N)], (∀ p : ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') p) = ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ a : B.KO, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) → (∀ q : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = algebraMap (Op X la N) (Kp X la N) (Tv X la N (Fin.cast hD q.1, eN q.2))) → gF (X.inc wL (w (eN j₀))) ≠ 0 → (∀ k, x k * gF (X.inc wL (w (eN j₀))) = gF (X.inc wL (w (eN (j₀.succAbove k))))) → ∃ χ : RZs X la N Ω gF w →ₐ[Kp X la N] Kp X la N ⊗[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N', Function.Surjective χ ∧ RingHom.ker χ = Ideal.map (phiZ X la N Ω gF w) (Jid X la w) ∧ ∀ ω : Ω, χ (CurveLoc.psiZ X la N w gF ω) = (1 : Kp X la N) ⊗ₜ[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') ω := by
  intro D B P j X la N wL w Ω _ _ gF D' N' hD eN j₀ x _ _ _ hs hK ht hv hx
  rw [componentRing_map_sectionIdeal]
  exact genericSection_away_quotient (Kl := X.Kl la) hD eN j₀ x
    (fun p => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)) (fun k => gF (X.inc wL (w k))) hs hK ht hv hx
    (fun i => rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i))
    (fun i => componentRing_sec_eq_sum X la N Ω gF w i)

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentRing_away_genericSection_quotient : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (D' N' : ℕ) (hD : D' + 1 = WeightFamilies.dimY D j + 1) (eN : Fin (N' + 1) ≃ Fin N) (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [FiniteDimensional (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N)], (∀ p : ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') p) = ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ a : B.KO, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) → (∀ q : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = algebraMap (Op X la N) (Kp X la N) (Tv X la N (Fin.cast hD q.1, eN q.2))) → gF (X.inc wL (w (eN j₀))) ≠ 0 → (∀ k, x k * gF (X.inc wL (w (eN j₀))) = gF (X.inc wL (w (eN (j₀.succAbove k))))) → ∃ χ : RZs X la N Ω gF w →ₐ[Kp X la N] Kp X la N ⊗[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N', Function.Surjective χ ∧ RingHom.ker χ = Ideal.map (phiZ X la N Ω gF w) (Jid X la w) ∧ ∀ ω : Ω, χ (CurveLoc.psiZ X la N w gF ω) = (1 : Kp X la N) ⊗ₜ[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') ω := by
  atlas_forward_decl GlobalTheory.componentRing_away_quotient
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.NetOrders

theorem exists_quot_maps {K' Fr : Type} [Field K'] [CommRing Fr] [Algebra K' Fr] (J : Ideal Fr)
    {ι : Type} [Fintype ι] {R : ι → Type} [∀ c, CommRing (R c)] [∀ c, Algebra K' (R c)]
    (φ : ∀ c, Fr →ₐ[K'] R c) (hinj : ∀ f : Fr, (∀ c, φ c f = 0) → f = 0)
    (hone : ∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → ∀ c c', RingHom.ker (φ c) ≤ Q →
      RingHom.ker (φ c') ≤ Q → c = c')
    (hloc : ∀ c (r : R c), ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a)
    {S : ι → Type} [∀ c, CommRing (S c)] [∀ c, Algebra K' (S c)] (χ : ∀ c, R c →ₐ[K'] S c)
    (hs : ∀ c, Function.Surjective (χ c)) (hk : ∀ c, RingHom.ker (χ c) = Ideal.map (φ c) J) :
    ∃ Ψ : ∀ c, (Fr ⧸ J) →ₐ[K'] S c, (∀ c x, Ψ c (Ideal.Quotient.mk J x) = χ c (φ c x)) ∧
      (∀ c, Function.Surjective (Ψ c)) ∧ (∀ a, (∀ c, Ψ c a = 0) → a = 0) ∧
      ∀ c c', c ≠ c' → ∃ a, Ψ c a = 0 ∧ Ψ c' a = 1 := by
  have hJ : ∀ c, ∀ x ∈ J, χ c (φ c x) = 0 := fun c x hx => by
    rw [← RingHom.mem_ker, hk]; exact Ideal.mem_map_of_mem _ hx
  have hJK : ∀ c, ∀ x ∈ J ⊔ RingHom.ker (φ c), χ c (φ c x) = 0 := fun c x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, map_add, hJ c a ha, (RingHom.mem_ker).1 hb, map_zero, add_zero]
  refine ⟨fun c => Ideal.Quotient.liftₐ J ((χ c).comp (φ c)) (hJ c), fun c x => rfl, fun c s => ?_,
    fun a ha => ?_, fun c c' hne => ?_⟩
  · obtain ⟨r, rfl⟩ := hs c s
    obtain ⟨a, p, hp, e⟩ := hloc c r
    have hu := LocalUnitReduction.isUnit_mk_of_forall_prime (I := J ⊔ RingHom.ker (φ c)) (p := p)
      fun Q hQ hle => hp Q hQ (le_sup_left.trans hle) (le_sup_right.trans hle)
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : p * q - 1 ∈ J ⊔ RingHom.ker (φ c) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hq, map_one, sub_self]
    have h2 := hJK c _ h1
    refine ⟨Ideal.Quotient.mk J (q * a), ?_⟩
    show χ c (φ c (q * a)) = _
    simp only [map_sub, map_mul, map_one] at h2 ⊢
    rw [← e, map_mul]
    linear_combination (χ c r) * h2
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine LocalUnitReduction.mem_of_forall_sup_ker J φ hinj hone fun c => LocalUnitReduction.mem_sup_ker J φ (hloc c) ?_
    rw [← hk]; exact ha c
  · have htop : (J ⊔ RingHom.ker (φ c')) ⊔ RingHom.ker (φ c) = ⊤ := by
      by_contra hne'
      obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne'
      exact hne (hone Q hQ.isPrime (le_sup_left.trans (le_sup_left.trans hle)) c c' (le_sup_right.trans hle)
        (le_sup_right.trans (le_sup_left.trans hle)))
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 htop)
    refine ⟨Ideal.Quotient.mk J b, ?_, ?_⟩
    · show χ c (φ c b) = 0
      rw [(RingHom.mem_ker).1 hb, map_zero]
    · show χ c' (φ c' b) = 1
      have := congrArg (fun z => χ c' (φ c' z)) e
      simpa only [map_add, hJK c' a ha, zero_add, map_one] using this

theorem addVal_mul_pow {S : Type} [CommRing S] (u : AddValuation S (WithTop ℤ)) (a b : S) (m : ℕ) :
    u (a * b ^ m) = u a + m • u b := by
  rw [u.map_mul, u.map_pow]

open ReciprocityTheory.ChartRestriction.G.T0 (Data KTf KTp OmS TVar algOpKT) in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_equiv_places {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
    {ι : Type} [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
    (gF : ∀ c, X.Forms →ₐ[B.KO] Ω c)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ c, gF c (X.inc u F) = 0) → F = 0)
    (hsplit : ∀ (c : ι) (k : Fin N), ∃ g : B.Cusp j wL, gF c (X.inc wL g) = gF c (X.inc wL (w k)) ∧
      ∀ c', c' ≠ c → gF c' (X.inc wL g) = 0)
    (hB : ∀ c, CurveLoc.BirAt X N w (gF c)) (hC : ∀ c, CurveLoc.CountQAt X la N w (gF c))
    [FiniteDimensional (Kp X la N) (OsK X la w)] [IsReduced (OsK X la w)]
    {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)]
    [∀ c, Algebra B.KO (A c)] [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
    (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin N)
    (hD : d.D = WeightFamilies.dimY D j) (h0 : ∀ c, gF c (X.inc wL (w (eN (d.jc c)))) ≠ 0)
    (hx : ∀ c k, d.x c k * gF c (X.inc wL (w (eN (d.jc c)))) = gF c (X.inc wL (w (eN ((d.jc c).succAbove k))))) :
    ∃ e : Pts (Op X la N) (OsK X la w) ≃ Σ c, {v // v ∈ d.PlOver la c}, ∀ ζ,
      fdeg ζ = d.fze hs (e ζ).1 (e ζ).2.1 ∧ ∃ κ : WithTop ℤ, κ ≠ ⊤ ∧ ∀ (m : ℕ) (F : X.Forms)
        (hF : Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F ∈ Vw X la N (addL (wt0 D j) wL m)),
        ord (unifO X la N) ζ (toOsK X la w (CurveLoc.fr0 X la N w m F hF)) =
          d.Wres (e ζ).1 (e ζ).2.1 (gF (e ζ).1 F) + m • κ := by
  have hD' : d.D + 1 = WeightFamilies.dimY D j + 1 := by rw [hD]
  obtain ⟨f, φ, hflat, hloc, hmax, hres, hφ, hφK, hφT⟩ :=
    GlobalTheory.T.exists_gaussRing_map_to_completion D B P j X la N d.D d.N (Equiv.prodCongr (finCongr hD') eN)
  letI : ∀ c, Algebra (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS hs c).toAlgebra
  letI : ∀ c, Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp hs la c
  letI := algOpKT (K := B.KO) d.D d.N la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_Op (K := B.KO) d.D d.N la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.Op_isDVR (K := B.KO) d.D d.N la
  haveI := fun c => (d.comp_facts hd hs la c).2.1
  haveI := fun c => (d.comp_facts hd hs la c).2.2.1
  haveI := fun c => (d.comp_facts hd hs la c).2.2.2.1
  letI : Algebra (KTf B.KO d.D d.N) (Kp X la N) := φ.toAlgebra
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) := f.toAlgebra
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Kp X la N) :=
    ((algebraMap (Op X la N) (Kp X la N)).comp f).toAlgebra
  haveI : IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) (Kp X la N) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (KTf B.KO d.D d.N) (Kp X la N) :=
    IsScalarTower.of_algebraMap_eq fun o => (hφ o).symm
  haveI : Module.Flat (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) := hflat
  haveI : IsLocalHom (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N)) := hloc
  have hres' : Function.Surjective (IsLocalRing.ResidueField.map
      (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N))) := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, ha⟩ := hres x
    refine ⟨IsLocalRing.residue _ a, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact ha
  choose χ hχs hχk hχψ using fun c => GlobalTheory.T.componentRing_away_genericSection_quotient D B P j X la N wL w (Ω c) (gF c) d.D d.N hD' eN (d.jc c) (d.x c)
    (fun p => IsFractionRing.lift_algebraMap (g := (d.sH c).toRingHom) (hs c) p) hφK hφT (h0 c) (hx c)
  obtain ⟨Ψ, hΨ, hΨs, hΨi, hΨsep⟩ := exists_quot_maps (Jid X la w) (fun c => phiZ X la N (Ω c) (gF c) w)
    (CurveInj.fraction_zero_injective X la N Ω gF w hinj)
    (fun Q hQ _ c c' => CurveLoc.one_of_split X la N w Ω gF hsplit Q hQ c c')
    (fun c => CurveLoc.loc_of_bir X la N w (gF c) (hB c) (hC c)) χ hχs hχk
  haveI : CharZero (Kp X la N) := by
    haveI : CharZero (X.Kl la) := charZero_of_injective_algebraMap (algebraMap B.KO (X.Kl la)).injective
    exact charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective
  haveI := (integralClosure_dvr' (Op X la N) (Kp X la N) (OsK X la w)).2
  have hU : IsUnif (OsK X la w) (unifO X la N) :=
    isUnif_of_field (Kp X la N) (Op.irreducible_map X la N
      (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))))
  let Ψ' : ∀ c, OsK X la w →ₐ[Kp X la N] Kp X la N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N := Ψ
  have key : ∀ c (m : ℕ) (F : X.Forms)
      (hF : Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F ∈ Vw X la N (addL (wt0 D j) wL m)),
      Ψ' c (toOsK X la w (CurveLoc.fr0 X la N w m F hF)) =
        ((1 : Kp X la N) ⊗ₜ[KTf B.KO d.D d.N] algebraMap (Ω c) (OmS (Ω c) d.D d.N) (gF c F)) *
          χ c (CurveLoc.invS X la N w (gF c)) ^ m := fun c m F hF => by
    refine (hΨ c _).trans ?_
    rw [CurveLoc.phiZ_fraction_base, map_mul, map_pow, hχψ c]
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_coverPoints_places_baseChange (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) (KTf B.KO d.D d.N) (Kp X la N)
    hmax hres' ι (fun c => OmS (Ω c) d.D d.N) (OsK X la w) (unifO X la N) hU
    (fun c => (Ψ' c).restrictScalars (Op X la N)) hΨs hΨi hΨsep
  refine ⟨e.trans (Equiv.sigmaCongrRight fun c => Equiv.subtypeEquivRight fun v => by
    rw [d.plOver_eq hs la c]), fun ζ => ?_⟩
  obtain ⟨h1, u, hu, hord⟩ := he ζ
  refine ⟨h1, u (χ _ (CurveLoc.invS X la N w (gF (e ζ).1))), ?_, fun m F hF => ?_⟩
  · intro ht
    have := congrArg (fun z => u (χ _ z)) (CurveLoc.weight_zero_section_mul_inv X la N w (gF (e ζ).1))
    simp only [map_mul, map_one, AddValuation.map_mul, ht, add_top, AddValuation.map_one] at this
    exact WithTop.top_ne_zero this
  · exact (hord _).trans ((congrArg u (key (e ζ).1 m F hF)).trans ((addVal_mul_pow u _ _ m).trans
      (congrArg (· + _) (hu _))))

theorem toE_eq_nval {T : CDVR} {a : WithTop ℤ} {x : T.Fr} (h : toE a = nval T.V 1 x) :
    (x = 0 → a = ⊤) ∧ (x ≠ 0 → a = (vV T.V x : ℤ)) := by
  constructor
  · rintro rfl
    rw [nval_zero] at h
    cases a with
    | top => rfl
    | coe n => exact absurd h (EReal.coe_ne_top _)
  · intro hx
    rw [nval_of_ne hx] at h
    cases a with
    | top => exact absurd h.symm (EReal.coe_ne_top _)
    | coe n =>
      have h' : ((n : ℝ) : EReal) = _ := h
      rw [EReal.coe_eq_coe_iff, Nat.cast_one, div_one] at h'
      exact_mod_cast h'

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem comp_val_eq {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
    {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF}
    {la : HeightOneSpectrum (𝓞 B.KO)} {ζ : PtsG G la} {y : E.Pt' la} (h : SecPt ζ y)
    {ι : Type} (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
    (gF : ∀ c, (xplus X E hM).Forms →ₐ[B.KO] Ω c)
    (hsplit : ∀ (c : ι) (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ g : B.Cusp j u,
      gF c ((xplus X E hM).inc u g) = gF c ((xplus X E hM).inc u F) ∧
      ∀ c', c' ≠ c → gF c' ((xplus X E hM).inc u g) = 0)
    (c : ι) (hB : CurveLoc.BirAt (xplus X E hM) G.N G.w (gF c)) (k0 : Fin G.N)
    (hk0 : gF c ((xplus X E hM).inc wL (G.w k0)) ≠ 0)
    (W : AddValuation (Ω c) (WithTop ℤ)) (κ : WithTop ℤ) (hκ : κ ≠ ⊤)
    (hW : ∀ (m : ℕ) (F : (xplus X E hM).Forms)
      (hF : Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N F ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL m)),
      ord (unifO (xplus X E hM) la G.N) ζ
        (toOsK (xplus X E hM) la G.w (CurveLoc.fr0 (xplus X E hM) la G.N G.w m F hF)) = W (gF c F) + m • κ)
    (Z : ι) (v : AddValuation (Ω Z) (WithTop ℤ)) (s : WeightFamilies.Wt D j → ℤ)
    (hv : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u),
      (gF Z ((xplus X E hM).inc u F) = 0 → h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) = 0) ∧
      (gF Z ((xplus X E hM).inc u F) ≠ 0 → h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) ≠ 0 ∧
        vV h.T.V (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F))) =
          WithTop.untopD 0 (v (gF Z ((xplus X E hM).inc u F))) + s u)) :
    (⟨Z, v⟩ : Σ c, AddValuation (Ω c) (WithTop ℤ)) = ⟨c, W⟩ := by
  have hb : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) ≠ 0 := h.s0.ne_zero
  have key : ∀ (m : ℕ) (F : B.Cusp j (addL (wt0 D j) wL m)),
      toE (W (gF c ((xplus X E hM).inc _ F)) + m • κ) =
        nval h.T.V 1 (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc _ F)) *
          (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))⁻¹ ^ m) := by
    intro m F
    rw [← hW m _ (emb_mem_Vw (xplus X E hM) la G.N _ F), h.ord]
    congr 1
    exact h.lift_frac m _
  have hWt : ∀ a : Ω c, a ≠ 0 → W a ≠ ⊤ := fun a ha ht => ha ((AddValuation.top_iff W).1 ht)
  obtain ⟨κ, rfl⟩ := WithTop.ne_top_iff_exists.1 hκ
  obtain rfl : Z = c := by
    by_contra hne
    obtain ⟨k, hk⟩ := GlobalTheory.ConstRatio.ratio_large (xplus X E hM) G.w (gF c) hB k0 hk0 1
    obtain ⟨-, d, hd, -⟩ := hk (k + 1) (Nat.lt_succ_self k)
    obtain ⟨g, hg1, hg2⟩ := hsplit c _ d
    have h1 := (toE_eq_nval (key _ g)).1 (by rw [(hv _ g).1 (hg2 Z hne), zero_mul])
    rw [← WithTop.coe_nsmul, WithTop.add_eq_top] at h1
    rcases h1 with h1 | h1
    · exact hWt _ (hg1 ▸ hd) h1
    · exact WithTop.coe_ne_top h1
  congr 1
  apply AddValuation.ext
  intro a
  by_cases ha : a = 0
  · rw [ha, v.map_zero, W.map_zero]
  have hvt : ∀ a : Ω Z, a ≠ 0 → v a ≠ ⊤ := fun a ha ht => ha ((AddValuation.top_iff v).1 ht)
  obtain ⟨k, hk⟩ := GlobalTheory.ConstRatio.ratio_large (xplus X E hM) G.w (gF Z) hB k0 hk0 a
  obtain ⟨n, d, hd, hn⟩ := hk (k + 1) (Nat.lt_succ_self k)
  have hn0 : gF Z ((xplus X E hM).inc _ n) ≠ 0 := hn ▸ mul_ne_zero ha hd
  have hp := pow_ne_zero (k + 1) (inv_ne_zero hb)
  obtain ⟨n1, n2⟩ := (hv _ n).2 hn0
  obtain ⟨d1, d2⟩ := (hv _ d).2 hd
  have n3 := (toE_eq_nval (key _ n)).2 (mul_ne_zero n1 hp)
  have d3 := (toE_eq_nval (key _ d)).2 (mul_ne_zero d1 hp)
  rw [vV_mul n1 hp, n2, hn, W.map_mul, v.map_mul] at n3
  rw [vV_mul d1 hp, d2] at d3
  obtain ⟨va, hva⟩ := WithTop.ne_top_iff_exists.1 (hvt a ha)
  obtain ⟨Wa, hWa⟩ := WithTop.ne_top_iff_exists.1 (hWt a ha)
  obtain ⟨vd, hvd⟩ := WithTop.ne_top_iff_exists.1 (hvt _ hd)
  obtain ⟨Wd, hWd⟩ := WithTop.ne_top_iff_exists.1 (hWt _ hd)
  rw [← hva, ← hWa, ← hvd, ← hWd] at n3
  rw [← hvd, ← hWd] at d3
  rw [← hva, ← hWa]
  simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.untopD_coe, WithTop.coe_inj] at n3 d3 ⊢
  omega

open ReciprocityTheory.ChartRestriction.G.T0 (Data) in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem net_eq {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
    {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (xplus X E hM) ka wL wF)
    {ι : Type} [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
    (gF : ∀ c, (xplus X E hM).Forms →ₐ[B.KO] Ω c) (val : ∀ c (u : WeightFamilies.Wt D j), B.Cusp j u → Ω c)
    (hval : ∀ c u F, gF c ((xplus X E hM).inc u F) = val c u F)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ c, val c u F = 0) → F = 0)
    (hsplit : ∀ (c : ι) (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ g : B.Cusp j u,
      val c u g = val c u F ∧ ∀ c', c' ≠ c → val c' u g = 0)
    (hB : ∀ c, CurveLoc.BirAt (xplus X E hM) G.N G.w (gF c))
    (hC : ∀ la c, CurveLoc.CountQAt (xplus X E hM) la G.N G.w (gF c))
    (y : ∀ la, PtsG G la → E.Pt' la) (hw : ∀ la ζ, SecPt ζ (y la ζ)) (g0 : B.Cusp j wF)
    (hcur : ∀ la, (secQ (y la) (hw la) g0).InCurve)
    {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)]
    [∀ c, Algebra B.KO (A c)] [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
    (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin G.N)
    (hD : d.D = WeightFamilies.dimY D j) (h0 : ∀ c, val c wL (G.w (eN (d.jc c))) ≠ 0)
    (hx : ∀ c k, d.x c k * val c wL (G.w (eN (d.jc c))) = val c wL (G.w (eN ((d.jc c).succAbove k))))
    (het : ∀ c, val c _ G.et ≠ 0)
    (s : ∀ c, AddValuation (Ω c) (WithTop ℤ) → WeightFamilies.Wt D j → ℤ)
    (hord : ∀ c v, d.ord c v (d.n1 • d.wde) (d.et c) = WithTop.untopD 0 (v (val c _ G.et)) + s c v (etWt D j G.iet))
    (hpt : ∀ la (ζ : PtsG G la), ∃ (Z : ι) (v : AddValuation (Ω Z) (WithTop ℤ)),
      ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u),
      (val Z u F = 0 → (hw la ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) = 0) ∧
      (val Z u F ≠ 0 → (hw la ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) ≠ 0 ∧
        vV (hw la ζ).T.V ((hw la ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F))) =
          WithTop.untopD 0 (v (val Z u F)) + s Z v u)) (Gc PH Prw Pet : ℝ) :
    NetTie d hd hs G (fun la => secQ (y la) (hw la) g0) Gc PH Prw Pet := by
  intro la
  haveI := (hcur la).1
  haveI := (hcur la).2.1
  simp only [← hval] at hinj hsplit h0 hx het hord hpt
  obtain ⟨e, he⟩ := exists_equiv_places (xplus X E hM) la G.N G.w Ω gF hinj (fun c k => hsplit c wL (G.w k)) hB
    (hC la) d hd hs eN hD h0 hx
  refine finsum_eq_of_bijective e e.bijective fun ζ => ?_
  obtain ⟨h1, κ, hκ, hW⟩ := he ζ
  obtain ⟨Z, v, hv⟩ := hpt la ζ
  have hZ := comp_val_eq (hw la ζ) Ω gF hsplit (e ζ).1 (hB _) _ (h0 _) _ κ hκ hW Z v (s Z v) hv
  obtain ⟨e1, e2⟩ := (hv _ G.et).2 (het Z)
  rw [← hord] at e2
  have e3 : d.ord Z v (d.n1 • d.wde) (d.et Z) =
      d.ord (e ζ).1 (d.Wres (e ζ).1 (e ζ).2.1) (d.n1 • d.wde) (d.et (e ζ).1) :=
    congrArg (fun p : Σ c, AddValuation (Ω c) (WithTop ℤ) => d.ord p.1 p.2 (d.n1 • d.wde) (d.et p.1)) hZ
  have e4 := normalized_valuation_mul (hw la ζ).ep_pos _ e1
  rw [← (hw la ζ).hv, e2, e3] at e4
  show (ep (unifO (xplus X E hM) la G.N) ζ : ℝ) * (fdeg ζ : ℝ) * (E.vAt' la (y la ζ) (X.inc _ G.et)).toReal =
    ((1 : ℕ) : ℝ) * (d.fze hs (e ζ).1 (e ζ).2.1 : ℝ) *
      (d.ord (e ζ).1 (d.Wres (e ζ).1 (e ζ).2.1) (d.n1 • d.wde) (d.et (e ζ).1) : ℝ)
  rw [← e4, ← h1]
  push_cast
  ring

theorem ratio_single_mul {Ω M : Type} [Field Ω] (m : M) (a b : Ω) (hb : b ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Ω) (AddMonoidAlgebra.single m a : AddMonoidAlgebra Ω M)
      (AddMonoidAlgebra.single m b) * b = a := by
  have hex : ∃ r : Ω, (AddMonoidAlgebra.single m a : AddMonoidAlgebra Ω M) = r • AddMonoidAlgebra.single m b :=
    ⟨a / b, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ _ hb]⟩
  unfold ReciprocityTheory.ChartRestriction.G.T0.ratio
  rw [dif_pos hex]
  have := hex.choose_spec
  rw [AddMonoidAlgebra.smul_single'] at this
  exact (AddMonoidAlgebra.single_right_injective this).symm

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem netTie_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → ∀ (δ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (T.Q.Dw j) → ℤ), OrdTie hG δ (trivialClassCondition (T.Q.Xo j) T.Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) → ∀ (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (hd : d.AxH (fun Z => AG Z)) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin G.N), d.D = WeightFamilies.dimY D j → (∀ Z v, d.ord Z v = ordC (δ Z v) v) → d.wL = wtZ (wtA wL) wL.n → d.wF = wtZ (wtA wF) wF.n → (∀ k, d.w k = valC hG (wtA wL) wL.n (G.w (eN k)).1) → d.et = valC hG (wtA (wEt D j G.iet)) (wEt D j G.iet).n G.et.1 → d.n1 • d.wde = wtZ (wtA (wEt D j G.iet)) (wEt D j G.iet).n → ∀ (Gc PH Prw Pet : ℝ), NetTie (B := (recB h.toLawsCore)) d hd hs G (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  intro D T h j hj hG _ ka wL wF G S g0 hH hV hC hB y hw hcur htie _ δ hδ d hd hs eN hD hord _ _ hdw hdet hwt
    Gc PH Prw Pet
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  have hpt := GlobalTheory.T.realisation_values_eq_valuedPoint_orders D T h j hj hG ka wL wF G S g0 hH hV hC hB y hw hcur htie δ hδ
  have hQ : CountQAtSt h j hj hG hT := GlobalTheory.SecCount.countQAtSt D T h j hj hG hT
  have hordC : ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (v : AddValuation (Om Z) (WithTop ℤ)) a n f,
      ordC (δ Z v) v (wtZ a n) (valC hG a n f Z) =
        WithTop.untopD 0 (v (evC hG Z f)) + frW (δ Z v) (wtZ a n) := fun Z v a n f => by
    simp only [ordC, valC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  have h0 : ∀ Z, evC hG Z (G.w (eN (d.jc Z))).1 ≠ 0 := fun Z h0 => hd.w_base Z (by
    rw [hdw]; simp only [valC, h0, AddMonoidAlgebra.single_zero])
  refine net_eq (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G (fun Z => Om Z)
    (fun Z => formsEvR j hG hT Z) (fun Z u F => evC hG Z F.1) (fun Z u F => formsEvR_inc h j hj hG hT Z u F) hV hC
    (fun Z => birAt_of h j hj hG hT G hB Z) (fun la Z => hQ ka wL wF G S g0 la hH Z) y
    (fun la ζ => (hw la ζ).toSecPt) g0 hcur d hd hs eN hD h0 (fun Z k => ?_) (fun Z h0 => hd.et_ne Z ?_)
    (fun Z v u => frW (δ Z v) (wtZ (wtA u) u.n)) (fun Z v => ?_) (fun la ζ => ?_) Gc PH Prw Pet
  · unfold ReciprocityTheory.ChartRestriction.G.T0.Data.x
    rw [hdw, hdw]
    exact ratio_single_mul _ _ _ (h0 Z)
  · rw [hdet]
    have h0' : evC hG Z G.et.1 = 0 := h0
    simp only [valC, h0', AddMonoidAlgebra.single_zero]
  · rw [hord, hwt, hdet]
    exact hordC Z v _ _ _
  · obtain ⟨Z, v, -, -, hv⟩ := hpt la ζ
    exact ⟨Z, v, fun u F => ⟨(hv u F).1, fun hne => ⟨((hv u F).2 hne).1,
      ((hv u F).2 hne).2.trans (hordC Z v _ _ _)⟩⟩⟩

end GlobalTheory.NetOrders
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orders_auxiliary_form_at_primes_eq_functionField : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → ∀ (δ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (T.Q.Dw j) → ℤ), OrdTie hG δ (trivialClassCondition (T.Q.Xo j) T.Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) → ∀ (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (hd : d.AxH (fun Z => AG Z)) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin G.N), d.D = WeightFamilies.dimY D j → (∀ Z v, d.ord Z v = ordC (δ Z v) v) → d.wL = wtZ (wtA wL) wL.n → d.wF = wtZ (wtA wF) wF.n → (∀ k, d.w k = valC hG (wtA wL) wL.n (G.w (eN k)).1) → d.et = valC hG (wtA (wEt D j G.iet)) (wEt D j G.iet).n G.et.1 → d.n1 • d.wde = wtZ (wtA (wEt D j G.iet)) (wEt D j G.iet).n → ∀ (Gc PH Prw Pet : ℝ), NetTie (B := (recB h.toLawsCore)) d hd hs G (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  atlas_forward_decl GlobalTheory.NetOrders.netTie_record
end
