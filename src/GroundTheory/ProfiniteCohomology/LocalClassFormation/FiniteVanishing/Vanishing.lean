import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.KummerOpen
import GroundTheory.ProfiniteCohomology.CartierDual
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.FormationThree
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Subgroup

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

theorem zmod_lift_zmultiplesHom_injective {X : Type*} [AddCommGroup X] {p : ℕ} [Fact p.Prime] {c : X}
    (hc : c ≠ 0) (hpc : p • c = 0) :
    Function.Injective (ZMod.lift p ⟨zmultiplesHom X c, by simp [hpc]⟩) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hord : addOrderOf c = p := addOrderOf_eq_prime hpc hc
  rw [← ZMod.intCast_zmod_cast x, ZMod.lift_coe, zmultiplesHom_apply] at hx
  have h := (addOrderOf_dvd_iff_zsmul_eq_zero).2 hx
  rw [hord] at h
  rw [← ZMod.intCast_zmod_cast x]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h

section Fixing

variable (K Ksep : Type) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (n : ℕ)
  [NeZero n]

def rootsOfUnityFixing : OpenSubgroup Gal(Ksep/K) where
  toSubgroup := ⨅ x : galRootsOfUnity.{0} K Ksep n, stabilizer (galRootsOfUnity.{0} K Ksep n).ρ x
  isOpen' := by
    have : Finite (galRootsOfUnity.{0} K Ksep n) :=
      inferInstanceAs (Finite (Additive (rootsOfUnity n Ksep)))
    change IsOpen (((⨅ x : galRootsOfUnity.{0} K Ksep n,
      stabilizer (galRootsOfUnity.{0} K Ksep n).ρ x : Subgroup Gal(Ksep/K))) : Set Gal(Ksep/K))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun x => isOpen_stabilizer _ x

end Fixing

theorem apply_eq_of_mem_rootsOfUnityFixing {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] {n : ℕ} [NeZero n] {σ : Gal(Ksep/K)} (hσ : σ ∈ rootsOfUnityFixing K Ksep n)
    {ζ : Ksep} (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hu : IsUnit ζ := IsUnit.of_pow_eq_one hζ (NeZero.ne n)
  let x : galRootsOfUnity.{0} K Ksep n :=
    Additive.ofMul ⟨hu.unit, (mem_rootsOfUnity n _).2 (Units.ext (by simpa using hζ))⟩
  have h := Subgroup.mem_iInf.1 hσ x
  exact congrArg (fun y : galRootsOfUnity.{0} K Ksep n =>
    (((Additive.toMul y : rootsOfUnity n Ksep) : Ksepˣ) : Ksep)) h

section Trivial

attribute [local instance 2000] Rep.hV2

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem natCard_rootsOfUnity_of_ne_zero {p : ℕ} (hp : (p : K) ≠ 0) :
    Nat.card (rootsOfUnity p Ksep) = p := by
  have : NeZero (p : Ksep) := ⟨by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero_iff _ (algebraMap K Ksep).injective).2 hp⟩
  have : NeZero p := .of_neZero_natCast Ksep
  have : IsSepClosed Ksep := ‹IsSepClosure K Ksep›.sep_closed
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Ksep p

variable {n : ℕ} (hn : (n : K) ≠ 0)

include hn in

theorem finite_cohomology_of_trivial (V : OpenSubgroup Gal(Ksep/K))
    (hV : ∀ σ ∈ V, ∀ ζ : Ksep, ζ ^ n = 1 → σ ζ = ζ) :
    ∀ (A : Rep (ULift.{0} ℤ) (V : Subgroup Gal(Ksep/K))) [IsDiscreteRep A] [Finite A],
      (∀ (g : (V : Subgroup Gal(Ksep/K))) (a : A), A.ρ g a = a) → (∀ a : A, n • a = 0) →
      ∀ r ≤ 2, Finite (cohomology A r) := by
  have hn0 : n ≠ 0 := fun h0 => hn (by simp [h0])
  intro A
  induction hN : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ N ih =>
  intro _ _ htriv hA r hr
  by_cases hsub : Subsingleton A
  · have := subsingleton_cohomology_of_subsingleton A r
    exact Finite.of_subsingleton
  obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := by
    rw [not_subsingleton_iff_nontrivial] at hsub
    exact exists_ne 0

  have hdn : addOrderOf a ∣ n := addOrderOf_dvd_of_nsmul_eq_zero (hA a)
  have hd0 : addOrderOf a ≠ 0 := fun h0 => hn0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdn))
  have hd1 : addOrderOf a ≠ 1 := fun h1 => ha (by rw [← one_nsmul a, ← h1, addOrderOf_nsmul_eq_zero])
  set d := addOrderOf a with hd
  set p := d.minFac
  have hp : p.Prime := Nat.minFac_prime hd1
  have : Fact p.Prime := ⟨hp⟩
  have hpd : p ∣ d := Nat.minFac_dvd d
  set b := (d / p) • a
  have hpb : p • b = 0 := by
    rw [smul_smul, Nat.mul_div_cancel' hpd, hd, addOrderOf_nsmul_eq_zero]
  have hb : b ≠ 0 := by
    intro hb0
    have h1 := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hpd) hp.pos)
      (addOrderOf_dvd_of_nsmul_eq_zero hb0)
    exact absurd h1 (not_le.2 (Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hp.one_lt))
  have hpn : p ∣ n := hpd.trans hdn
  have hpK : (p : K) ≠ 0 := fun h0 => hn (by
    obtain ⟨c, hc⟩ := hpn
    rw [hc, Nat.cast_mul, h0, zero_mul])

  have hcard := natCard_rootsOfUnity_of_ne_zero K Ksep hpK
  have : Finite (rootsOfUnity p Ksep) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have : Nontrivial (rootsOfUnity p Ksep) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact hp.one_lt)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : rootsOfUnity p Ksep)
  have hζ0 : Additive.ofMul ζ ≠ 0 := hζ
  have hζp : p • Additive.ofMul ζ = 0 := by
    have h := pow_card_eq_one' (G := rootsOfUnity p Ksep) (x := ζ)
    rw [hcard] at h
    rw [← ofMul_pow, h]
    rfl
  let j : ZMod p →+ Additive (rootsOfUnity p Ksep) :=
    ZMod.lift p ⟨zmultiplesHom _ (Additive.ofMul ζ), by simp [hζp]⟩
  have hj : Function.Bijective j :=
    (zmod_lift_zmultiplesHom_injective hζ0 hζp).bijective_of_nat_card_le (by
      rw [Nat.card_zmod, Nat.card_congr Additive.ofMul.symm, hcard])
  let e : ZMod p ≃+ Additive (rootsOfUnity p Ksep) := AddEquiv.ofBijective j hj
  let i : ZMod p →+ A := ZMod.lift p ⟨zmultiplesHom A b, by simp [hpb]⟩
  have hi : Function.Injective i := zmod_lift_zmultiplesHom_injective hb hpb

  have hfix : ∀ (σ : (V : Subgroup Gal(Ksep/K))) (x : Additive (rootsOfUnity p Ksep)),
      (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep p)).ρ σ x = x := by
    intro σ x
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    refine hV σ σ.2 _ ?_
    obtain ⟨c, hc⟩ := hpn
    have hxp : (((Additive.toMul x : rootsOfUnity p Ksep) : Ksepˣ) : Ksep) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p _).1 (Additive.toMul x).2, Units.val_one]
    rw [hc, pow_mul, hxp, one_pow]
  let ι : Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep p) ⟶ A :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom (Rep.res (V : Subgroup Gal(Ksep/K)).subtype
      (galRootsOfUnity.{0} K Ksep p)) A).symm (i.comp e.symm.toAddMonoidHom), fun σ => LinearMap.ext fun x => by
      change i (e.symm ((Rep.res (V : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep p)).ρ σ x)) = A.ρ σ (i (e.symm x))
      rw [hfix, htriv]⟩
  have hι : Function.Injective ι.hom := fun x y h => e.symm.injective (hi h)
  let S := cokerShortComplex ι
  have hS : S.ShortExact := cokerShortComplex_shortExact ι hι
  have : IsDiscreteRep S.X₁ :=
    inferInstanceAs (IsDiscreteRep (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep p)))
  have : IsDiscreteRep S.X₂ := (inferInstance : IsDiscreteRep A)
  have : Finite S.X₂ := (inferInstance : Finite A)
  have : IsDiscreteRep S.X₃ := isDiscreteRep_quotient _ _ _
  have hsurj : Function.Surjective S.g.hom := Submodule.mkQ_surjective _
  have : Finite S.X₃ := Finite.of_surjective _ hsurj
  have htrivQ : ∀ (g : (V : Subgroup Gal(Ksep/K))) (q : S.X₃), S.X₃.ρ g q = q := by
    intro g q
    obtain ⟨a', rfl⟩ := hsurj q
    exact (Rep.hom_comm_apply S.g g a').symm.trans (congrArg S.g.hom (htriv g a'))
  have hQ : ∀ q : S.X₃, n • q = 0 := by
    intro q
    obtain ⟨a', rfl⟩ := hsurj q
    rw [← map_nsmul]
    exact (congrArg S.g.hom (hA a')).trans (map_zero _)
  have hlt : Nat.card S.X₃ < N := by
    rw [← hN]
    have := Fintype.ofFinite S.X₃
    have := Fintype.ofFinite A
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_surjective_not_injective _ hsurj fun hinj => hb ?_
    have h0 : S.g.hom (ι.hom (e 1)) = 0 :=
      congrArg (fun φ => φ.hom (e 1)) S.zero
    have h1 : ι.hom (e 1) = b := by
      change i (e.symm (e 1)) = b
      rw [AddEquiv.symm_apply_apply, show (1 : ZMod p) = ((1 : ℤ) : ZMod p) from Int.cast_one.symm,
        ZMod.lift_coe]
      exact one_zsmul b
    rw [← h1]
    exact hinj (h0.trans (map_zero _).symm)
  have h3 : Finite (cohomology S.X₃ r) := ih _ hlt S.X₃ rfl htrivQ hQ r hr
  have h1 : Finite (cohomology S.X₁ r) := finite_cohomology_rootsOfUnity_open K Ksep hpK V r hr
  exact finite_of_exact (cohomologyMap S.f r).hom.toAddMonoidHom (cohomologyMap S.g r).hom.toAddMonoidHom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (cohomology_exact₂ hS r))

end Trivial

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

theorem eq_zero_of_primaryComponent_eq_bot {M : Type*} [AddCommGroup M] :
    ∀ (n : ℕ), n ≠ 0 → (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → AddCommGroup.primaryComponent M ℓ = ⊥) →
      ∀ x : M, n • x = 0 → x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn h x hx
  rcases eq_or_ne n 1 with rfl | h1
  · rwa [one_nsmul] at hx
  set ℓ := n.minFac
  have hℓ : ℓ.Prime := Nat.minFac_prime h1
  obtain ⟨n', hn'⟩ : ℓ ∣ n := Nat.minFac_dvd n
  have hn'0 : n' ≠ 0 := fun h0 => hn (by rw [hn', h0, mul_zero])
  have hy : n' • x = 0 := by
    refine (primaryComponent_eq_bot_iff.1 (h ℓ hℓ ⟨n', hn'⟩)) (n' • x) ⟨1, ?_⟩
    rw [pow_one, smul_smul, ← hn', hx]
  refine ih n' ?_ hn'0 (fun q hq hqn => h q hq (hqn.trans ⟨ℓ, by rw [hn', mul_comm]⟩)) x hy
  rw [hn']
  exact lt_mul_left (Nat.pos_of_ne_zero hn'0) hℓ.one_lt

section Local

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem subsingleton_cohomology_three_galUnits_open (U : OpenSubgroup Gal(Ksep/K)) :
    Subsingleton (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) 3) :=
  (localClassFormationOfIsSepClosure K Ksep).subsingleton_cohomology_three U

theorem subsingleton_cohomology_three_rootsOfUnity {n : ℕ} (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) :
    Subsingleton (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 3) :=
  subsingleton_cohomology_three_rootsOfUnity_open K Ksep hn U
    (subsingleton_cohomology_three_galUnits_open K Ksep U)

end Local

section Sylow

attribute [local instance 2000] Rep.hV2

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem rootsOfUnityFixing_normal (n : ℕ) [NeZero n] :
    ((rootsOfUnityFixing K Ksep n : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).Normal := by
  constructor
  intro σ hσ τ
  refine Subgroup.mem_iInf.2 fun x => ?_
  have h1 := Subgroup.mem_iInf.1 hσ ((galRootsOfUnity.{0} K Ksep n).ρ τ⁻¹ x)
  change (galRootsOfUnity.{0} K Ksep n).ρ (τ * σ * τ⁻¹) x = x
  change (galRootsOfUnity.{0} K Ksep n).ρ σ ((galRootsOfUnity.{0} K Ksep n).ρ τ⁻¹ x) =
    (galRootsOfUnity.{0} K Ksep n).ρ τ⁻¹ x at h1
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1,
    Representation.self_inv_apply]

def rootsOfUnityFixingNormal (n : ℕ) [NeZero n] : OpenNormalSubgroup Gal(Ksep/K) :=
  { rootsOfUnityFixing K Ksep n with isNormal' := rootsOfUnityFixing_normal n }

theorem apply_eq_of_isProPGroup {ℓ : ℕ} (hℓ : ℓ.Prime) {P : Subgroup Gal(Ksep/K)}
    (hP : IsProPGroup ℓ P) {σ : Gal(Ksep/K)} (hσ : σ ∈ P) {ζ : Ksep} (hζ : ζ ^ ℓ = 1) : σ ζ = ζ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let W := rootsOfUnityFixingNormal (K := K) (Ksep := Ksep) ℓ
  have : ((rootsOfUnityFixing K Ksep ℓ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).Normal :=
    rootsOfUnityFixing_normal ℓ
  obtain ⟨k, hk⟩ := (isProPGroup_subgroup_iff_isPGroup_map.1 hP W)
    ⟨QuotientGroup.mk' (W : Subgroup Gal(Ksep/K)) σ, Subgroup.mem_map_of_mem _ hσ⟩
  have hmem : σ ^ ℓ ^ k ∈ rootsOfUnityFixing K Ksep ℓ := by
    have h := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, ← map_pow] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  have hfixk : (σ ^ ℓ ^ k) ζ = ζ := apply_eq_of_mem_rootsOfUnityFixing hmem hζ
  have hu : IsUnit ζ := IsUnit.of_pow_eq_one hζ hℓ.ne_zero
  obtain ⟨m, hm⟩ := map_rootsOfUnity_eq_pow_self σ
    (⟨hu.unit, (mem_rootsOfUnity ℓ _).2 (Units.ext (by simpa using hζ))⟩ : rootsOfUnity ℓ Ksep)
  have hm' : σ ζ = ζ ^ m := hm
  have hpow : ∀ j : ℕ, (σ ^ j) ζ = ζ ^ (m ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hm', ← pow_mul, ← pow_succ']
  have hmodpow : ∀ a : ℕ, ζ ^ a = ζ ^ (a % ℓ) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a ℓ, pow_add, pow_mul, hζ, one_pow, mul_one]
  have hmod : m ^ ℓ ^ k % ℓ = m % ℓ := by
    have h := ZMod.pow_card_pow (p := ℓ) (n := k) (m : ZMod ℓ)
    rw [← Nat.cast_pow] at h
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
  calc σ ζ = ζ ^ m := hm'
    _ = ζ ^ (m ^ ℓ ^ k) := by rw [hmodpow m, hmodpow (m ^ ℓ ^ k), hmod]
    _ = (σ ^ ℓ ^ k) ζ := (hpow _).symm
    _ = ζ := hfixk

variable (K Ksep) [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem nonempty_zmod_addEquiv_rootsOfUnity {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) :
    Nonempty (ZMod ℓ ≃+ Additive (rootsOfUnity ℓ Ksep)) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hcard := natCard_rootsOfUnity_of_ne_zero K Ksep hℓK
  have : Finite (rootsOfUnity ℓ Ksep) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)
  have : Nontrivial (rootsOfUnity ℓ Ksep) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact hℓ.one_lt)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : rootsOfUnity ℓ Ksep)
  have hζ0 : Additive.ofMul ζ ≠ 0 := hζ
  have hζp : ℓ • Additive.ofMul ζ = 0 := by
    have h := pow_card_eq_one' (G := rootsOfUnity ℓ Ksep) (x := ζ)
    rw [hcard] at h
    rw [← ofMul_pow, h]
    rfl
  exact ⟨AddEquiv.ofBijective _ ((zmod_lift_zmultiplesHom_injective hζ0 hζp).bijective_of_nat_card_le
    (by rw [Nat.card_zmod, Nat.card_congr Additive.ofMul.symm, hcard]))⟩

theorem cdp_galois_le_two {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) :
    cdp ℓ Gal(Ksep/K) ≤ 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P, hP⟩ := exists_isProSylow (G := Gal(Ksep/K)) (p := ℓ)
  have : CompactSpace P := isCompact_iff_compactSpace.1 hP.1.isCompact
  rw [← cdp_eq_of_isProSylow hℓ hP]
  change cdp ℓ P ≤ ((2 : ℕ) : ℕ∞)
  rw [cdp_le_iff_of_isProPGroup hℓ hP.2.1 2]

  have hμ : Subsingleton (cohomology (Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)) 3) := by
    suffices h : ∀ x : cohomology (Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)) 3, x = 0 from
      ⟨fun x y => (h x).trans (h y).symm⟩
    intro x
    obtain ⟨U, hU, hPU, y, rfl⟩ := exists_cohomologyResLE_eq (galRootsOfUnity.{0} K Ksep ℓ) hP.1 3 x
    have := subsingleton_cohomology_three_rootsOfUnity K Ksep hℓK ⟨U, hU⟩
    rw [Subsingleton.elim y 0, map_zero]

  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity K Ksep hℓ hℓK
  have hfix : ∀ (σ : P) (x : Additive (rootsOfUnity ℓ Ksep)),
      (Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)).ρ σ x = x := by
    intro σ x
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    refine apply_eq_of_isProPGroup hℓ hP.2.1 σ.2 ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity ℓ _).1 (Additive.toMul x).2, Units.val_one]
  let ψ : Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ)) ⟶
      Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ) :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      (e.toAddMonoidHom.comp (AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).toAddMonoidHom),
      fun σ => LinearMap.ext fun x => (hfix σ _).symm⟩
  let ψ' : Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ) ⟶
      Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ)) :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      ((AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).symm.toAddMonoidHom.comp e.symm.toAddMonoidHom),
      fun σ => LinearMap.ext fun x => by
        change ULift.up (e.symm ((Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)).ρ σ x)) =
          ULift.up (e.symm x)
        rw [hfix]⟩
  have hcomp : ψ ≫ ψ' = 𝟙 _ := by
    ext x
    change e.symm (e x.down) = x.down
    exact e.symm_apply_apply x.down
  have hinj : Function.Injective (cohomologyMap ψ 3).hom := fun x y h => by
    have h' := congrArg (cohomologyMap ψ' 3).hom h
    rwa [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← cohomologyMap_comp, hcomp,
      cohomologyMap_id, ModuleCat.id_apply, ModuleCat.id_apply] at h'
  exact hinj.subsingleton

theorem subsingleton_cohomology_of_three_le {n : ℕ} (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (M : Rep (ULift.{0} ℤ) (U : Subgroup Gal(Ksep/K))) [IsDiscreteRep M] (hM : ∀ m : M, n • m = 0)
    {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology M r) := by
  have hn0 : n ≠ 0 := fun h0 => hn (by simp [h0])
  have htors : IsAddTorsion M := fun m =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn0, hM m⟩
  suffices h : ∀ x : cohomology M r, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  refine eq_zero_of_primaryComponent_eq_bot n hn0 (fun ℓ hℓ hℓn => ?_) x
    (nsmul_cohomology_eq_zero M hM r x)
  have hℓK : (ℓ : K) ≠ 0 := fun h0 => hn (by
    obtain ⟨c, hc⟩ := hℓn
    rw [hc, Nat.cast_mul, h0, zero_mul])
  refine primaryComponent_cohomology_eq_bot_of_cdp_lt (p := ℓ) M htors ?_
  calc cdp ℓ (U : Subgroup Gal(Ksep/K)) ≤ cdp ℓ Gal(Ksep/K) := cdp_openSubgroup_le ℓ U
    _ ≤ 2 := cdp_galois_le_two K Ksep hℓ hℓK
    _ < r := by exact_mod_cast (show 2 < r by omega)

end Sylow

end GroundTheory.ProfCoh
end
end
