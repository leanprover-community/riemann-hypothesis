import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealAbstract
import GroundTheory.ProfiniteCohomology.PoitouTate.BrauerInvZOfIsSepClosureCohomologyULiftIntAddEqu
import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityPlace
import GroundTheory.ProfiniteCohomology.PoitouTate.RealCup
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

section NormClassMap

variable {k F : Type} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [Fintype F]

theorem cohomologyMap_normClass {B B' : Rep k F} [IsDiscreteRep B] [IsDiscreteRep B'] (f : B ⟶ B')
    (m : B) : (cohomologyMap f 0).hom (normClass B m) = normClass B' (f.hom m) := by
  obtain ⟨z, hz, hiz⟩ := exists_normClass_cycle B m
  obtain ⟨z', hz', hiz'⟩ := exists_normClass_cycle B' (f.hom m)
  rw [hz, hz']
  change (HomologicalComplex.homologyMap (cochainsMap f) 0).hom _ = _
  rw [homologyMap_homologyπ_apply]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, hiz, hiz']
  apply cochainOf_injective
  funext σ
  change f.hom ((∑ g, B.ρ g) m) = (∑ g, B'.ρ g) (f.hom m)
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => Rep.hom_comm_apply f g m

end NormClassMap

section Abstract

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ψ : Gal(L/K) →ₜ* G)
  (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (ρ : Rep.res ψ.toMonoidHom D ⟶ galUnits.{0} K L)
  (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]

abbrev resEvalPair :
    Rep.res ψ.toMonoidHom M ⊗ Rep.res ψ.toMonoidHom (dualRep D M) ⟶ Rep.res ψ.toMonoidHom D :=
  (Rep.resFunctor ψ.toMonoidHom).map (evalPairing D M)

def dualToCartier :
    Rep.res ψ.toMonoidHom (dualRep D M) ⟶ cartierDual K L (Rep.res ψ.toMonoidHom M) :=
  resDualPost ψ.toMonoidHom D M _ ρ

omit [IsTopologicalGroup G] [IsDiscreteRep D] [IsDiscreteRep M] in
theorem bijective_dualToCartier {n : ℕ} [NeZero n] (hL : Nonempty (galRootsOfUnity.{0} K L n ≃+ ZMod n))
    (hD : Nonempty (D ≃+ ZMod n)) (hρ : Function.Injective ρ.hom) [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (dualToCartier ψ D ρ M).hom := by
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite (galRootsOfUnity.{0} K L n) := finite_of_nonempty_addEquiv hL
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep D (dualRep D M)) := finite_dualRep
  have : Finite (Rep.res ψ.toMonoidHom M) := inferInstanceAs (Finite M)
  have : Finite (dualRep (galRootsOfUnity.{0} K L n) (Rep.res ψ.toMonoidHom M)) := finite_dualRep
  set e := dualRepRootsOfUnityIso K L (Rep.res ψ.toMonoidHom M) n hM
  have he : Function.Injective e.inv.hom := fun a b hab => by
    have h := congrArg e.hom.hom hab
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, e.inv_hom_id] at h
  have : Finite (cartierDual K L (Rep.res ψ.toMonoidHom M)) := Finite.of_injective _ he
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · intro f f' hff'
    exact LinearMap.ext fun m => hρ (LinearMap.congr_fun hff' m)
  · calc _ ≤ Nat.card (dualRep (galRootsOfUnity.{0} K L n) (Rep.res ψ.toMonoidHom M)) :=
          Nat.card_le_card_of_injective _ he
      _ ≤ Nat.card M := card_dualRep_le hL
      _ ≤ Nat.card (dualRep D (dualRep D M)) :=
          Nat.card_le_card_of_injective _ (bijective_toDualDual hD hM).1
      _ ≤ Nat.card (dualRep D M) := card_dualRep_le hD

omit [IsTopologicalGroup G] [IsDiscreteRep D] [IsDiscreteRep M] in

theorem tensorHom_dualToCartier_cartierPairing :
    (𝟙 (Rep.res ψ.toMonoidHom M) ⊗ₘ dualToCartier ψ D ρ M) ≫
        cartierPairing K L (Rep.res ψ.toMonoidHom M) =
      resEvalPair ψ D M ≫ ρ := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cupPairing_dualToCartier [Finite M] [IsDiscreteRep (galUnits.{0} K L)]
    [IsDiscreteRep (cartierDual K L (Rep.res ψ.toMonoidHom M))] {r s : ℕ} (h : r + s = 2)
    (ξ : cohomology (Rep.res ψ.toMonoidHom M) r)
    (η : cohomology (Rep.res ψ.toMonoidHom (dualRep D M)) s) :
    cupPairing (cartierPairing K L (Rep.res ψ.toMonoidHom M)) h ξ
        ((cohomologyMap (dualToCartier ψ D ρ M) s).hom η) =
      (cohomologyMap ρ 2).hom (cupPairing (resEvalPair ψ D M) h ξ η) := by
  have hc := cupPairing_cohomologyMap (cartierPairing K L (Rep.res ψ.toMonoidHom M))
    (𝟙 _) (dualToCartier ψ D ρ M) h ξ η
  rw [cohomologyMap_id, ModuleCat.id_apply] at hc
  rw [hc, tensorHom_dualToCartier_cartierPairing, cohomologyMap_cupPairing]

section Order2

variable [FiniteDimensional K L] [IsGalois K L] (h2 : Module.finrank K L ≤ 2)
  (hN : ∀ a b : Kˣ, (a : K) ∉ Set.range (Algebra.norm K : L → K) →
    (b : K) ∉ Set.range (Algebra.norm K : L → K) →
      ((a * b : Kˣ) : K) ∈ Set.range (Algebra.norm K : L → K))
  {c : Gal(L/K)} (hG : ∀ g : Gal(L/K), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hneg : (-1 : K) ∉ Set.range (Algebra.norm K : L → K))
  (hconj : ∀ ζ : galUnits.{0} K L, (∃ k : ℕ, 0 < k ∧ k • ζ = 0) → (galUnits.{0} K L).ρ c ζ = -ζ)
  (hroots : ∀ k : ℕ, 0 < k → Nonempty (galRootsOfUnity.{0} K L k ≃+ ZMod k))
  [IsDiscreteRep (galUnits.{0} K L)] [Finite M]
  [IsDiscreteRep (cartierDual K L (Rep.res ψ.toMonoidHom M))]
  (inv : cohomology (Rep.res ψ.toMonoidHom D) 2 →+ QZ)
  (hinv : ∀ z, inv z = realInv K L h2 hN ((cohomologyMap ρ 2).hom z))

include hG hc hneg hconj hroots hinv in

theorem exists_orderTwo_pairing_zero {n : ℕ} [NeZero n] (hD : Nonempty (D ≃+ ZMod n))
    (hρ : Function.Injective ρ.hom) (hM : ∀ m : M, n • m = 0)
    (χ : cohomology (Rep.res ψ.toMonoidHom (dualRep D M)) 2 →+ QZ) :
    ∃ ξ : cohomology (Rep.res ψ.toMonoidHom M) 0, ∀ η,
      inv (cupPairing (resEvalPair ψ D M) (show 0 + 2 = 2 from rfl) ξ η) = χ η := by
  have hf := bijective_dualToCartier ψ D ρ M (hroots n (Nat.pos_of_ne_zero (NeZero.ne n))) hD hρ hM
  let e := cohomologyAddEquivOfIso (Rep.isoOfBijective _ hf) 2
  obtain ⟨x, hx⟩ := (real_local_duality_of_orderTwo h2 hN hG hc hneg hconj hroots
    (Rep.res ψ.toMonoidHom M)).1.1.2 (χ.comp e.symm.toAddMonoidHom)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨x, fun η => ?_⟩
  have e1 := DFunLike.congr_fun hx (e η)
  rw [realDualityPairingZeroTwo_mk, realDualityPairing_apply] at e1
  rw [hinv, ← cupPairing_dualToCartier]
  refine e1.trans ?_
  change χ (e.symm (e η)) = χ η
  rw [AddEquiv.symm_apply_apply]

include hG hc hneg hconj hroots hinv in

theorem exists_orderTwo_pairing_two {n : ℕ} [NeZero n] (hD : Nonempty (D ≃+ ZMod n))
    (hρ : Function.Injective ρ.hom) (hM : ∀ m : M, n • m = 0)
    (χ : cohomology (Rep.res ψ.toMonoidHom (dualRep D M)) 0 →+ QZ)
    (hχ : ∀ x ∈ normClasses (Rep.res ψ.toMonoidHom (dualRep D M)), χ x = 0) :
    ∃ ξ : cohomology (Rep.res ψ.toMonoidHom M) 2, ∀ η,
      inv (cupPairing (resEvalPair ψ D M) (show 2 + 0 = 2 from rfl) ξ η) = χ η := by
  set f := dualToCartier ψ D ρ M
  have hf := bijective_dualToCartier ψ D ρ M (hroots n (Nat.pos_of_ne_zero (NeZero.ne n))) hD hρ hM
  let e := cohomologyAddEquivOfIso (Rep.isoOfBijective f hf) 0
  let χ' := χ.comp e.symm.toAddMonoidHom
  have hχ' : ∀ y ∈ normClasses (cartierDual K L (Rep.res ψ.toMonoidHom M)), χ' y = 0 := fun y hy => by
    obtain ⟨m', rfl⟩ := exists_normClass_eq_of_mem _ y hy
    obtain ⟨m, rfl⟩ := hf.2 m'
    have hem : e (normClass _ m) = normClass _ (f.hom m) := by
      rw [cohomologyAddEquivOfIso_apply]
      exact cohomologyMap_normClass f m
    rw [← hem]
    change χ (e.symm (e (normClass _ m))) = 0
    rw [AddEquiv.symm_apply_apply]
    exact hχ _ (normClass_mem_normClasses _ m)
  obtain ⟨ξ, hξ⟩ := (real_local_duality_of_orderTwo h2 hN hG hc hneg hconj hroots
    (Rep.res ψ.toMonoidHom M)).2.2.1.2 (QuotientAddGroup.lift _ χ' hχ')
  refine ⟨ξ, fun η => ?_⟩
  have e1 := DFunLike.congr_fun hξ (Submodule.Quotient.mk (e η))
  rw [realDualityPairingTwoZero_mk, realDualityPairing_apply] at e1
  rw [hinv, ← cupPairing_dualToCartier]
  refine e1.trans ?_
  change χ (e.symm (e η)) = χ η
  rw [AddEquiv.symm_apply_apply]

end Order2

end Abstract

section GS

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (n : ℕ)

def gsRealRootsToUnits (w : {v : InfinitePlace K.1 // v.IsReal}) :
    Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S n) ⟶
      galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion) :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)))
      (B := Additive (AlgebraicClosure w.1.Completion)ˣ)
      (MonoidHom.toAdditive
        ((Units.map ((ιr w).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom.toMonoidHom).comp
          (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)).subtype)),
    fun σ => LinearMap.ext fun (ζ : Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) =>
      congrArg Additive.ofMul
        (Units.ext (gsRealFamily_apply S ιr w σ
          (((Additive.toMul ζ : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
            maxUnramifiedOutside K.1 ℚ̄ S)))⟩

theorem gsRealRootsToUnits_injective (w : {v : InfinitePlace K.1 // v.IsReal}) :
    Function.Injective (gsRealRootsToUnits S ιr n w).hom := by
  intro a b hab
  have h := congrArg (fun x => ((Additive.toMul x : (AlgebraicClosure w.1.Completion)ˣ) :
    AlgebraicClosure w.1.Completion)) hab
  change ιr w _ = ιr w _ at h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact (ιr w).toRingHom.injective h

def gsRealInvRootsQZ (w : {v : InfinitePlace K.1 // v.IsReal}) :
    cohomology (Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S n)) 2 →+ QZ :=
  (realInv w.1.Completion (AlgebraicClosure w.1.Completion) (infAlgClosure_finrank_le_two w.1)
    (infAlgClosure_mul_mem_range_norm w.1)).comp
      (cohomologyMap (gsRealRootsToUnits S ιr n w) 2).hom.toAddMonoidHom

theorem gsRealInvRootsQZ_apply (w : {v : InfinitePlace K.1 // v.IsReal})
    (z : cohomology (Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S n)) 2) :
    gsRealInvRootsQZ S ιr n w z =
      realInv w.1.Completion (AlgebraicClosure w.1.Completion) (infAlgClosure_finrank_le_two w.1)
        (infAlgClosure_mul_mem_range_norm w.1) ((cohomologyMap (gsRealRootsToUnits S ιr n w) 2).hom z) :=
  rfl

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]

variable [NeZero n] (hD : Nonempty (gsRoots S n ≃+ ZMod n)) (hM : ∀ m : M, n • m = 0)

set_option maxHeartbeats 400000 in
include hD hM in

theorem surjective_gsRealPairing_zero (w : {v : InfinitePlace K.1 // v.IsReal}) :
    Function.Surjective
      (ptLocalPairing (gsRealFamily S ιr) (gsRoots S n) M (gsRealInvRootsQZ S ιr n) w
        (show 0 + 2 = 2 from rfl)) := fun χ => by
  have : IsDiscreteRep (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) :=
    isDiscreteRep_galUnits
  have : IsDiscreteRep (cartierDual w.1.Completion (AlgebraicClosure w.1.Completion)
      (Rep.res (gsRealFamily S ιr w).toMonoidHom M)) := isDiscreteRep_cartierDual _
  have key := exists_orderTwo_pairing_zero (gsRealFamily S ιr w) (gsRoots S n)
    (gsRealRootsToUnits S ιr n w) M ?h2 ?hN (c := realConj w.1 w.2) ?hG ?hc ?hneg ?hconj ?hroots
    (gsRealInvRootsQZ S ιr n w) ?hinv hD ?hρ hM χ
  case h2 => exact infAlgClosure_finrank_le_two w.1
  case hN => exact infAlgClosure_mul_mem_range_norm w.1
  case hG => exact eq_one_or_eq_realConj w.1 w.2
  case hc => exact realConj_ne_one w.1 w.2
  case hneg => exact neg_one_not_mem_range_norm_infAlgClosure w.1 w.2
  case hconj => exact realConj_galUnits_of_torsion w.1 w.2
  case hroots => exact nonempty_addEquiv_galRootsOfUnity_infAlgClosure w.1
  case hinv => exact gsRealInvRootsQZ_apply S ιr n w
  case hρ => exact gsRealRootsToUnits_injective S ιr n w
  obtain ⟨ξ, hξ⟩ := key
  exact ⟨ξ, AddMonoidHom.ext fun η => (ptLocalPairing_apply _ _ _ _ _ _ _ _).trans (hξ η)⟩

set_option maxHeartbeats 400000 in
include hD hM in

theorem exists_gsRealPairing_two (w : {v : InfinitePlace K.1 // v.IsReal})
    (χ : cohomology (Rep.res (gsRealFamily S ιr w).toMonoidHom (dualRep (gsRoots S n) M)) 0 →+ QZ)
    (hχ : ∀ x ∈ normClasses (Rep.res (gsRealFamily S ιr w).toMonoidHom (dualRep (gsRoots S n) M)),
      χ x = 0) :
    ∃ ξ, ptLocalPairing (gsRealFamily S ιr) (gsRoots S n) M (gsRealInvRootsQZ S ιr n) w
      (show 2 + 0 = 2 from rfl) ξ = χ := by
  have : IsDiscreteRep (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) :=
    isDiscreteRep_galUnits
  have : IsDiscreteRep (cartierDual w.1.Completion (AlgebraicClosure w.1.Completion)
      (Rep.res (gsRealFamily S ιr w).toMonoidHom M)) := isDiscreteRep_cartierDual _
  have key := exists_orderTwo_pairing_two (gsRealFamily S ιr w) (gsRoots S n)
    (gsRealRootsToUnits S ιr n w) M ?h2 ?hN (c := realConj w.1 w.2) ?hG ?hc ?hneg ?hconj ?hroots
    (gsRealInvRootsQZ S ιr n w) ?hinv hD ?hρ hM χ hχ
  case h2 => exact infAlgClosure_finrank_le_two w.1
  case hN => exact infAlgClosure_mul_mem_range_norm w.1
  case hG => exact eq_one_or_eq_realConj w.1 w.2
  case hc => exact realConj_ne_one w.1 w.2
  case hneg => exact neg_one_not_mem_range_norm_infAlgClosure w.1 w.2
  case hconj => exact realConj_galUnits_of_torsion w.1 w.2
  case hroots => exact nonempty_addEquiv_galRootsOfUnity_infAlgClosure w.1
  case hinv => exact gsRealInvRootsQZ_apply S ιr n w
  case hρ => exact gsRealRootsToUnits_injective S ιr n w
  obtain ⟨ξ, hξ⟩ := key
  exact ⟨ξ, AddMonoidHom.ext fun η => (ptLocalPairing_apply _ _ _ _ _ _ _ _).trans (hξ η)⟩

end GS

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory CategoryTheory.Limits MonoidalCategory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section OrderTwoOdd

variable {F : Type} [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [Fintype F] {n : ℕ}
  (hn : Odd n) (B : Rep.{0} (ULift.{0} ℤ) F) [IsDiscreteRep B] (hB : ∀ b : B, n • b = 0)

include hn hB in

theorem isZero_cohomology_of_card_two_of_odd [CompactSpace F] [TotallyDisconnectedSpace F]
    (hcard : Fintype.card F = 2) (m : ℕ) : IsZero (cohomology B (m + 1)) := by
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  have hz : ∀ x : cohomology B (m + 1), x = 0 := by
    intro x
    have hnx : n • x = 0 := nsmul_cohomology_eq_zero B hB (m + 1) x
    obtain ⟨U, hU⟩ := exists_card_smul_eq_zero B (Nat.succ_ne_zero m) x
    have hdvd : Nat.card (F ⧸ (U : Subgroup F)) ∣ 2 := by
      rw [← hcard, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_quotient_dvd_card _
    obtain ⟨d, hd⟩ := hdvd
    have h2x : 2 • x = 0 := by rw [hd, mul_comm, mul_nsmul', hU, nsmul_zero]
    obtain ⟨k, rfl⟩ := hn
    calc x = (2 * k + 1) • x - (k * 2) • x := by
          rw [mul_comm k 2, add_nsmul, one_nsmul, add_sub_cancel_left]
      _ = 0 := by rw [hnx, mul_nsmul', h2x, nsmul_zero, sub_zero]
  rw [hz x, hz y]

omit [TopologicalSpace F] [IsTopologicalGroup F] [IsDiscreteRep B] in
include hn hB in

theorem exists_norm_of_orderTwo_of_odd {c : F} (hG : ∀ g : F, g = 1 ∨ g = c) (hc : c ≠ 1) :
    ∀ x ∈ B.ρ.invariants, ∃ m, B.ρ.norm m = x := by
  intro x hx
  obtain ⟨k, hk⟩ := hn
  refine ⟨(k + 1) • x, ?_⟩
  rw [OrderTwo.norm_apply B hG hc, map_nsmul, hx c, ← add_nsmul]
  have h : k + 1 + (k + 1) = n + 1 := by omega
  rw [h, add_nsmul, one_nsmul, hB, zero_add]

end OrderTwoOdd

section Local

variable {n : ℕ} (hn : Odd n) (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep A]
  (hA : ∀ a : A, n • a = 0)

include hn hA in

theorem isZero_cohomology_gsReal_of_odd (w : {v : InfinitePlace K.1 // v.IsReal}) (m : ℕ) :
    IsZero (cohomology (Rep.res (gsRealFamily S ιr w).toMonoidHom A) (m + 1)) := by
  have key := isZero_cohomology_of_card_two_of_odd hn (Rep.res (gsRealFamily S ιr w).toMonoidHom A) hA
    ?hcard m
  case hcard => exact card_realGal_eq_two w.1 w.2
  exact key

omit [IsDiscreteRep A] in
include hn hA in

theorem exists_norm_gsReal_of_odd (w : {v : InfinitePlace K.1 // v.IsReal}) :
    ∀ x ∈ (Rep.res (gsRealFamily S ιr w).toMonoidHom A).ρ.invariants,
      ∃ m, (Rep.res (gsRealFamily S ιr w).toMonoidHom A).ρ.norm m = x := by
  have key := exists_norm_of_orderTwo_of_odd hn (Rep.res (gsRealFamily S ιr w).toMonoidHom A) hA
    (c := realConj w.1 w.2) ?hG ?hc
  case hG => exact eq_one_or_eq_realConj w.1 w.2
  case hc => exact realConj_ne_one w.1 w.2
  exact key

include hn hA in

theorem bijective_tateForget_gs_of_odd (m : ℕ) :
    Function.Bijective (tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) A
      (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom A) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom A) (fun _ => 𝟙 _) (m + 1)).hom := by
  have := isIso_tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) A
    (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom A) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom A) (fun _ => 𝟙 _)
    (fun w m => isZero_cohomology_gsReal_of_odd S ιr hn A hA w m)
    (fun w => exists_norm_gsReal_of_odd S ιr hn A hA w) m
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

include hn hA in

theorem bijective_tateForget_gs_of_odd' {m : ℕ} (hm : 1 ≤ m) :
    Function.Bijective (tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) A
      (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom A) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom A) (fun _ => 𝟙 _) m).hom := by
  cases m with
  | zero => exact absurd hm (by norm_num)
  | succ m => exact bijective_tateForget_gs_of_odd S ιr ιs hn A hA m

end Local

section Hypotheses

noncomputable instance fintypeRealPlaces (K : FiniteSubfield) : Fintype {v : InfinitePlace K.1 // v.IsReal} :=
  Fintype.ofFinite _

theorem injective_resZero {G H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →ₜ* G)
    (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] :
    Function.Injective (cohomologyMapAlong φ.toMonoidHom (continuous_toMonoidHom φ)
      (𝟙 (Rep.res φ.toMonoidHom M)) 0).hom := by
  intro x y h
  have ex := H0Iso_hom_cohomologyMapAlong φ.toMonoidHom (continuous_toMonoidHom φ) (𝟙 _) x
  have ey := H0Iso_hom_cohomologyMapAlong φ.toMonoidHom (continuous_toMonoidHom φ) (𝟙 _) y
  rw [h] at ex
  have hxy' : (H0Iso M).hom.hom x = (H0Iso M).hom.hom y := Subtype.ext (ex.symm.trans ey)
  calc x = (H0Iso M).inv.hom ((H0Iso M).hom.hom x) :=
        (hom_apply_hom_apply_of_comp_eq (H0Iso M).hom_inv_id x).symm
    _ = (H0Iso M).inv.hom ((H0Iso M).hom.hom y) := by rw [hxy']
    _ = y := hom_apply_hom_apply_of_comp_eq (H0Iso M).hom_inv_id y

theorem injective_ptRes_zero_gs [Nonempty S] (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] : Function.Injective fun (x : cohomology M 0) v => ptRes (gsFinFamily S ιs) M v 0 x :=
  fun x y hxy => (‹Nonempty S›.elim fun v =>
    injective_resZero (gsFinFamily S ιs v) M (congrFun hxy v))

variable [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hodd : Odd N)

def gsOddTrace : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N :=
  (gsCompactInv S ιs N (Or.inl hodd) (subsingleton_cohomology_three_gsRoots S hS (Or.inl hodd))).comp
    (tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _) 3).hom.toAddMonoidHom

omit [Fintype S] [NeZero N] in
include hodd in

theorem gsReal_two_eq_zero_of_odd (w : {v : InfinitePlace K.1 // v.IsReal})
    (x : cohomology (Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S N)) 2) : x = 0 :=
  (ModuleCat.subsingleton_of_isZero
    (isZero_cohomology_gsReal_of_odd S ιr hodd (gsRoots S N) (nsmul_gsRoots S N) w 1)).elim _ _

theorem gsOddTrace_apply (z : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3) :
    gsOddTrace S ιr ιs hS hodd z =
      gsCompactInv S ιs N (Or.inl hodd) (subsingleton_cohomology_three_gsRoots S hS (Or.inl hodd))
        ((tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
          (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _)
          (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _) 3).hom z) :=
  rfl

set_option maxHeartbeats 1000000 in

theorem gsOddTrace_localToCompact
    (ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2) :
    zmodToQZ N (gsOddTrace S ιr ιs hS hodd ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr)
      (gsRoots S N) 2).hom ξ)) =
      ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w) := by
  have h1 : (tateForget (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _) 3).hom
        ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ) =
      (localToCompact (gsFinFamily S ιs) (gsRoots S N) _ (fun _ => 𝟙 _) 2).hom ξ.1 :=
    congrArg (fun f => f.hom ξ) (tateLocalToCompact_tateForget (gsFinFamily S ιs) (gsRealFamily S ιr)
      (gsRoots S N) (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (gsRoots S N)) (fun _ => 𝟙 _) 2)
  have h2 : ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w) = 0 :=
    Finset.sum_eq_zero fun w _ =>
      (congrArg (gsRealInvRootsQZ S ιr N w) (gsReal_two_eq_zero_of_odd S ιr hodd w (ξ.2 w))).trans (map_zero _)
  calc zmodToQZ N (gsOddTrace S ιr ιs hS hodd ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr)
        (gsRoots S N) 2).hom ξ))
      = ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) :=
        (congrArg (zmodToQZ N) ((gsOddTrace_apply S ιr ιs hS hodd _).trans (congrArg _ h1))).trans
          (zmodToQZ_gsCompactInv_localToCompact S ιs (Or.inl hodd) _ ξ.1)
    _ = ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + 0 := (add_zero _).symm
    _ = _ := congrArg (∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ·) h2.symm

set_option maxHeartbeats 1000000 in
include hS in

theorem bijective_tateCompactDualityMap_gs_of_odd (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) h
      (gsOddTrace S ιr ιs hS hodd) M) := by
  have hf := bijective_tateForget_gs_of_odd' S ιr ιs hodd (dualRep (gsRoots S N) M)
    (nsmul_dualRep_eq_zero (nsmul_gsRoots S N)) hs
  have hγ := poitouTate_duality_gs S ιs hS (Or.inl hodd) M hM h
  refine bijective_of_bijective_precomp _ _ (AddEquiv.ofBijective _ hf) (fun x y => ?_) hγ
  exact (gsOddTrace_apply S ιr ιs hS hodd _).trans (congrArg _ (tateForget_tateCompactCupRes
    (gsFinFamily S ιs) (gsRealFamily S ιr) (dualEvalPairing (gsRoots S N) M) _ y x))

include hS hodd in

theorem gsOddTatePoitouTateHypotheses [Nonempty S] :
    TatePoitouTateHypotheses (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (gsOddTrace S ιr ιs hS hodd) (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) := by
  have hD := nonempty_addEquiv_gsRoots_of_mem S hS
  exact
    { nonempty_addEquiv := hD
      duality := @fun M _ _ hM r s h hs => bijective_tateCompactDualityMap_gs_of_odd S ιr ιs hS hodd M hM h hs
      finite_cohomology := fun M _ _ hM r hr =>
        finite_cohomology_gs K S M (fun v hv => hS v (natCast_mem_of_natCard_mem v.isPrime hM hv)) r hr
      localToCompact_two := gsOddTrace_localToCompact S ιr ιs hS hodd
      injective_res_zero := fun M _ => injective_ptRes_zero_gs S ιs M
      surjective_localPairing_zero := fun M _ _ hM v => (bijective_gsLocalPairing S ιs N hD M hM v _).2
      surjective_localPairing_two := fun M _ _ hM v => (bijective_gsLocalPairing S ιs N hD M hM v _).2
      surjective_realPairing_zero := fun M _ _ hM w => surjective_gsRealPairing_zero S ιr N M hD hM w
      surjective_realPairing_two := fun M _ _ hM w χ hχ => exists_gsRealPairing_two S ιr N M hD hM w χ hχ }

end Hypotheses

end GroundTheory.ProfCoh
end
end
