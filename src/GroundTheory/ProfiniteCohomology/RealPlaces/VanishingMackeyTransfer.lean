import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyPlaces
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingUnitsDiv

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section Kummer

abbrev finKummer (v : S) :=
  localKummerSeq S (gsFinFamily S ιs v).toMonoidHom
    ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιs v))

abbrev realKummer (w : {v : InfinitePlace K.1 // v.IsReal}) :=
  localKummerSeq S (gsRealFamily S ιr w).toMonoidHom
    ((ιr w).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιr w))

abbrev finKummerMap (v : S) :=
  kummerLocalMap S (gsFinFamily S ιs v).toMonoidHom
    ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιs v))

abbrev realKummerMap (w : {v : InfinitePlace K.1 // v.IsReal}) :=
  kummerLocalMap S (gsRealFamily S ιr w).toMonoidHom
    ((ιr w).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιr w))

instance (v : S) : IsDiscreteRep (finKummer S ιs v).X₁ :=
  IsDiscreteRep.res (continuous_toMonoidHom (gsFinFamily S ιs v)) _

instance (v : S) : IsDiscreteRep (finKummer S ιs v).X₂ := isDiscreteRep_finUnits S v

instance (v : S) : IsDiscreteRep (finKummer S ιs v).X₃ := isDiscreteRep_finUnits S v

instance (w : {v : InfinitePlace K.1 // v.IsReal}) : IsDiscreteRep (realKummer S ιr w).X₁ :=
  IsDiscreteRep.res (continuous_toMonoidHom (gsRealFamily S ιr w)) _

instance (w : {v : InfinitePlace K.1 // v.IsReal}) : IsDiscreteRep (realKummer S ιr w).X₂ :=
  isDiscreteRep_realUnits w

instance (w : {v : InfinitePlace K.1 // v.IsReal}) : IsDiscreteRep (realKummer S ιr w).X₃ :=
  isDiscreteRep_realUnits w

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include h2S in

theorem kummerSeq_shortExact :
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2).ShortExact :=
  sUnitsKummerSequence_shortExact (Ω := ℚ̄) S 2 (fun v hv h => hv (h2S v h))

def kummerF (n : ℕ) :
    gsTateCompactCohomology S ιr ιs (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) n →+
      unitsTateCohomology S ιr ιs n :=
  (tateCompactCohomologyMap₁₂ (gsFinFamily S ιs) (gsRealFamily S ιr)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2) (finKummer S ιs) (finKummerMap S ιs)
    (realKummer S ιr) (realKummerMap S ιr) n).hom.toAddMonoidHom

def kummerG (n : ℕ) : unitsTateCohomology S ιr ιs n →+ unitsTateCohomology S ιr ιs n :=
  (tateCompactCohomologyMap₂₃ (gsFinFamily S ιs) (gsRealFamily S ιr)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2) (finKummer S ιs) (finKummerMap S ιs)
    (realKummer S ιr) (realKummerMap S ιr) n).hom.toAddMonoidHom

def kummerδ (n : ℕ) : unitsTateCohomology S ιr ιs n →+
    gsTateCompactCohomology S ιr ιs (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) (n + 1) :=
  (tateCompactδ (gsFinFamily S ιs) (gsRealFamily S ιr) (finKummerMap S ιs) (realKummerMap S ιr)
    (kummerSeq_shortExact S h2S) (fun _ => localKummerSeq_shortExact _ _ _ _)
    (fun _ => localKummerSeq_shortExact _ _ _ _) n).hom.toAddMonoidHom

set_option maxHeartbeats 1000000 in

theorem kummerG_apply (n : ℕ) (y : unitsTateCohomology S ιr ιs n) : kummerG S ιr ιs n y = 2 • y := by
  have h : tateCompactCohomologyMap₂₃ (gsFinFamily S ιs) (gsRealFamily S ιr)
      (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2) (finKummer S ιs) (finKummerMap S ιs)
      (realKummer S ιr) (realKummerMap S ιr) n = 2 • 𝟙 _ :=
    tateCompactCohomologyMap_nsmul_id (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S)
      (finUnits S) (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) 2 n _ _
  exact congrArg (fun f => f.hom y) h

set_option maxHeartbeats 1000000 in

theorem kummerG_kummerF (n : ℕ)
    (x : gsTateCompactCohomology S ιr ιs (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) n) :
    kummerG S ιr ιs n (kummerF S ιr ιs n x) = 0 :=
  hom_apply_hom_apply_of_comp_eq (tateCompactCohomologyMap_f_g (gsFinFamily S ιs) (gsRealFamily S ιr)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2) (finKummer S ιs) (finKummerMap S ιs)
    (realKummer S ιr) (realKummerMap S ιr) n) x

set_option maxHeartbeats 1000000 in

theorem exists_kummerδ_eq (n : ℕ)
    (x : gsTateCompactCohomology S ιr ιs (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) (n + 1))
    (hx : kummerF S ιr ιs (n + 1) x = 0) : ∃ y, kummerδ S ιr ιs h2S n y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (tateCompactCohomology_exact₁ (gsFinFamily S ιs) (gsRealFamily S ιr)
    (finKummerMap S ιs) (realKummerMap S ιr) (kummerSeq_shortExact S h2S)
    (fun _ => localKummerSeq_shortExact _ _ _ _) (fun _ => localKummerSeq_shortExact _ _ _ _) n) x hx

set_option maxHeartbeats 1000000 in

theorem kummerδ_kummerG (n : ℕ) (y : unitsTateCohomology S ιr ιs n) :
    kummerδ S ιr ιs h2S n (kummerG S ιr ιs n y) = 0 :=
  hom_apply_hom_apply_of_comp_eq (tateCompactCohomologyMap₂₃_tateCompactδ (gsFinFamily S ιs)
    (gsRealFamily S ιr) (finKummerMap S ιs) (realKummerMap S ιr) (kummerSeq_shortExact S h2S)
    (fun _ => localKummerSeq_shortExact _ _ _ _) (fun _ => localKummerSeq_shortExact _ _ _ _) n) y

end Kummer

section Main

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include h2S in

theorem gsTateCompactCohomology_rootsOfUnity_two_eq_zero {r : ℕ} (hr : 4 ≤ r)
    (x : gsTateCompactCohomology S ιr ιs (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) r) :
    x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hf : kummerF S ιr ιs (n + 1) x = 0 := by
    refine eq_zero_unitsTateCohomology_of_two_pow_nsmul S ιr ιs h2S hr _ (k := 1) ?_
    rw [pow_one, ← kummerG_apply]
    exact kummerG_kummerF S ιr ιs (n + 1) x
  obtain ⟨y, rfl⟩ := exists_kummerδ_eq S ιr ιs h2S n x hf
  obtain ⟨y', rfl⟩ := exists_two_nsmul_unitsTateCohomology S ιr ιs h2S (by omega) y
  rw [← kummerG_apply]
  exact kummerδ_kummerG S ιr ιs h2S n y'

end Main

section ZModTwo

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

instance isDiscreteRep_zmodRep_two_gs : IsDiscreteRep (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) :=
  isDiscreteRep_of_isTrivial _

theorem galRootsOfUnity_two_ρ_apply (σ : galUnramifiedOutside K.1 ℚ̄ S)
    (x : Additive (rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S))) :
    (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2).ρ σ x = x := by
  rw [galRootsOfUnity_ρ_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change σ (((Additive.toMul x : rootsOfUnity 2 _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    maxUnramifiedOutside K.1 ℚ̄ S) = (((Additive.toMul x : rootsOfUnity 2 _) :
      (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S)
  have hx : (((Additive.toMul x : rootsOfUnity 2 _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
      maxUnramifiedOutside K.1 ℚ̄ S) * (((Additive.toMul x : rootsOfUnity 2 _) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) = 1 := by
    rw [← Units.val_mul, ← pow_two, (mem_rootsOfUnity 2 _).1 (Additive.toMul x).2, Units.val_one]
  rcases mul_self_eq_one_iff.1 hx with h | h <;> rw [h]
  · exact map_one σ
  · rw [map_neg, map_one]

include h2S in

theorem nonempty_rootsOfUnity_two_iso_zmodRep :
    Nonempty (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2 ≅
      zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) := by
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity_gs K S Nat.prime_two h2S
  exact ⟨Rep.mkIso (Representation.Equiv.mk (uliftIntLinearEquiv.{0} (e.symm.trans AddEquiv.ulift.symm))
    fun σ => LinearMap.ext fun x => by
      change (uliftIntLinearEquiv.{0} (e.symm.trans AddEquiv.ulift.symm))
        ((galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2).ρ σ x) =
          (uliftIntLinearEquiv.{0} (e.symm.trans AddEquiv.ulift.symm)) x
      rw [galRootsOfUnity_two_ρ_apply])⟩

include h2S in

theorem gsTateCompactCohomology_zmodRep_two_eq_zero {r : ℕ} (hr : 4 ≤ r)
    (x : gsTateCompactCohomology S ιr ιs (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) r) : x = 0 := by
  obtain ⟨e⟩ := nonempty_rootsOfUnity_two_iso_zmodRep S h2S
  exact eq_zero_tateCompactCohomologyRes_of_retract (gsFinFamily S ιs) (gsRealFamily S ιr) e.inv e.hom
    e.inv_hom_id r (gsTateCompactCohomology_rootsOfUnity_two_eq_zero S ιr ιs h2S hr) x

instance isDiscreteRep_res_zmodRep_two_fin (v : S) :
    IsDiscreteRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) :=
  isDiscreteRep_res_toMonoidHom _ _

theorem subsingleton_finLocal_zmodRep_two (v : S) {n : ℕ} (hn : 3 ≤ n) :
    Subsingleton (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
      (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) n) := by
  refine subsingleton_cohomology_of_cdp_le_two two_ne_zero (fun ℓ hℓ _ => ?_) _
    (fun m => nsmul_zmodRep_eq_zero _ 2 m) hn
  refine cdp_galois_le_two _ _ hℓ ?_
  exact_mod_cast hℓ.ne_zero

def someFinEmbeddings : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) :=
  fun _ => Classical.choice nonempty_algHom_of_isSepClosed

set_option maxHeartbeats 1000000 in
include h2S in

theorem injective_gsRealRes_zmodRep_two_succ {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (gsRealRes S ιr (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) (n + 1)).hom :=
  (injective_tateGlobalToLocal_iff (gsFinFamily S (someFinEmbeddings S)) (gsRealFamily S ιr)
    (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)
    (fun v => Rep.res (gsFinFamily S (someFinEmbeddings S) v).toMonoidHom
      (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2))
    (fun _ => 𝟙 _) (n + 1)
    (fun v => subsingleton_finLocal_zmodRep_two S (someFinEmbeddings S) v (by omega))).1
    (injective_tateGlobalToLocal_of_eq_zero (gsFinFamily S (someFinEmbeddings S)) (gsRealFamily S ιr)
      (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)
      (fun v => Rep.res (gsFinFamily S (someFinEmbeddings S) v).toMonoidHom
        (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2))
      (fun _ => 𝟙 _) n
      (gsTateCompactCohomology_zmodRep_two_eq_zero S ιr (someFinEmbeddings S) h2S (by omega)))

set_option maxHeartbeats 1000000 in
include h2S in

theorem surjective_gsRealRes_zmodRep_two_succ {n : ℕ} (hn : 2 ≤ n) :
    Function.Surjective (gsRealRes S ιr (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) (n + 1)).hom :=
  (surjective_tateGlobalToLocal_iff (gsFinFamily S (someFinEmbeddings S)) (gsRealFamily S ιr)
    (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)
    (fun v => Rep.res (gsFinFamily S (someFinEmbeddings S) v).toMonoidHom
      (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2))
    (fun _ => 𝟙 _) (n + 1)
    (fun v => subsingleton_finLocal_zmodRep_two S (someFinEmbeddings S) v (by omega))).1
    (surjective_tateGlobalToLocal_of_eq_zero (gsFinFamily S (someFinEmbeddings S)) (gsRealFamily S ιr)
      (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)
      (fun v => Rep.res (gsFinFamily S (someFinEmbeddings S) v).toMonoidHom
        (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2)) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2))
      (fun _ => 𝟙 _) n
      (gsTateCompactCohomology_zmodRep_two_eq_zero S ιr (someFinEmbeddings S) h2S (by omega)))

set_option maxHeartbeats 4000000 in
include h2S in

theorem injective_gsRealRes_zmodRep_two {r : ℕ} (hr : 4 ≤ r) :
    Function.Injective (gsRealRes S ιr (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) r).hom := by
  cases r with
  | zero => omega
  | succ n => exact injective_gsRealRes_zmodRep_two_succ S ιr h2S (by omega)

set_option maxHeartbeats 4000000 in
include h2S in

theorem surjective_gsRealRes_zmodRep_two {r : ℕ} (hr : 3 ≤ r) :
    Function.Surjective (gsRealRes S ιr (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) 2) r).hom := by
  cases r with
  | zero => omega
  | succ n => exact surjective_gsRealRes_zmodRep_two_succ S ιr h2S (by omega)

end ZModTwo

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

section GalConj

variable {Kv Ew Ωv ΩE : Type*} [Field Kv] [Field Ew] [Field Ωv] [Field ΩE] [Algebra Kv Ew] [Algebra Kv Ωv]
  [Algebra Ew Ωv] [IsScalarTower Kv Ew Ωv] [Algebra Ew ΩE] (θ : ΩE ≃ₐ[Ew] Ωv)
  (hfix : ∀ (σ : Ωv ≃ₐ[Kv] Ωv) (y : Ew), σ (algebraMap Ew Ωv y) = algebraMap Ew Ωv y)

theorem conj_algebraMap_eq (τ : ΩE ≃ₐ[Ew] ΩE) (a : Kv) :
    θ (τ (θ.symm (algebraMap Kv Ωv a))) = algebraMap Kv Ωv a := by
  have h1 : algebraMap Kv Ωv a = θ (algebraMap Ew ΩE (algebraMap Kv Ew a)) :=
    (IsScalarTower.algebraMap_apply Kv Ew Ωv a).trans (θ.commutes _).symm
  calc θ (τ (θ.symm (algebraMap Kv Ωv a))) = θ (τ (θ.symm (θ (algebraMap Ew ΩE (algebraMap Kv Ew a))))) :=
        congrArg (fun t => θ (τ (θ.symm t))) h1
    _ = θ (τ (algebraMap Ew ΩE (algebraMap Kv Ew a))) := congrArg (fun t => θ (τ t)) (θ.symm_apply_apply _)
    _ = θ (algebraMap Ew ΩE (algebraMap Kv Ew a)) := congrArg θ (τ.commutes _)
    _ = algebraMap Kv Ωv a := h1.symm

def galConjEquiv : (Ωv ≃ₐ[Kv] Ωv) ≃* (ΩE ≃ₐ[Ew] ΩE) where
  toFun σ := (θ.trans (AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (hfix σ))).trans θ.symm
  invFun τ := AlgEquiv.ofRingEquiv (f := θ.symm.toRingEquiv.trans (τ.toRingEquiv.trans θ.toRingEquiv))
    (conj_algebraMap_eq θ τ)
  left_inv σ := AlgEquiv.ext fun y => by
    change θ (θ.symm (σ (θ (θ.symm y)))) = σ y
    rw [θ.apply_symm_apply, θ.apply_symm_apply]
  right_inv τ := AlgEquiv.ext fun y => by
    change θ.symm (θ (τ (θ.symm (θ y)))) = τ y
    rw [θ.symm_apply_apply, θ.symm_apply_apply]
  map_mul' σ τ := AlgEquiv.ext fun y => by
    change θ.symm (σ (τ (θ y))) = θ.symm (σ (θ (θ.symm (τ (θ y)))))
    rw [θ.apply_symm_apply]

theorem galConjEquiv_apply (σ : Ωv ≃ₐ[Kv] Ωv) (y : ΩE) : galConjEquiv θ hfix σ y = θ.symm (σ (θ y)) :=
  rfl

end GalConj

section Data

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

set_option maxHeartbeats 1000000 in

theorem exists_real_data (v : {v : InfinitePlace K.1 // v.IsReal}) (x : galUnramifiedOutside K.1 ℚ̄ S)
    (hreal : (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).IsReal) :
    ∃ (ιw : ℚ̄ →ₐ[L.1] AlgebraicClosure
        (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion)
      (e : Gal(AlgebraicClosure v.1.Completion / v.1.Completion) ≃*
        Gal(AlgebraicClosure (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion /
          (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion)),
      ∀ (g : Gal(AlgebraicClosure v.1.Completion / v.1.Completion))
        (hg : x * gsRealFamily S ιr v g * x⁻¹ ∈ gsOpenSubgroup S hL),
        gsBaseChange S hL ⟨x * gsRealFamily S ιr v g * x⁻¹, hg⟩ =
          decompHomS (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion
            (placesOver S) ιw (e g) := by
  have hLO : (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).LiesOver v.1 :=
    (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L).2
  have hf : Module.finrank v.1.Completion
      (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion = 1 :=
    (InfinitePlace.finrank_completion_eq_one_iff _).2 fun h =>
      (InfinitePlace.not_isReal_iff_isComplex.2 h.2) hreal
  have hcK : ∀ y : (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion,
      ∃ a : v.1.Completion, infCompletionEmbedding (gsRealEmbedding S ιr v x) L y =
        algebraMap v.1.Completion (AlgebraicClosure v.1.Completion) a := by
    intro y
    have hmem : y ∈ (⊥ : Subalgebra v.1.Completion
        (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion) := by
      rw [Subalgebra.bot_eq_top_of_finrank_eq_one hf]
      exact Algebra.mem_top
    obtain ⟨a, rfl⟩ := Algebra.mem_bot.1 hmem
    exact ⟨a, (infCompletionEmbedding (gsRealEmbedding S ιr v x) L).commutes a⟩
  let _ : Algebra (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion
      (AlgebraicClosure v.1.Completion) :=
    (infCompletionEmbedding (gsRealEmbedding S ιr v x) L).toRingHom.toAlgebra
  have : IsScalarTower v.1.Completion
      (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion
      (AlgebraicClosure v.1.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((infCompletionEmbedding (gsRealEmbedding S ιr v x) L).commutes a).symm
  have : Algebra.IsAlgebraic (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion
      (AlgebraicClosure v.1.Completion) :=
    Algebra.IsAlgebraic.tower_top (K := v.1.Completion) _
  have : IsAlgClosure (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion
      (AlgebraicClosure v.1.Completion) := ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion ≃ₐ[
      (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion]
      AlgebraicClosure v.1.Completion := IsAlgClosure.equiv _ _ _
  let _ : Algebra L.1 (AlgebraicClosure v.1.Completion) :=
    ((algebraMap (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion
      (AlgebraicClosure v.1.Completion)).comp
      (algebraMap L.1 (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion)).toAlgebra
  have : IsScalarTower L.1 (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion
      (AlgebraicClosure v.1.Completion) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[L.1] AlgebraicClosure v.1.Completion :=
    { (gsRealEmbedding S ιr v x).toRingHom with
      commutes' := fun y => (infCompletionEmbedding_algebraMap (gsRealEmbedding S ιr v x) L y).symm }
  let ιw : ℚ̄ →ₐ[L.1] AlgebraicClosure
      (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion :=
    (θ.symm.toAlgHom.restrictScalars L.1).comp ιE'
  have hfix : ∀ (σ : Gal(AlgebraicClosure v.1.Completion / v.1.Completion))
      (y : (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion),
      σ (algebraMap _ (AlgebraicClosure v.1.Completion) y) = algebraMap _ (AlgebraicClosure v.1.Completion) y := by
    intro σ y
    obtain ⟨a, ha⟩ := hcK y
    change σ (infCompletionEmbedding (gsRealEmbedding S ιr v x) L y) =
      infCompletionEmbedding (gsRealEmbedding S ιr v x) L y
    rw [ha]
    exact σ.commutes a
  refine ⟨ιw, galConjEquiv θ hfix, fun g hg => ?_⟩
  have key : ∀ y : maxUnramifiedOutside L.1 ℚ̄ (placesOver S),
      θ.symm (gsRealEmbedding S ιr v x ((gsBaseChange S hL ⟨x * gsRealFamily S ιr v g * x⁻¹, hg⟩ y :
        maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) : ℚ̄)) =
      θ.symm (g (gsRealEmbedding S ιr v x (y : ℚ̄))) := by
    intro y
    have hc := gsRealEmbedding_conj S ιr v x g ((gsFieldEquiv hL).symm y)
    rw [coe_fieldEquivOfRestrictScalarsEq_symm] at hc
    rw [coe_gsBaseChange_apply]
    exact congrArg θ.symm hc
  have hιw : ∀ z, ιw z = θ.symm (gsRealEmbedding S ιr v x z) := fun _ => rfl
  have key' : ∀ y : maxUnramifiedOutside L.1 ℚ̄ (placesOver S),
      (ιw.comp (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)).val)
        (gsBaseChange S hL ⟨x * gsRealFamily S ιr v g * x⁻¹, hg⟩ y) =
      galConjEquiv θ hfix g ((ιw.comp (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)).val) y) := by
    intro y
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, galConjEquiv_apply]
    rw [hιw, hιw, θ.apply_symm_apply]
    exact key y
  exact ((decompHom_eq_iff (Kv := (infPlaceOfEmbedding (gsRealEmbedding S ιr v x) L : InfinitePlace L.1).Completion)
    (ιw.comp (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)).val) (galConjEquiv θ hfix g)
    (gsBaseChange S hL ⟨x * gsRealFamily S ιr v g * x⁻¹, hg⟩)).2 key').symm

end Data

section Bijective

variable {k H G : Type} [CommRing k] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

theorem bijective_cohomologyMapAlong_of_equiv (e : H ≃ₜ* G) {A : Rep.{0} k G} {B : Rep.{0} k H}
    [IsDiscreteRep A] [IsDiscreteRep B] (f : Rep.res e.toMulEquiv.toMonoidHom A ⟶ B)
    (g : Rep.res e.symm.toMulEquiv.toMonoidHom B ⟶ A) (hgf : ∀ a : A, g.hom (f.hom a) = a)
    (hfg : ∀ b : B, f.hom (g.hom b) = b) (n : ℕ) :
    Function.Bijective (cohomologyMapAlong e.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e) f n).hom := by
  have h1 : cohomologyMapAlong e.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e) f n ≫
      cohomologyMapAlong e.symm.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e.symm) g n = 𝟙 _ := by
    rw [← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_eq_id _ _ (MonoidHom.ext fun x => e.apply_symm_apply x) (fun a => hgf a) n
  have h2 : cohomologyMapAlong e.symm.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e.symm) g n ≫
      cohomologyMapAlong e.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e) f n = 𝟙 _ := by
    rw [← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_eq_id _ _ (MonoidHom.ext fun x => e.symm_apply_apply x) (fun b => hfg b) n
  have l1 : Function.LeftInverse
      (cohomologyMapAlong e.symm.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e.symm) g n).hom
      (cohomologyMapAlong e.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e) f n).hom := fun x =>
    (hom_apply_hom_apply_of_comp_eq h1 x).trans rfl
  have l2 : Function.RightInverse
      (cohomologyMapAlong e.symm.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e.symm) g n).hom
      (cohomologyMapAlong e.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e) f n).hom := fun y =>
    (hom_apply_hom_apply_of_comp_eq h2 y).trans rfl
  exact ⟨l1.injective, l2.surjective⟩

end Bijective

section AbstractTransfer

variable {k W Γ : Type} [CommRing k] [Group W] [TopologicalSpace W] [IsTopologicalGroup W]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (E : W ≃ₜ* Γ) (V : Type) [AddCommGroup V] [Module k V]
  [IsDiscreteRep (Rep.trivial k W V)] [IsDiscreteRep (Rep.trivial k Γ V)]
  {P : Type} {C : P → Type} [∀ p, Group (C p)] [∀ p, TopologicalSpace (C p)] [∀ p, IsTopologicalGroup (C p)]
  (f : ∀ p, C p →ₜ* W)
  {Q : Type} {D : Q → Type} [∀ q, Group (D q)] [∀ q, TopologicalSpace (D q)] [∀ q, IsTopologicalGroup (D q)]
  (g : ∀ q, D q →ₜ* Γ)
  (σ : P → Q) (hσ : Function.Injective σ) (mem : Q → P) (hmem : ∀ q, σ (mem q) = q)
  (e : ∀ q, C (mem q) ≃ₜ* D q) (he : ∀ q x, E (f (mem q) x) = g q (e q x))
  [∀ p, IsDiscreteRep (Rep.res (f p).toMonoidHom (Rep.trivial k W V))]
  [∀ q, IsDiscreteRep (Rep.res (g q).toMonoidHom (Rep.trivial k Γ V))]

def trivialRes (n : ℕ) (c : cohomology (Rep.trivial k W V) n) :
    ∀ p, cohomology (Rep.res (f p).toMonoidHom (Rep.trivial k W V)) n :=
  fun p => (cohomologyMapAlong (f p).toMonoidHom (continuous_toMonoidHom (f p))
    (𝟙 (Rep.res (f p).toMonoidHom (Rep.trivial k W V))) n).hom c

include hσ hmem he in

theorem trivialRes_transfer (n : ℕ) :
    (Function.Injective (globalToLocal g (Rep.trivial k Γ V) (fun q => Rep.res (g q).toMonoidHom
        (Rep.trivial k Γ V)) (fun _ => 𝟙 _) n).hom → Function.Injective (trivialRes (k := k) V f n)) ∧
    (Function.Surjective (globalToLocal g (Rep.trivial k Γ V) (fun q => Rep.res (g q).toMonoidHom
        (Rep.trivial k Γ V)) (fun _ => 𝟙 _) n).hom → Function.Surjective (trivialRes (k := k) V f n)) := by
  classical
  have : IsDiscreteRep (Rep.res E.symm.toMulEquiv.toMonoidHom (Rep.trivial k W V)) :=
    IsDiscreteRep.res (continuous_mulEquiv_toMonoidHom E.symm) _
  let m0 : Rep.res E.symm.toMulEquiv.toMonoidHom (Rep.trivial k W V) ⟶ Rep.trivial k Γ V :=
    Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  let m0' : Rep.res E.symm.symm.toMulEquiv.toMonoidHom (Rep.trivial k Γ V) ⟶ Rep.trivial k W V :=
    Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  let Φ := cohomologyMapAlong E.symm.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom E.symm) m0 n
  have hΦ : Function.Bijective Φ.hom :=
    bijective_cohomologyMapAlong_of_equiv E.symm m0 m0' (fun _ => rfl) (fun _ => rfl) n
  have : ∀ q, IsDiscreteRep (Rep.res (e q).symm.toMulEquiv.toMonoidHom
      (Rep.res (f (mem q)).toMonoidHom (Rep.trivial k W V))) := fun q =>
    IsDiscreteRep.res (continuous_mulEquiv_toMonoidHom (e q).symm) _
  let m1 : ∀ q, Rep.res (e q).symm.toMulEquiv.toMonoidHom
      (Rep.res (f (mem q)).toMonoidHom (Rep.trivial k W V)) ⟶
      Rep.res (g q).toMonoidHom (Rep.trivial k Γ V) := fun _ => Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  let m1' : ∀ q, Rep.res (e q).symm.symm.toMulEquiv.toMonoidHom
      (Rep.res (g q).toMonoidHom (Rep.trivial k Γ V)) ⟶
      Rep.res (f (mem q)).toMonoidHom (Rep.trivial k W V) := fun _ => Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  let τ := fun q => cohomologyMapAlong (e q).symm.toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (e q).symm) (m1 q) n
  have hτ : ∀ q, Function.Bijective (τ q).hom := fun q =>
    bijective_cohomologyMapAlong_of_equiv (e q).symm (m1 q) (m1' q) (fun _ => rfl) (fun _ => rfl) n
  have hmaps : ∀ q, (f (mem q)).toMonoidHom.comp (e q).symm.toMulEquiv.toMonoidHom =
      E.symm.toMulEquiv.toMonoidHom.comp (g q).toMonoidHom := fun q => MonoidHom.ext fun y => by
    change f (mem q) ((e q).symm y) = E.symm (g q y)
    rw [E.eq_symm_apply, he q, (e q).apply_symm_apply]
  have key : ∀ q c, (τ q).hom (trivialRes (k := k) V f n c (mem q)) =
      (globalToLocal g (Rep.trivial k Γ V) (fun q => Rep.res (g q).toMonoidHom
        (Rep.trivial k Γ V)) (fun _ => 𝟙 _) n).hom (Φ.hom c) q := by
    intro q c
    have hcomp := (cohomologyMapAlong_comp _ (continuous_toMonoidHom (f (mem q))) (𝟙 _) _
      (continuous_mulEquiv_toMonoidHom (e q).symm) (m1 q) n).symm.trans
      ((cohomologyMapAlong_congr _ _ _ _ (hmaps q) (fun _ => rfl) n).trans
        (cohomologyMapAlong_comp _ (continuous_mulEquiv_toMonoidHom E.symm) m0 _
          (continuous_toMonoidHom (g q)) (𝟙 _) n))
    exact hom_apply_hom_apply_eq_of_comp_eq hcomp c
  refine ⟨fun hinj c c' hcc => ?_, fun hsurj t => ?_⟩
  · apply hΦ.1
    apply hinj
    funext q
    exact (key q c).symm.trans ((congrArg (τ q).hom (congrFun hcc (mem q))).trans (key q c'))
  · obtain ⟨y, hy⟩ := hsurj fun q => (τ q).hom (t (mem q))
    obtain ⟨c, rfl⟩ := hΦ.2 y
    refine ⟨c, funext fun p => ?_⟩
    have hp : mem (σ p) = p := hσ (hmem _)
    have h2 := (hτ (σ p)).1 ((key (σ p) c).trans (congrFun hy (σ p)))
    have hgen : ∀ p' : P, p' = p → trivialRes (k := k) V f n c p' = t p' → trivialRes (k := k) V f n c p = t p := by
      intro p' hp' h
      subst hp'
      exact h
    exact hgen _ hp h2

end AbstractTransfer

section Apply

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {κ : Type} {F : κ → Type} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, CompactSpace (F w)] (ψ : ∀ w, F w →ₜ* G)
  (W : OpenSubgroup G) (V : Type) [AddCommGroup V] [Module k V] [IsDiscreteRep (Rep.trivial k (W : Subgroup G) V)]

omit [CompactSpace G] [∀ w, CompactSpace (F w)] in

theorem mackeyTopRes_trivial_eq [∀ p : MackeyTopIndex ψ W, IsDiscreteRep
      (Rep.res (mackeyConjₜ W (ψ p.1.1) p.1.2.out).toMonoidHom (Rep.trivial k (W : Subgroup G) V))] (n : ℕ) :
    mackeyTopRes ψ W (Rep.trivial k (W : Subgroup G) V) n =
      trivialRes (k := k) V (fun p : MackeyTopIndex ψ W => mackeyConjₜ W (ψ p.1.1) p.1.2.out) n :=
  rfl

omit [CompactSpace G] [∀ w, CompactSpace (F w)] in

theorem mackeyTopRes_transfer {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (E : (W : Subgroup G) ≃ₜ* Γ) [IsDiscreteRep (Rep.trivial k Γ V)]
    {Q : Type} {D : Q → Type} [∀ q, Group (D q)] [∀ q, TopologicalSpace (D q)] [∀ q, IsTopologicalGroup (D q)]
    (g : ∀ q, D q →ₜ* Γ) (σ : MackeyTopIndex ψ W → Q) (hσ : Function.Injective σ)
    (mem : Q → MackeyTopIndex ψ W) (hmem : ∀ q, σ (mem q) = q)
    (e : ∀ q, (mackeySubgroup (W : Subgroup G) (ψ (mem q).1.1).toMonoidHom (mem q).1.2.out) ≃ₜ* D q)
    (he : ∀ q x, E (mackeyConjₜ W (ψ (mem q).1.1) (mem q).1.2.out x) = g q (e q x))
    [∀ p : MackeyTopIndex ψ W, IsDiscreteRep
      (Rep.res (mackeyConjₜ W (ψ p.1.1) p.1.2.out).toMonoidHom (Rep.trivial k (W : Subgroup G) V))]
    [∀ q, IsDiscreteRep (Rep.res (g q).toMonoidHom (Rep.trivial k Γ V))] (n : ℕ) :
    (Function.Injective (globalToLocal g (Rep.trivial k Γ V) (fun q => Rep.res (g q).toMonoidHom
        (Rep.trivial k Γ V)) (fun _ => 𝟙 _) n).hom →
      Function.Injective (mackeyTopRes ψ W (Rep.trivial k (W : Subgroup G) V) n)) ∧
    (Function.Surjective (globalToLocal g (Rep.trivial k Γ V) (fun q => Rep.res (g q).toMonoidHom
        (Rep.trivial k Γ V)) (fun _ => 𝟙 _) n).hom →
      Function.Surjective (mackeyTopRes ψ W (Rep.trivial k (W : Subgroup G) V) n)) := by
  rw [mackeyTopRes_trivial_eq]
  exact trivialRes_transfer E V (fun p : MackeyTopIndex ψ W => mackeyConjₜ W (ψ p.1.1) p.1.2.out) g σ hσ mem hmem
    e he n

end Apply

section Transfer

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

theorem coe_realMemberPlace (p : MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL)) :
    ((realMemberPlace S ιr hL p : {w : InfinitePlace L.1 // w.IsReal}) : InfinitePlace L.1) =
      (infPlaceOfEmbedding (gsRealEmbedding S ιr p.1.1 p.1.2.out) L : InfinitePlace L.1) :=
  rfl

theorem exists_real_data_of_eq (p : MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL))
    (w : {w : InfinitePlace L.1 // w.IsReal})
    (hp : (infPlaceOfEmbedding (gsRealEmbedding S ιr p.1.1 p.1.2.out) L : InfinitePlace L.1) = w.1) :
    ∃ (ιw : ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion)
      (e : Gal(AlgebraicClosure p.1.1.1.Completion / p.1.1.1.Completion) ≃*
        Gal(AlgebraicClosure w.1.Completion / w.1.Completion)),
      ∀ (g : Gal(AlgebraicClosure p.1.1.1.Completion / p.1.1.1.Completion))
        (hg : p.1.2.out * gsRealFamily S ιr p.1.1 g * p.1.2.out⁻¹ ∈ gsOpenSubgroup S hL),
        gsBaseChange S hL ⟨p.1.2.out * gsRealFamily S ιr p.1.1 g * p.1.2.out⁻¹, hg⟩ =
          decompHomS w.1.Completion (placesOver S) ιw (e g) := by
  obtain ⟨w, hw⟩ := w
  subst hp
  exact exists_real_data S ιr hL p.1.1 p.1.2.out hw

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

set_option maxHeartbeats 1000000 in
include h2S in

theorem gsMackeyTop_gsOpenSubgroup (j : ℕ) :
    (4 ≤ j → GsMackeyTopInjective S ιr (gsOpenSubgroup S hL) j) ∧
      (3 ≤ j → GsMackeyTopSurjective S ιr (gsOpenSubgroup S hL) j) := by
  classical
  have h2SL : ∀ v : HeightOneSpectrum (𝓞 L.1), ((2 : ℕ) : 𝓞 L.1) ∈ v.asIdeal → v ∈ placesOver S :=
    fun v hv => mem_placesOver_of_natCast_mem h2S hv
  choose mem hmem using realMemberPlace_surjective S ιr hL
  choose ιrL e he using fun w => exists_real_data_of_eq S ιr hL (mem w) w
    ((coe_realMemberPlace S ιr hL (mem w)).symm.trans (congrArg Subtype.val (hmem w)))
  let e' : ∀ w : {w : InfinitePlace L.1 // w.IsReal},
      (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr (mem w).1.1).toMonoidHom (mem w).1.2.out) ≃ₜ*
        Gal(AlgebraicClosure w.1.Completion / w.1.Completion) := fun w =>
    { toMulEquiv := ((MulEquiv.subgroupCongr (mem w).2).trans Subgroup.topEquiv).trans (e w)
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  have he' : ∀ w x, gsBaseChange S hL (mackeyConjₜ (gsOpenSubgroup S hL) (gsRealFamily S ιr (mem w).1.1)
      (mem w).1.2.out x) = gsRealFamily (placesOver S) ιrL w (e' w x) := fun w x =>
    (congrArg (gsBaseChange S hL) (Subtype.ext rfl)).trans
      (he w (x : Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion))
        ((mem_mackeySubgroup _ _ _ _).1 x.2))
  have : ∀ p : MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL),
      IsDiscreteRep (Rep.res (mackeyConjₜ (gsOpenSubgroup S hL) (gsRealFamily S ιr p.1.1) p.1.2.out).toMonoidHom
        (Rep.trivial (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (ULift.{0} (ZMod 2)))) := fun p =>
    IsDiscreteRep.res (continuous_toMonoidHom _) _
  have : ∀ w : {w : InfinitePlace L.1 // w.IsReal},
      IsDiscreteRep (Rep.res (gsRealFamily (placesOver S) ιrL w).toMonoidHom
        (Rep.trivial (ULift.{0} ℤ) (galUnramifiedOutside L.1 ℚ̄ (placesOver S)) (ULift.{0} (ZMod 2)))) := fun w =>
    IsDiscreteRep.res (continuous_toMonoidHom _) _
  have ht := mackeyTopRes_transfer (k := ULift.{0} ℤ) (gsRealFamily S ιr) (gsOpenSubgroup S hL)
    (ULift.{0} (ZMod 2)) (gsBaseChange S hL) (gsRealFamily (placesOver S) ιrL) (realMemberPlace S ιr hL)
    (realMemberPlace_injective S ιr hL) mem hmem e' he' j
  exact ⟨fun hj => ht.1 (injective_gsRealRes_zmodRep_two (placesOver S) ιrL h2SL hj),
    fun hj => ht.2 (surjective_gsRealRes_zmodRep_two (placesOver S) ιrL h2SL hj)⟩

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

include h2S in

theorem gsTateCompactCohomology_coind_zmodRep_two_eq_zero
    (W : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) {r : ℕ} (hr : 4 ≤ r)
    (x : gsTateCompactCohomology S ιr ιs (Rep.coind (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (zmodRep.{0} (G := (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) 2)) r) : x = 0 := by
  obtain ⟨L', hKL', hL', rfl⟩ := exists_gsOpenSubgroup_eq K S W
  exact gsTateCompactCohomology_coind_zmodRep_eq_zero_of S ιs ιr (gsOpenSubgroup S hL')
    (fun j hj => (gsMackeyTop_gsOpenSubgroup S ιr hL' h2S j).1 hj)
    (fun j hj => (gsMackeyTop_gsOpenSubgroup S ιr hL' h2S j).2 hj) hr x

end Transfer

end GroundTheory.ProfCoh
end
end
