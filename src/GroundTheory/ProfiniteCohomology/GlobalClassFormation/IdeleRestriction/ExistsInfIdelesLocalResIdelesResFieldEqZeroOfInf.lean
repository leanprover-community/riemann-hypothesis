import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleRestriction
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalResConj
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Splitting

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
  (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem localInfl_finiteComponent_eq_idelesLocalRes (n : ℕ) (y : cohomology (ideleRep K.1 F.1) n) :
    (localInfl ι F n).hom ((finiteComponent (placeOfEmbedding ι F) n).hom y) =
      (idelesLocalRes ι n).hom ((levelInfl K F n).hom y) := by
  have h : finiteComponent (placeOfEmbedding ι F) n ≫ localInfl ι F n = levelInfl K F n ≫ idelesLocalRes ι n := by
    rw [finiteComponent, localInfl, levelInfl, idelesLocalRes, ← cohomologyMapAlong_comp,
      ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _
      (MonoidHom.ext fun σ => coe_localDecompHom_eq_restrictHom ι F σ)
      (fun u : Additive (IdeleGroup F.1) => congrArg Additive.ofMul (idelesProj_of ι F u.toMul).symm) n
  exact congrArg (fun φ => φ.hom y) h

end Finite

section Infinite

variable {v : InfinitePlace K.1} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
  (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem infLocalInfl_infiniteComponent_eq_infIdelesLocalRes (n : ℕ) (y : cohomology (ideleRep K.1 F.1) n) :
    (infLocalInfl ι F n).hom ((infiniteComponent (infPlaceOfEmbedding ι F) n).hom y) =
      (infIdelesLocalRes ι n).hom ((levelInfl K F n).hom y) := by
  have h : infiniteComponent (infPlaceOfEmbedding ι F) n ≫ infLocalInfl ι F n =
      levelInfl K F n ≫ infIdelesLocalRes ι n := by
    rw [infiniteComponent, infLocalInfl, levelInfl, infIdelesLocalRes, ← cohomologyMapAlong_comp,
      ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _
      (MonoidHom.ext fun σ => coe_infLocalDecompHom_eq_restrictHom ι F σ)
      (fun u : Additive (IdeleGroup F.1) =>
        congrArg Additive.ofMul (infIdelesProj_of ι F u.toMul).symm) n
  exact congrArg (fun φ => φ.hom y) h

end Infinite

section Components

variable (ι : LocalEmbeddings K) {n : ℕ} (hn : 1 ≤ n)

set_option maxHeartbeats 4000000 in

theorem idelesLimitCohomologyEquiv_apply_inr (v : HeightOneSpectrum (𝓞 K.1)) (y : cohomology (limitRep K) n) :
    idelesLimitCohomologyEquiv ι hn y (.inr v) = (idelesLocalRes (ι.fin v) n).hom y := by
  obtain ⟨p, z, rfl⟩ := exists_levelInfl_eq n y
  rw [idelesLimitCohomologyEquiv_levelInfl]
  change (localInfl (ι.fin v) p.1 n).hom (ι.places.shapiro n (.inr v) p
      ((cohomologyMap (placeProj (.inr v)) n).hom z)) = _
  rw [CompatiblePlaces.shapiro_placeProj_inr]
  exact localInfl_finiteComponent_eq_idelesLocalRes (ι.fin v) p.1 n z

set_option maxHeartbeats 4000000 in

theorem idelesLimitCohomologyEquiv_apply_inl (v : InfinitePlace K.1) (y : cohomology (limitRep K) n) :
    idelesLimitCohomologyEquiv ι hn y (.inl v) = (infIdelesLocalRes (ι.inf v) n).hom y := by
  obtain ⟨p, z, rfl⟩ := exists_levelInfl_eq n y
  rw [idelesLimitCohomologyEquiv_levelInfl]
  change (infLocalInfl (ι.inf v) p.1 n).hom (ι.places.shapiro n (.inl v) p
      ((cohomologyMap (placeProj (.inl v)) n).hom z)) = _
  rw [CompatiblePlaces.shapiro_placeProj_inl]
  exact infLocalInfl_infiniteComponent_eq_infIdelesLocalRes (ι.inf v) p.1 n z

end Components

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

open scoped NumberField.LiesOver NumberField.AdeleRing

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

instance isDiscreteRep_res_globalDecomp_limitRep (Kv : Type) {Ωv : Type} [Field Kv] [Field Ωv] [Algebra K.1 Kv]
    [Algebra Kv Ωv] [Algebra K.1 Ωv] [IsScalarTower K.1 Kv Ωv] (ι : ℚ̄ →ₐ[K.1] Ωv) :
    IsDiscreteRep (Rep.res (globalDecomp Kv ι) (limitRep K)) :=
  IsDiscreteRep.res (continuous_globalDecomp Kv ι) _

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

theorem completionEmbedding_eq_of_algebraMap (F : FiniteSubfield) [Fact (K ≤ F)] (u : PlacesOver F.1 v)
    (j : u.1.adicCompletion F.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1))
    (hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x) (a : 𝔸[F.1]) :
    j (a.2 u.1) = completionEmbedding ι F (a.2 (placeOfEmbedding ι F).1) := by
  have h := eq_placeOfEmbedding ι F j hj
  subst h
  rw [algHom_ext_adicCompletion F (f := j) (g := completionEmbedding ι F)
    fun x => by rw [hj, completionEmbedding_algebraMap]]

set_option maxHeartbeats 2000000 in

theorem idelesProj_comp (g : K.1.fixingSubgroup) (z : IdeleLimit) :
    idelesProj (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) z = idelesProj ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • z) := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  obtain ⟨p, hp⟩ := GLevel.exists_le (K := K) F
  rw [← of_ideleMap hp x]
  generalize ideleMap hp x = y
  rw [smul_of_restrictHom]
  set r : p.1.1 ≃ₐ[K.1] p.1.1 := restrictHom (E := p.1) g with hr
  set w := placeOfEmbedding ι p.1 with hw
  apply Units.ext
  rw [coe_idelesProj_of, coe_idelesProj_of, coe_smul_idele,
    smul_snd_eq_galHom r (y : 𝔸[p.1.1]) (r⁻¹ • w).1 w.1 (eq_smul_inv_smul v r w)]
  let j : (r⁻¹ • w).1.adicCompletion p.1.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1) :=
    (completionEmbedding ι p.1).comp (galEquiv v r (r⁻¹ • w).1 w.1 (eq_smul_inv_smul v r w)).toAlgHom
  have hj : ∀ x : p.1.1, j (algebraMap p.1.1 _ x) = (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) x := by
    intro x
    change completionEmbedding ι p.1 (galEquiv v r (r⁻¹ • w).1 w.1 (eq_smul_inv_smul v r w)
      (algebraMap p.1.1 _ x)) = ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : ℚ̄))
    rw [galEquiv_algebraMap, completionEmbedding_algebraMap, hr, coe_restrictHom_apply]
  exact (completionEmbedding_eq_of_algebraMap _ p.1 (r⁻¹ • w) j hj (y : 𝔸[p.1.1])).symm

set_option maxHeartbeats 2000000 in

theorem idelesLocalRes_comp (g : K.1.fixingSubgroup) (n : ℕ) :
    idelesLocalRes (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) n = idelesLocalRes ι n := by
  set ι' := ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)
  have hconj := cohomologyMapAlong_conj (limitRep K) (continuous_globalDecomp (v.adicCompletion K.1) ι)
    (continuous_globalDecomp (v.adicCompletion K.1) ι') g (globalDecomp_comp (v.adicCompletion K.1) ι g) n
  have e1 : idelesLocalRes ι' n =
      cohomologyMapAlong (globalDecomp (v.adicCompletion K.1) ι') (continuous_globalDecomp (v.adicCompletion K.1) ι') (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id (idelesLocalMor ι') n := by
    rw [idelesLocalRes, ← cohomologyMapAlong_comp]
    rfl
  have e2 : idelesLocalRes ι n =
      cohomologyMapAlong (globalDecomp (v.adicCompletion K.1) ι) (continuous_globalDecomp (v.adicCompletion K.1) ι) (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id (idelesLocalMor ι) n := by
    rw [idelesLocalRes, ← cohomologyMapAlong_comp]
    rfl
  rw [e1, hconj, Category.assoc, ← cohomologyMapAlong_comp, e2]
  congr 1
  refine cohomologyMapAlong_congr _ _ _ _ rfl (fun (a : Additive IdeleLimit) => ?_) n
  apply Additive.toMul.injective
  change idelesProj ι' (((g⁻¹ : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) • a.toMul) = idelesProj ι a.toMul
  rw [idelesProj_comp, smul_smul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_smul]

theorem idelesLocalRes_eq_of_algHom (ι ι' : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (n : ℕ) :
    idelesLocalRes ι' n = idelesLocalRes ι n := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ι ι'
  have : ι' = ι.comp (fixingSubgroupEquiv K.1 ((fixingSubgroupEquiv K.1).symm g) : ℚ̄ →ₐ[K.1] ℚ̄) := by
    rw [MulEquiv.apply_symm_apply]
    exact hg
  rw [this, idelesLocalRes_comp]

end Finite

section Infinite

variable {v : InfinitePlace K.1} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

theorem infCompletionEmbedding_eq_of_algebraMap (F : FiniteSubfield) [Fact (K ≤ F)] (u : v.placesOver F.1)
    (j : (u : InfinitePlace F.1).Completion →ₐ[v.Completion] AlgebraicClosure v.Completion)
    (hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x) (a : 𝔸[F.1]) :
    j (a.1 u) = infCompletionEmbedding ι F (a.1 (infPlaceOfEmbedding ι F : InfinitePlace F.1)) := by
  have h := eq_infPlaceOfEmbedding ι F j hj
  subst h
  rw [algHom_ext_infCompletion F (f := j) (g := infCompletionEmbedding ι F)
    fun x => by rw [hj, infCompletionEmbedding_algebraMap]]

set_option maxHeartbeats 2000000 in

theorem infIdelesProj_comp (g : K.1.fixingSubgroup) (z : IdeleLimit) :
    infIdelesProj (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) z =
      infIdelesProj ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • z) := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  obtain ⟨p, hp⟩ := GLevel.exists_le (K := K) F
  rw [← of_ideleMap hp x]
  generalize ideleMap hp x = y
  rw [smul_of_restrictHom]
  set r : p.1.1 ≃ₐ[K.1] p.1.1 := restrictHom (E := p.1) g with hr
  set w := infPlaceOfEmbedding ι p.1 with hw
  apply Units.ext
  rw [coe_infIdelesProj_of, coe_infIdelesProj_of, coe_smul_idele, smul_fst r (y : 𝔸[p.1.1])]
  have hcomap : (w : InfinitePlace p.1.1).comap ((r : p.1.1 ≃+* p.1.1) : p.1.1 →+* p.1.1) =
      r⁻¹ • (w : InfinitePlace p.1.1) :=
    AdeleBaseChange.comap_eq_inv_smul r w
  have hu : ((w : InfinitePlace p.1.1).comap ((r : p.1.1 ≃+* p.1.1) : p.1.1 →+* p.1.1)).LiesOver v := by
    rw [GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, hcomap,
      GroundTheory.Global.InfinitePlace.comap_smul_algebraMap,
      ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]
    exact w.2
  let u : v.placesOver p.1.1 := ⟨_, hu⟩
  let j : (u : InfinitePlace p.1.1).Completion →ₐ[v.Completion] AlgebraicClosure v.Completion :=
    (infCompletionEmbedding ι p.1).comp
      { AdeleBaseChange.infiniteCompletionMap (r : p.1.1 ≃+* p.1.1) w with
        commutes' := infiniteCompletionMap_algebraMap_completion p.1 r w }
  have hj : ∀ x : p.1.1, j (algebraMap p.1.1 _ x) = (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) x := by
    intro x
    change infCompletionEmbedding ι p.1 (AdeleBaseChange.infiniteCompletionMap (r : p.1.1 ≃+* p.1.1) w
      (algebraMap p.1.1 _ x)) = ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : ℚ̄))
    rw [AdeleBaseChange.infiniteCompletionMap_algebraMap, infCompletionEmbedding_algebraMap, AlgEquiv.coe_ringEquiv,
      hr, coe_restrictHom_apply]
  exact (infCompletionEmbedding_eq_of_algebraMap _ p.1 u j hj (y : 𝔸[p.1.1])).symm

set_option maxHeartbeats 2000000 in

theorem infIdelesLocalRes_comp (g : K.1.fixingSubgroup) (n : ℕ) :
    infIdelesLocalRes (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) n = infIdelesLocalRes ι n := by
  set ι' := ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)
  have hconj := cohomologyMapAlong_conj (limitRep K) (continuous_globalDecomp v.Completion ι)
    (continuous_globalDecomp v.Completion ι') g (globalDecomp_comp v.Completion ι g) n
  have e1 : infIdelesLocalRes ι' n =
      cohomologyMapAlong (globalDecomp v.Completion ι') (continuous_globalDecomp v.Completion ι') (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id (infIdelesLocalMor ι') n := by
    rw [infIdelesLocalRes, ← cohomologyMapAlong_comp]
    rfl
  have e2 : infIdelesLocalRes ι n =
      cohomologyMapAlong (globalDecomp v.Completion ι) (continuous_globalDecomp v.Completion ι) (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id (infIdelesLocalMor ι) n := by
    rw [infIdelesLocalRes, ← cohomologyMapAlong_comp]
    rfl
  rw [e1, hconj, Category.assoc, ← cohomologyMapAlong_comp, e2]
  congr 1
  refine cohomologyMapAlong_congr _ _ _ _ rfl (fun (a : Additive IdeleLimit) => ?_) n
  apply Additive.toMul.injective
  change infIdelesProj ι' (((g⁻¹ : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) • a.toMul) = infIdelesProj ι a.toMul
  rw [infIdelesProj_comp, smul_smul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_smul]

theorem infIdelesLocalRes_eq_of_algHom (ι ι' : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion) (n : ℕ) :
    infIdelesLocalRes ι' n = infIdelesLocalRes ι n := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ι ι'
  have : ι' = ι.comp (fixingSubgroupEquiv K.1 ((fixingSubgroupEquiv K.1).symm g) : ℚ̄ →ₐ[K.1] ℚ̄) := by
    rw [MulEquiv.apply_symm_apply]
    exact hg
  rw [this, infIdelesLocalRes_comp]

end Infinite

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal

open scoped NumberField.LiesOver NumberField.AdeleRing DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Res

variable (K E : FiniteSubfield) [Fact (K ≤ E)]

def idelesResMor : Rep.res (fixingIncl K E) (limitRep K) ⟶ limitRep E :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def idelesResField (n : ℕ) : cohomology (limitRep K) n ⟶ cohomology (limitRep E) n :=
  cohomologyMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (idelesResMor K E) n

end Res

section Conj

variable {K E : FiniteSubfield} [Fact (K ≤ E)]
  (Kv : Type) {Ωv : Type} [Field Kv] [Field Ωv] [Algebra K.1 Kv] [Algebra Kv Ωv] [Algebra K.1 Ωv]
  [IsScalarTower K.1 Kv Ωv] [Algebra.IsIntegral Kv Ωv]
  (Ew : Type) {Ωw : Type} [Field Ew] [Field Ωw] [Algebra E.1 Ew] [Algebra Ew Ωw] [Algebra E.1 Ωw]
  [IsScalarTower E.1 Ew Ωw] [Algebra.IsIntegral Ew Ωw]
  (L : IntermediateField Kv Ωv) [Algebra.IsIntegral L Ωv] (e : Ωw ≃+* Ωv)
  (hL : ∀ l ∈ L, ∃ y : Ew, e (algebraMap Ew Ωw y) = l)
  (ιK : ℚ̄ →ₐ[K.1] Ωv) (ιE : ℚ̄ →ₐ[E.1] Ωw) (hι : ∀ x, e (ιE x) = ιK x)
  (fK : Rep.res (globalDecomp Kv ιK) (limitRep K) ⟶ galUnitsZ Kv Ωv)
  (fE : Rep.res (globalDecomp Ew ιE) (limitRep E) ⟶ galUnitsZ Ew Ωw)
  (hf : ∀ z : IdeleLimit, e ((Additive.toMul (fE.hom (Additive.ofMul z)) : Ωwˣ) : Ωw) =
    ((Additive.toMul (fK.hom (Additive.ofMul z)) : Ωvˣ) : Ωv))

include hι hf in

theorem cohomologyMapAlong_globalDecomp_idelesResField (n : ℕ) (y : cohomology (limitRep K) n) :
    (cohomologyMapAlong (globalDecomp Ew ιE) (continuous_globalDecomp Ew ιE) fE n).hom
        ((idelesResField K E n).hom y) =
      (cohomologyMapAlong (fieldConjHom Kv L e hL) (continuous_fieldConjHom Kv L e hL)
        (fieldConjUnitsMor Kv L e hL) n).hom
        ((unitsScalarsRes Kv Ωv L n).hom
          ((cohomologyMapAlong (globalDecomp Kv ιK) (continuous_globalDecomp Kv ιK) fK n).hom y)) := by
  have h : idelesResField K E n ≫ cohomologyMapAlong (globalDecomp Ew ιE) (continuous_globalDecomp Ew ιE) fE n =
      cohomologyMapAlong (globalDecomp Kv ιK) (continuous_globalDecomp Kv ιK) fK n ≫
        unitsScalarsRes Kv Ωv L n ≫
          cohomologyMapAlong (fieldConjHom Kv L e hL) (continuous_fieldConjHom Kv L e hL)
            (fieldConjUnitsMor Kv L e hL) n := by
    rw [idelesResField, unitsScalarsRes, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp,
      ← cohomologyMapAlong_comp]
    refine cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun σ => ?_) (fun (a : Additive IdeleLimit) => ?_) n
    · apply Subtype.ext
      apply AlgEquiv.ext
      intro t
      apply ιK.injective
      change ιK ((globalDecomp Ew ιE σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) t) =
        ιK ((globalDecomp Kv ιK (AlgEquiv.restrictScalarsHom Kv (fieldConjHom Kv L e hL σ)) : ℚ̄ ≃ₐ[ℚ] ℚ̄) t)
      rw [globalDecomp_apply, ← hι, ← hι, globalDecomp_apply]
      change e (σ (ιE t)) = e (σ (e.symm (e (ιE t))))
      rw [RingEquiv.symm_apply_apply]
    · apply Additive.toMul.injective
      apply Units.ext
      change ((Additive.toMul (fE.hom (Additive.ofMul a.toMul)) : Ωwˣ) : Ωw) =
        e.symm ((Additive.toMul (fK.hom (Additive.ofMul a.toMul)) : Ωvˣ) : Ωv)
      rw [← hf, RingEquiv.symm_apply_apply]
  exact congrArg (fun φ => φ.hom y) h

end Conj

variable {K E : FiniteSubfield} [Fact (K ≤ E)]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)}

set_option maxHeartbeats 2000000 in

theorem idelesProj_eq_of_algebraMap (w : PlacesOver E.1 v) (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
    (ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (w.1.adicCompletion E.1))
    (e : AlgebraicClosure (w.1.adicCompletion E.1) ≃+* AlgebraicClosure (v.adicCompletion K.1))
    (hι : ∀ x, e (ιE x) = ι x)
    (he : ∀ a : v.adicCompletion K.1, e (algebraMap (w.1.adicCompletion E.1) (AlgebraicClosure (w.1.adicCompletion E.1))
      (algebraMap (v.adicCompletion K.1) (w.1.adicCompletion E.1) a)) =
        algebraMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) a)
    (z : IdeleLimit) :
    e (idelesProj ιE z : AlgebraicClosure (w.1.adicCompletion E.1)) =
      (idelesProj ι z : AlgebraicClosure (v.adicCompletion K.1)) := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  rw [← of_ideleMap (le_joinField_right E F) x]
  generalize ideleMap (le_joinField_right E F) x = x'
  have : Fact (K ≤ joinField E F) := ⟨(Fact.out : K ≤ E).trans (le_joinField_left E F)⟩
  rw [coe_idelesProj_of ιE (joinField E F), coe_idelesProj_of ι (joinField E F)]
  set u := placeOfEmbedding ιE (joinField E F)
  have hu : u.1.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans u.1.asIdeal w.1.asIdeal v.asIdeal
  let j : u.1.adicCompletion (joinField E F).1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1) :=
    { e.toRingHom.comp (completionEmbedding ιE (joinField E F)).toRingHom with
      commutes' := fun a => by
        change e (completionEmbedding ιE (joinField E F) (completionMap v u.1 a)) = _
        rw [← AdeleBaseChange.completionMap_completionMap v w.1 u.1 a]
        change e (completionEmbedding ιE (joinField E F)
          (algebraMap (w.1.adicCompletion E.1) _ (completionMap v w.1 a))) = _
        rw [AlgHom.commutes]
        exact he a }
  have hj : ∀ t : (joinField E F).1, j (algebraMap _ _ t) = ι t := fun t => by
    change e (completionEmbedding ιE (joinField E F) (algebraMap _ _ t)) = ι t
    rw [completionEmbedding_algebraMap, hι]
  exact completionEmbedding_eq_of_algebraMap ι (joinField E F) ⟨u.1, hu⟩ j hj (x' : 𝔸[(joinField E F).1])

end Finite

section Infinite

variable {v : InfinitePlace K.1}

set_option maxHeartbeats 2000000 in

theorem infIdelesProj_eq_of_algebraMap (w : v.placesOver E.1) (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
    (ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (w : InfinitePlace E.1).Completion)
    (e : AlgebraicClosure (w : InfinitePlace E.1).Completion ≃+* AlgebraicClosure v.Completion)
    (hι : ∀ x, e (ιE x) = ι x)
    (he : ∀ a : v.Completion, e (algebraMap (w : InfinitePlace E.1).Completion
      (AlgebraicClosure (w : InfinitePlace E.1).Completion) (algebraMap v.Completion (w : InfinitePlace E.1).Completion a)) =
        algebraMap v.Completion (AlgebraicClosure v.Completion) a)
    (z : IdeleLimit) :
    e (infIdelesProj ιE z : AlgebraicClosure (w : InfinitePlace E.1).Completion) =
      (infIdelesProj ι z : AlgebraicClosure v.Completion) := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  rw [← of_ideleMap (le_joinField_right E F) x]
  generalize ideleMap (le_joinField_right E F) x = x'
  have : Fact (K ≤ joinField E F) := ⟨(Fact.out : K ≤ E).trans (le_joinField_left E F)⟩
  rw [coe_infIdelesProj_of ιE (joinField E F), coe_infIdelesProj_of ι (joinField E F)]
  set u := infPlaceOfEmbedding ιE (joinField E F)
  have hw : (w : InfinitePlace E.1).LiesOver v := w.2
  have huw : (u : InfinitePlace (joinField E F).1).LiesOver (w : InfinitePlace E.1) := u.2
  have hu : (u : InfinitePlace (joinField E F).1).LiesOver v := by
    rw [GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, IsScalarTower.algebraMap_eq K.1 E.1 (joinField E F).1,
      NumberField.InfinitePlace.comap_comp, InfinitePlace.LiesOver.comap_eq (u : InfinitePlace (joinField E F).1)
        (w : InfinitePlace E.1), ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]
    exact hw
  let j : (u : InfinitePlace (joinField E F).1).Completion →ₐ[v.Completion] AlgebraicClosure v.Completion :=
    { e.toRingHom.comp (infCompletionEmbedding ιE (joinField E F)).toRingHom with
      commutes' := fun a => by
        change e (infCompletionEmbedding ιE (joinField E F) (algebraMap v.Completion _ a)) = _
        rw [← completionMap_algebraMap_completion (F := E) (E := joinField E F) (w : InfinitePlace E.1)
          (u : InfinitePlace (joinField E F).1) a]
        change e (infCompletionEmbedding ιE (joinField E F)
          (algebraMap (w : InfinitePlace E.1).Completion _ (algebraMap v.Completion _ a))) = _
        rw [AlgHom.commutes]
        exact he a }
  have hj : ∀ t : (joinField E F).1, j (algebraMap _ _ t) = ι t := fun t => by
    change e (infCompletionEmbedding ιE (joinField E F) (algebraMap _ _ t)) = ι t
    rw [infCompletionEmbedding_algebraMap, hι]
  exact infCompletionEmbedding_eq_of_algebraMap ι (joinField E F) ⟨_, hu⟩ j hj (x' : 𝔸[(joinField E F).1])

end Infinite

section Places

set_option maxHeartbeats 4000000 in
variable (v) in

theorem exists_idelesLocalRes_idelesResField_eq_zero_of_placeOfEmbedding (v : HeightOneSpectrum (𝓞 K.1))
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (y : cohomology (limitRep K) 2)
    (hy : Module.finrank (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1) •
      brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
        ((idelesLocalRes ι 2).hom y) = 0) :
    ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1),
      (idelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y) = 0 := by
  have := finiteDimensional_adicCompletion_placesOver (E := E) (placeOfEmbedding ι E)
  let c := completionEmbedding ι E
  let L := c.fieldRange
  let : Algebra ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    c.toRingHom.toAlgebra
  have : IsScalarTower (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  have : Algebra.IsAlgebraic ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsAlgebraic.tower_top (K := v.adicCompletion K.1) _
  have : IsAlgClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) ≃ₐ[(placeOfEmbedding ι E).1.adicCompletion E.1]
      AlgebraicClosure (v.adicCompletion K.1) := IsAlgClosure.equiv _ _ _
  let : Algebra E.1 (AlgebraicClosure (v.adicCompletion K.1)) :=
    ((algebraMap ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
      (algebraMap E.1 ((placeOfEmbedding ι E).1.adicCompletion E.1))).toAlgebra
  have : IsScalarTower E.1 ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[E.1] AlgebraicClosure (v.adicCompletion K.1) :=
    { ι.toRingHom with commutes' := fun t => (completionEmbedding_algebraMap ι E t).symm }
  let ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) :=
    (θ.symm.toAlgHom.restrictScalars E.1).comp ιE'
  have hι : ∀ t, θ.toRingEquiv (ιE t) = ι t := fun t => θ.apply_symm_apply (ι t)
  have hL : ∀ l ∈ L, ∃ t : (placeOfEmbedding ι E).1.adicCompletion E.1,
      θ.toRingEquiv (algebraMap _ (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)) t) = l := by
    intro l hl
    obtain ⟨t, rfl⟩ := (AlgHom.mem_fieldRange).1 hl
    exact ⟨t, θ.commutes t⟩
  have : FiniteDimensional (v.adicCompletion K.1) L := LinearEquiv.finiteDimensional c.equivFieldRange.toLinearEquiv
  have : Algebra.IsIntegral L (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsIntegral.tower_top (v.adicCompletion K.1)
  have hfin : Module.finrank (v.adicCompletion K.1) L =
      Module.finrank (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1) :=
    c.equivFieldRange.toLinearEquiv.finrank_eq.symm
  have hproj : ∀ z : IdeleLimit, θ.toRingEquiv (idelesProj ιE z : AlgebraicClosure _) =
      (idelesProj ι z : AlgebraicClosure (v.adicCompletion K.1)) :=
    idelesProj_eq_of_algebraMap (placeOfEmbedding ι E) ι ιE θ.toRingEquiv hι fun a => by
      change θ (algebraMap _ (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1))
        (algebraMap (v.adicCompletion K.1) _ a)) = _
      rw [θ.commutes]
      exact c.commutes a
  have h0 : (unitsScalarsRes (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) L 2).hom
      ((idelesLocalRes ι 2).hom y) = 0 :=
    brauerResZ_eq_zero_of_finrank_smul (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) L _
      (by rw [hfin]; exact hy)
  refine ⟨ιE, ?_⟩
  have key := cohomologyMapAlong_globalDecomp_idelesResField (v.adicCompletion K.1)
    ((placeOfEmbedding ι E).1.adicCompletion E.1) L θ.toRingEquiv hL ι ιE hι (idelesLocalMor ι) (idelesLocalMor ιE)
    hproj 2 y
  rw [idelesLocalRes, key]
  change (cohomologyMapAlong _ _ _ 2).hom
    ((unitsScalarsRes (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) L 2).hom
      ((idelesLocalRes ι 2).hom y)) = 0
  rw [h0, map_zero]

set_option maxHeartbeats 4000000 in

theorem exists_infIdelesLocalRes_idelesResField_eq_zero_of_infPlaceOfEmbedding {v : InfinitePlace K.1}
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion) (y : cohomology (limitRep K) 2)
    (hy : (infIdelesLocalRes ι 2).hom y = 0) :
    ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion,
      (infIdelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y) = 0 := by
  have : (infPlaceOfEmbedding ι E : InfinitePlace E.1).LiesOver v := (infPlaceOfEmbedding ι E).2
  let c := infCompletionEmbedding ι E
  let L := c.fieldRange
  let : Algebra (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    c.toRingHom.toAlgebra
  have : IsScalarTower v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
      (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  have : Algebra.IsAlgebraic (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    Algebra.IsAlgebraic.tower_top (K := v.Completion) _
  have : IsAlgClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion ≃ₐ[(infPlaceOfEmbedding ι E :
      InfinitePlace E.1).Completion] AlgebraicClosure v.Completion := IsAlgClosure.equiv _ _ _
  let : Algebra E.1 (AlgebraicClosure v.Completion) :=
    ((algebraMap (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion)).comp
      (algebraMap E.1 (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)).toAlgebra
  have : IsScalarTower E.1 (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[E.1] AlgebraicClosure v.Completion :=
    { ι.toRingHom with commutes' := fun t => (infCompletionEmbedding_algebraMap ι E t).symm }
  let ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion :=
    (θ.symm.toAlgHom.restrictScalars E.1).comp ιE'
  have hι : ∀ t, θ.toRingEquiv (ιE t) = ι t := fun t => θ.apply_symm_apply (ι t)
  have hL : ∀ l ∈ L, ∃ t : (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion,
      θ.toRingEquiv (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) t) = l := by
    intro l hl
    obtain ⟨t, rfl⟩ := (AlgHom.mem_fieldRange).1 hl
    exact ⟨t, θ.commutes t⟩
  have : Algebra.IsIntegral L (AlgebraicClosure v.Completion) := Algebra.IsIntegral.tower_top v.Completion
  have hproj : ∀ z : IdeleLimit, θ.toRingEquiv (infIdelesProj ιE z : AlgebraicClosure _) =
      (infIdelesProj ι z : AlgebraicClosure v.Completion) :=
    infIdelesProj_eq_of_algebraMap (infPlaceOfEmbedding ι E) ι ιE θ.toRingEquiv hι fun a => by
      change θ (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
        (algebraMap v.Completion _ a)) = _
      rw [θ.commutes]
      exact c.commutes a
  refine ⟨ιE, ?_⟩
  have key := cohomologyMapAlong_globalDecomp_idelesResField v.Completion
    (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion L θ.toRingEquiv hL ι ιE hι (infIdelesLocalMor ι)
    (infIdelesLocalMor ιE) hproj 2 y
  rw [infIdelesLocalRes, key]
  change (cohomologyMapAlong _ _ _ 2).hom
    ((unitsScalarsRes v.Completion (AlgebraicClosure v.Completion) L 2).hom ((infIdelesLocalRes ι 2).hom y)) = 0
  rw [hy, map_zero, map_zero]

end Places

section Main

set_option maxHeartbeats 4000000 in

theorem idelesResField_eq_zero (ι : LocalEmbeddings K) (y : cohomology (limitRep K) 2)
    (hinf : ∀ v : InfinitePlace K.1, idelesLimitCohomologyEquiv ι (by norm_num) y (.inl v) = 0)
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 K.1)) (w : PlacesOver E.1 v),
      Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) •
        placeInv (.inr v) (idelesLimitCohomologyEquiv ι (by norm_num) y (.inr v)) = 0) :
    (idelesResField K E 2).hom y = 0 := by
  have Hfin : ∀ w : HeightOneSpectrum (𝓞 E.1), ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (w.adicCompletion E.1),
      (idelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y) = 0 := by
    intro w
    let v : HeightOneSpectrum (𝓞 K.1) := AdeleBaseChange.below K.1 w
    let w' : PlacesOver E.1 v := ⟨w, AdeleBaseChange.liesOver_below w⟩
    obtain ⟨ι', hι'⟩ := exists_placeOfEmbedding_eq w'
    have key : ∀ u : PlacesOver E.1 v, placeOfEmbedding ι' E = u →
        ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (u.1.adicCompletion E.1),
          (idelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y) = 0 := by
      rintro u rfl
      apply exists_idelesLocalRes_idelesResField_eq_zero_of_placeOfEmbedding v ι' y
      rw [idelesLocalRes_eq_of_algHom (ι.fin v) ι' 2, ← idelesLimitCohomologyEquiv_apply_inr ι (by norm_num) v y]
      exact hfin v (placeOfEmbedding ι' E)
    exact key w' hι'
  have Hinf : ∀ w : InfinitePlace E.1, ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure w.Completion,
      (infIdelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y) = 0 := by
    intro w
    let v : InfinitePlace K.1 := w.comap (algebraMap K.1 E.1)
    let w' : v.placesOver E.1 := ⟨w, ⟨rfl⟩⟩
    obtain ⟨ι', hι'⟩ := exists_infPlaceOfEmbedding_eq w'
    have key : ∀ u : v.placesOver E.1, infPlaceOfEmbedding ι' E = u →
        ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (u : InfinitePlace E.1).Completion,
          (infIdelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y) = 0 := by
      rintro u rfl
      apply exists_infIdelesLocalRes_idelesResField_eq_zero_of_infPlaceOfEmbedding ι' y
      rw [infIdelesLocalRes_eq_of_algHom (ι.inf v) ι' 2, ← idelesLimitCohomologyEquiv_apply_inl ι (by norm_num) v y]
      exact hinf v
    exact key w' hι'
  let ιE : LocalEmbeddings E := ⟨fun w => (Hfin w).choose, fun w => (Hinf w).choose⟩
  apply (idelesLimitCohomologyEquiv ιE (n := 2) (by norm_num)).injective
  rw [map_zero]
  refine DFinsupp.ext fun u => ?_
  rw [DirectSum.zero_apply]
  rcases u with w | w
  · rw [idelesLimitCohomologyEquiv_apply_inl]
    exact (Hinf w).choose_spec
  · rw [idelesLimitCohomologyEquiv_apply_inr]
    exact (Hfin w).choose_spec

end Main

end

end GroundTheory.ProfCoh
end
