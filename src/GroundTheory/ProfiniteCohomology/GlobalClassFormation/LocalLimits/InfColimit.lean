import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.LiesOver
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.ApplyCompletionEmbeddingOfLocalDecompHomEqOne
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LocalTransition

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield
  NumberField.InfinitePlace.Completion

open scoped TensorProduct Pointwise NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

variable (F : FiniteSubfield) [Fact (K ≤ F)]

def infEmbedLevel : F.1 →ₐ[K.1] AlgebraicClosure v.Completion :=
  ι.comp (IsScalarTower.toAlgHom K.1 F.1 ℚ̄)

@[simp]
theorem infEmbedLevel_apply (x : F.1) : infEmbedLevel ι F x = ι x :=
  rfl

instance (v : NumberField.InfinitePlace K.1) : Finite (v.placesOver F.1) := inferInstance

def infTensorLift :
    GroundTheory.Global.InfinitePlace.PiPlacesOver (L := F.1) v →ₐ[v.Completion]
      AlgebraicClosure v.Completion :=
  (Algebra.TensorProduct.lift (Algebra.ofId _ _) (infEmbedLevel ι F)
    (fun _ _ ↦ Commute.all _ _)).comp
      (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).symm.toAlgHom

theorem infTensorLift_tensorPiEquiv' (t : v.Completion ⊗[K.1] F.1) :
    infTensorLift ι F (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v t) =
      Algebra.TensorProduct.lift (Algebra.ofId _ _) (infEmbedLevel ι F)
        (fun _ _ ↦ Commute.all _ _) t := by
  simp [infTensorLift, -GroundTheory.Global.InfinitePlace.tensorPiEquiv_apply]

theorem infTensorLift_tensorPiEquiv (a : v.Completion) (x : F.1) :
    infTensorLift ι F (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (a ⊗ₜ x)) =
      algebraMap v.Completion (AlgebraicClosure v.Completion) a * ι x := by
  rw [infTensorLift_tensorPiEquiv', Algebra.TensorProduct.lift_tmul]
  rfl

theorem infTensorLift_algebraMap (x : F.1) :
    infTensorLift ι F (algebraMap F.1 (GroundTheory.Global.InfinitePlace.PiPlacesOver (L := F.1) v) x) =
      ι x := by
  have : algebraMap F.1 (GroundTheory.Global.InfinitePlace.PiPlacesOver (L := F.1) v) x =
      GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (1 ⊗ₜ x) := by
    funext w
    rw [GroundTheory.Global.InfinitePlace.tensorPiEquiv_apply,
      GroundTheory.Global.InfinitePlace.tensorPiHom_tmul, map_one, one_mul]
    rfl
  rw [this, infTensorLift_tensorPiEquiv, map_one, one_mul]

open Classical in
theorem exists_unique_infTensorLift_single :
    ∃! w : v.placesOver F.1, infTensorLift ι F (Pi.single w 1) = 1 := by
  have := Fintype.ofFinite (v.placesOver F.1)
  exact exists_unique_map_single_one_eq_one (infTensorLift ι F).toRingHom

def infPlaceOfEmbedding : v.placesOver F.1 :=
  (exists_unique_infTensorLift_single ι F).exists.choose

open Classical in
theorem infTensorLift_single_infPlaceOfEmbedding :
    infTensorLift ι F (Pi.single (infPlaceOfEmbedding ι F) 1) = 1 :=
  (exists_unique_infTensorLift_single ι F).exists.choose_spec

open Classical in
theorem eq_infPlaceOfEmbedding_of_infTensorLift {w : v.placesOver F.1}
    (h : infTensorLift ι F (Pi.single w 1) = 1) : w = infPlaceOfEmbedding ι F :=
  (exists_unique_infTensorLift_single ι F).unique h (infTensorLift_single_infPlaceOfEmbedding ι F)

theorem pi_single_algebraMap_eq_infinite {w : v.placesOver F.1} [DecidableEq (v.placesOver F.1)]
    (a : v.Completion) :
    Pi.single w (algebraMap v.Completion (w : NumberField.InfinitePlace F.1).Completion a) =
      algebraMap v.Completion (GroundTheory.Global.InfinitePlace.PiPlacesOver (L := F.1) v) a *
        Pi.single w 1 := by
  funext u
  by_cases hu : u = w
  · subst hu
    simp
  · simp [hu]

open Classical in

def infCompletionEmbedding :
    (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion]
      AlgebraicClosure v.Completion where
  toFun x := infTensorLift ι F (Pi.single (infPlaceOfEmbedding ι F) x)
  map_one' := infTensorLift_single_infPlaceOfEmbedding ι F
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' x y := by
    rw [Pi.single_add]
    exact (infTensorLift ι F).toRingHom.map_add _ _
  commutes' a := by
    rw [pi_single_algebraMap_eq_infinite, map_mul, AlgHom.commutes,
      infTensorLift_single_infPlaceOfEmbedding, mul_one]

theorem infTensorLift_eq (y : GroundTheory.Global.InfinitePlace.PiPlacesOver (L := F.1) v) :
    infTensorLift ι F y = infCompletionEmbedding ι F (y (infPlaceOfEmbedding ι F)) := by
  classical
  have := Fintype.ofFinite (v.placesOver F.1)
  exact map_eq_map_single_of_map_single_one (φ := (infTensorLift ι F).toRingHom)
    (infTensorLift_single_infPlaceOfEmbedding ι F) y

@[simp]
theorem infCompletionEmbedding_algebraMap (x : F.1) :
    infCompletionEmbedding ι F
      (algebraMap F.1 (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion x) =
      ι x := by
  rw [← infTensorLift_algebraMap ι F x, infTensorLift_eq]
  rfl

theorem algHom_ext_infCompletion {B : Type*} [Semiring B] [Algebra K.1 B]
    [Algebra v.Completion B] [IsScalarTower K.1 v.Completion B] {w : v.placesOver F.1}
    {f g : (w : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion] B}
    (h : ∀ x : F.1, f (algebraMap F.1 _ x) = g (algebraMap F.1 _ x)) : f = g := by
  have key : (f.comp (Pi.evalAlgHom _ _ w)).comp
        (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).toAlgHom =
      (g.comp (Pi.evalAlgHom _ _ w)).comp
        (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a x
    change f ((GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (a ⊗ₜ x)) w) =
      g ((GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (a ⊗ₜ x)) w)
    rw [GroundTheory.Global.InfinitePlace.tensorPiEquiv_apply,
      GroundTheory.Global.InfinitePlace.tensorPiHom_tmul, map_mul, map_mul]
    congr 1
    · rw [AlgHom.commutes, AlgHom.commutes]
    · exact h x
  ext y
  classical
  obtain ⟨t, ht⟩ := (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).surjective
    (Pi.single w y)
  have := DFunLike.congr_fun key t
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at this
  rw [show (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).toAlgHom t =
    GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v t from rfl, ht,
    Pi.single_eq_same] at this
  exact this

theorem eq_infPlaceOfEmbedding {w : v.placesOver F.1}
    (j : (w : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion]
      AlgebraicClosure v.Completion)
    (hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x) : w = infPlaceOfEmbedding ι F := by
  classical
  have key : infTensorLift ι F = j.comp (Pi.evalAlgHom _ _ w) := by
    have : (infTensorLift ι F).comp
          (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).toAlgHom =
        (j.comp (Pi.evalAlgHom _ _ w)).comp
          (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro a x
      change infTensorLift ι F (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (a ⊗ₜ x)) =
        j ((GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (a ⊗ₜ x)) w)
      rw [infTensorLift_tensorPiEquiv, GroundTheory.Global.InfinitePlace.tensorPiEquiv_apply,
        GroundTheory.Global.InfinitePlace.tensorPiHom_tmul, map_mul, ← hj x]
      congr 1
      exact (j.commutes a).symm
    ext y
    obtain ⟨t, rfl⟩ := (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).surjective y
    exact DFunLike.congr_fun this t
  apply eq_infPlaceOfEmbedding_of_infTensorLift
  refine (DFunLike.congr_fun key _).trans ?_
  rw [AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same, map_one]

section Decomposition

theorem infiniteCompletionMap_algebraMap_completion (τ : F.1 ≃ₐ[K.1] F.1)
    (w' : NumberField.InfinitePlace F.1) [w'.LiesOver v]
    [(w'.comap ((τ : F.1 ≃+* F.1) : F.1 →+* F.1)).LiesOver v] (c : v.Completion) :
    AdeleBaseChange.infiniteCompletionMap (τ : F.1 ≃+* F.1) w'
      (algebraMap v.Completion (w'.comap ((τ : F.1 ≃+* F.1) : F.1 →+* F.1)).Completion c) =
      algebraMap v.Completion w'.Completion c := by
  have h := (denseRange_coe v).equalizer
    ((continuous_infiniteCompletionMap _ w').comp (continuous_algebraMap v.Completion
      (w'.comap ((τ : F.1 ≃+* F.1) : F.1 →+* F.1)).Completion))
    (continuous_algebraMap v.Completion w'.Completion) (funext fun a ↦ ?_)
  · exact congrFun h c
  · simp only [Function.comp_apply]
    change AdeleBaseChange.infiniteCompletionMap (τ : F.1 ≃+* F.1) w'
      (algebraMap v.Completion _ (algebraMap K.1 v.Completion (WithAbs.ofAbs a))) =
      algebraMap v.Completion w'.Completion (algebraMap K.1 v.Completion (WithAbs.ofAbs a))
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply K.1 F.1, AdeleBaseChange.infiniteCompletionMap_algebraMap,
      AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

variable [F.1.fixingSubgroup.Normal]

theorem decompHom_smul_infPlaceOfEmbedding (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) :
    decompHom v.Completion (infEmbedLevel ι F) σ • (infPlaceOfEmbedding ι F :
      NumberField.InfinitePlace F.1) = infPlaceOfEmbedding ι F := by
  set τ := decompHom v.Completion (infEmbedLevel ι F) σ
  set w₀ := infPlaceOfEmbedding ι F
  have hcomap : (w₀ : NumberField.InfinitePlace F.1).comap ((τ : F.1 ≃+* F.1) : F.1 →+* F.1) =
      τ⁻¹ • (w₀ : NumberField.InfinitePlace F.1) :=
    AdeleBaseChange.comap_eq_inv_smul τ w₀
  have hu : ((w₀ : NumberField.InfinitePlace F.1).comap
      ((τ : F.1 ≃+* F.1) : F.1 →+* F.1)).LiesOver v := by
    rw [GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, hcomap,
      GroundTheory.Global.InfinitePlace.comap_smul_algebraMap,
      ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]
    exact w₀.2
  let u : v.placesOver F.1 := ⟨_, hu⟩
  let j : (u : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion]
      AlgebraicClosure v.Completion :=
    σ.symm.toAlgHom.comp ((infCompletionEmbedding ι F).comp
      { AdeleBaseChange.infiniteCompletionMap (τ : F.1 ≃+* F.1) w₀ with
        commutes' := infiniteCompletionMap_algebraMap_completion F τ w₀ })
  have hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x := by
    intro x
    change σ.symm (infCompletionEmbedding ι F (AdeleBaseChange.infiniteCompletionMap
      (τ : F.1 ≃+* F.1) w₀ (algebraMap F.1 _ x))) = ι x
    rw [AdeleBaseChange.infiniteCompletionMap_algebraMap, infCompletionEmbedding_algebraMap]
    have h := decompHom_apply (Kv := v.Completion) (infEmbedLevel ι F) σ x
    rw [infEmbedLevel_apply, infEmbedLevel_apply] at h
    rw [AlgEquiv.coe_ringEquiv, h, AlgEquiv.symm_apply_apply]
  have h := congrArg Subtype.val (eq_infPlaceOfEmbedding ι F j hj)
  change (w₀ : NumberField.InfinitePlace F.1).comap ((τ : F.1 ≃+* F.1) : F.1 →+* F.1) =
    (w₀ : NumberField.InfinitePlace F.1) at h
  rw [hcomap] at h
  calc τ • (w₀ : NumberField.InfinitePlace F.1) = τ • (τ⁻¹ • (w₀ : NumberField.InfinitePlace F.1)) := by
        rw [h]
    _ = w₀ := smul_inv_smul τ _

def infLocalDecompHom :
    Gal(AlgebraicClosure v.Completion/v.Completion) →*
      MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1) :=
  (decompHom v.Completion (infEmbedLevel ι F)).codRestrict _ fun σ ↦
    MulAction.mem_stabilizer_iff.2 (decompHom_smul_infPlaceOfEmbedding ι F σ)

theorem coe_infLocalDecompHom (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) :
    (infLocalDecompHom ι F σ : Gal(F.1/K.1)) = decompHom v.Completion (infEmbedLevel ι F) σ :=
  rfl

theorem ι_infLocalDecompHom_apply (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) (x : F.1) :
    ι ((infLocalDecompHom ι F σ : Gal(F.1/K.1)) x : F.1) = σ (ι x) :=
  decompHom_apply (Kv := v.Completion) (infEmbedLevel ι F) σ x

theorem continuous_infLocalDecompHom : Continuous (infLocalDecompHom ι F) :=
  (continuous_decompHom (infEmbedLevel ι F)).subtype_mk _

theorem infCompletionEmbedding_smul (σ : Gal(AlgebraicClosure v.Completion/v.Completion))
    (y : (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion) :
    infCompletionEmbedding ι F (infLocalDecompHom ι F σ • y) = σ (infCompletionEmbedding ι F y) := by
  have : (infCompletionEmbedding ι F).comp (infiniteDecompositionAlgEquiv v
      (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1) (infLocalDecompHom ι F σ)).toAlgHom =
      σ.toAlgHom.comp (infCompletionEmbedding ι F) := by
    apply algHom_ext_infCompletion
    intro x
    change infCompletionEmbedding ι F (infLocalDecompHom ι F σ • algebraMap F.1 _ x) =
      σ (infCompletionEmbedding ι F (algebraMap F.1 _ x))
    have e : infLocalDecompHom ι F σ • algebraMap F.1
        (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion x =
        algebraMap F.1 (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
          ((infLocalDecompHom ι F σ : Gal(F.1/K.1)) x) :=
      infiniteDecomposition_smul_coe (infLocalDecompHom ι F σ) (WithAbs.toAbs _ x)
    rw [e, infCompletionEmbedding_algebraMap, infCompletionEmbedding_algebraMap,
      ι_infLocalDecompHom_apply]
  exact DFunLike.congr_fun this y

def infLocalUnitsMor :
    Rep.res (infLocalDecompHom ι F) (Rep.ofMulDistribMulAction
      (MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1))
      ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) ⟶
      galUnitsZ v.Completion (AlgebraicClosure v.Completion) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive
      (Units.map (infCompletionEmbedding ι F).toRingHom.toMonoidHom)).toIntLinearMap,
    fun σ ↦ LinearMap.ext fun x ↦
      congrArg Additive.ofMul (Units.ext (infCompletionEmbedding_smul ι F σ
        ((Additive.toMul x : ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) :
          (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)))⟩

@[simp]
theorem infLocalUnitsMor_hom_apply
    (x : Additive ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) :
    ((Additive.toMul ((infLocalUnitsMor ι F).hom x) : (AlgebraicClosure v.Completion)ˣ) :
      AlgebraicClosure v.Completion) =
      infCompletionEmbedding ι F (x.toMul :
        (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion) :=
  rfl

def infLocalInfl (n : ℕ) :
    cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1))
      ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) n ⟶
      cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) n :=
  cohomologyMapAlong (infLocalDecompHom ι F) (continuous_infLocalDecompHom ι F)
    (infLocalUnitsMor ι F) n

end Decomposition

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField GroundTheory.Global FiniteSubfield NumberField.InfinitePlace.Completion

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
  {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]

theorem comap_liesOver (w' : v.placesOver E.1) :
    ((w' : NumberField.InfinitePlace E.1).comap (algebraMap F.1 E.1)).LiesOver v := by
  rw [GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, ← NumberField.InfinitePlace.comap_comp,
    ← IsScalarTower.algebraMap_eq, ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]
  exact w'.2

theorem completionMap_algebraMap_completion (u : NumberField.InfinitePlace F.1)
    (w' : NumberField.InfinitePlace E.1) [w'.LiesOver u] [u.LiesOver v] [w'.LiesOver v]
    (c : v.Completion) :
    NumberField.LiesOver.completionMap (v := u) (w := w') (algebraMap v.Completion u.Completion c) =
      algebraMap v.Completion w'.Completion c := by
  have h := (denseRange_coe v).equalizer
    ((NumberField.LiesOver.continuous_completionMap).comp
      (continuous_algebraMap v.Completion u.Completion))
    (continuous_algebraMap v.Completion w'.Completion) (funext fun a ↦ ?_)
  · exact congrFun h c
  · simp only [Function.comp_apply]
    change algebraMap u.Completion w'.Completion
      (algebraMap v.Completion _ (algebraMap K.1 v.Completion (WithAbs.ofAbs a))) =
      algebraMap v.Completion _ (algebraMap K.1 v.Completion (WithAbs.ofAbs a))
    rw [← IsScalarTower.algebraMap_apply K.1 v.Completion u.Completion,
      ← IsScalarTower.algebraMap_apply K.1 v.Completion w'.Completion,
      IsScalarTower.algebraMap_apply K.1 F.1, ← IsScalarTower.algebraMap_apply F.1,
      IsScalarTower.algebraMap_apply K.1 E.1 w'.Completion,
      IsScalarTower.algebraMap_apply F.1 E.1 w'.Completion]
    rfl

variable (F E) in

def infCompletionEmbeddingBelow (u : v.placesOver F.1)
    [(infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (u : NumberField.InfinitePlace F.1)] :
    (u : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion] AlgebraicClosure v.Completion :=
  { (infCompletionEmbedding ι E).toRingHom.comp (NumberField.LiesOver.completionMap
      (v := (u : NumberField.InfinitePlace F.1))
      (w := (infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1))) with
    commutes' c := by
      change infCompletionEmbedding ι E (NumberField.LiesOver.completionMap
        (algebraMap v.Completion _ c)) = _
      rw [completionMap_algebraMap_completion]
      exact (infCompletionEmbedding ι E).commutes c }

theorem infCompletionEmbeddingBelow_algebraMap (u : v.placesOver F.1)
    [(infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (u : NumberField.InfinitePlace F.1)] (x : F.1) :
    infCompletionEmbeddingBelow ι F E u (algebraMap F.1 _ x) = ι x := by
  change infCompletionEmbedding ι E (algebraMap u.1.Completion _ (algebraMap F.1 _ x)) = ι x
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F.1 E.1,
    infCompletionEmbedding_algebraMap]
  rfl

instance liesOver_infPlaceOfEmbedding :
    (infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1) := by
  have hu := comap_liesOver (F := F) (infPlaceOfEmbedding ι E)
  let u : v.placesOver F.1 := ⟨_, hu⟩
  have : (infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (u : NumberField.InfinitePlace F.1) :=
    (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq _ _).2 rfl
  have h := eq_infPlaceOfEmbedding ι F (infCompletionEmbeddingBelow ι F E u)
    (infCompletionEmbeddingBelow_algebraMap ι u)
  rw [← h]
  exact this

theorem infCompletionEmbedding_completionMap
    (a : (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion) :
    infCompletionEmbedding ι E (NumberField.LiesOver.completionMap
      (v := (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1))
      (w := (infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1)) a) =
      infCompletionEmbedding ι F a := by
  have : infCompletionEmbeddingBelow ι F E (infPlaceOfEmbedding ι F) = infCompletionEmbedding ι F :=
    algHom_ext_infCompletion F fun x ↦ by
      rw [infCompletionEmbeddingBelow_algebraMap, infCompletionEmbedding_algebraMap]
  exact DFunLike.congr_fun this a

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField GroundTheory.Global FiniteSubfield

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

section Level

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

theorem infLocalDecompHom_surjective : Function.Surjective (infLocalDecompHom ι F) := by
  intro τ
  let _ : Algebra (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
      (AlgebraicClosure v.Completion) := (infCompletionEmbedding ι F).toRingHom.toAlgebra
  have : IsScalarTower v.Completion (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
      (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ ((infCompletionEmbedding ι F).commutes a).symm
  let ψ := infiniteDecompositionToLocal v (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1) τ
  refine ⟨ψ.liftNormal (AlgebraicClosure v.Completion), Subtype.ext ?_⟩
  rw [coe_infLocalDecompHom, decompHom_eq_iff]
  intro x
  rw [infEmbedLevel_apply, infEmbedLevel_apply, ← infCompletionEmbedding_algebraMap,
    ← infCompletionEmbedding_algebraMap]
  change algebraMap _ (AlgebraicClosure v.Completion)
      (algebraMap F.1 (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion (τ.1 x)) =
    (ψ.liftNormal (AlgebraicClosure v.Completion)) (algebraMap _ _
      (algebraMap F.1 (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion x))
  rw [AlgEquiv.liftNormal_commutes, infiniteDecompositionToLocal_apply]
  exact congrArg (algebraMap _ (AlgebraicClosure v.Completion))
    (infiniteDecomposition_smul_coe τ (WithAbs.toAbs _ x)).symm

omit [F.1.fixingSubgroup.Normal] in

theorem isComplex_infPlaceOfEmbedding {r : F.1} (hr : r ^ 2 = -1) :
    (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).IsComplex := by
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hreal
  let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal
  have h : e (algebraMap F.1 _ r) ^ 2 = -1 := by
    rw [← map_pow, ← map_pow, hr, map_neg, map_one, map_neg, map_one]
  have := sq_nonneg (e (algebraMap F.1 _ r))
  rw [h] at this
  linarith

omit [F.1.fixingSubgroup.Normal] in

theorem isAlgClosed_infCompletion {r : F.1} (hr : r ^ 2 = -1) :
    IsAlgClosed (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion :=
  IsAlgClosed.of_ringEquiv ℂ _
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (isComplex_infPlaceOfEmbedding ι F hr)).symm

omit [F.1.fixingSubgroup.Normal] in

theorem infCompletionEmbedding_surjective {r : F.1} (hr : r ^ 2 = -1) :
    Function.Surjective (infCompletionEmbedding ι F) := by
  have := isAlgClosed_infCompletion ι F hr
  let _ : Algebra (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
      (AlgebraicClosure v.Completion) := (infCompletionEmbedding ι F).toRingHom.toAlgebra
  have : IsScalarTower v.Completion (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
      (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ ((infCompletionEmbedding ι F).commutes a).symm
  have : Algebra.IsIntegral (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
      (AlgebraicClosure v.Completion) := Algebra.IsIntegral.tower_top v.Completion
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)
    (K := AlgebraicClosure v.Completion)).2

theorem infLocalDecompHom_injective (hF : Function.Surjective (infCompletionEmbedding ι F)) :
    Function.Injective (infLocalDecompHom ι F) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply AlgEquiv.ext
  intro α
  obtain ⟨y, rfl⟩ := hF α
  have h1 := infCompletionEmbedding_smul ι F σ y
  have h2 : infLocalDecompHom ι F σ • y = y := by
    rw [hσ]
    exact one_smul _ y
  rw [h2] at h1
  exact h1.symm

end Level

theorem exists_level_infCompletionEmbedding_surjective :
    ∃ p₀ : GLevel K, ∀ p : GLevel K, p₀ ≤ p → Function.Surjective (infCompletionEmbedding ι p.1) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℚ̄) two_pos
  obtain ⟨p₀, hr₀⟩ := exists_level_mem (K := K) r
  refine ⟨p₀, fun p hp ↦ ?_⟩
  have hrp : r ∈ p.1.1 := (show p₀.1.1 ≤ p.1.1 from hp) hr₀
  exact infCompletionEmbedding_surjective ι p.1 (r := ⟨r, hrp⟩) (Subtype.ext hr)

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField IntermediateField GroundTheory.Global
  GroundTheory.Global.SemiLocal FiniteSubfield

open scoped Pointwise NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

section Level

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

abbrev infLocalLevelRep :
    Rep ℤ (MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1)) :=
  Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1))
    ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ

abbrev infLocalCochainsInfl :
    cochainsComplex (infLocalLevelRep ι F) ⟶
      cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) :=
  cochainsMapAlong (infLocalDecompHom ι F) (continuous_infLocalDecompHom ι F) (infLocalUnitsMor ι F)

theorem infLocalUnitsMor_injective : Function.Injective (infLocalUnitsMor ι F).hom := by
  intro a b h
  have h' := congrArg (fun u ↦ ((Additive.toMul u :
    (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion)) h
  simp only at h'
  exact congrArg Additive.ofMul (Units.ext ((infCompletionEmbedding ι F).toRingHom.injective h'))

theorem infLocalCochains_injective (m : ℕ) : Function.Injective ((infLocalCochainsInfl ι F).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (infLocalLevelRep ι F)).f m)).1 inferInstance
  funext τ
  obtain ⟨σ, rfl⟩ : ∃ σ : Fin m → Gal(AlgebraicClosure v.Completion/v.Completion),
      (fun i ↦ infLocalDecompHom ι F (σ i)) = τ :=
    ⟨fun i ↦ Function.surjInv (infLocalDecompHom_surjective ι F) (τ i),
      funext fun i ↦ Function.surjInv_eq (infLocalDecompHom_surjective ι F) (τ i)⟩
  have h1 := congrFun (congrArg (fun c ↦ ((cochainsComplexι
    (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).f m).hom c) h) σ
  exact infLocalUnitsMor_injective ι F h1

end Level

theorem exists_infLevel_factor (m : ℕ)
    (f : (Fin m → Gal(AlgebraicClosure v.Completion/v.Completion)) →
      Additive (AlgebraicClosure v.Completion)ˣ) :
    ∃ (p : GLevel K) (z : (Fin m → MulAction.stabilizer Gal(p.1.1/K.1)
      (infPlaceOfEmbedding ι p.1 : NumberField.InfinitePlace p.1.1)) →
        ((infPlaceOfEmbedding ι p.1 : NumberField.InfinitePlace p.1.1).Completion)ˣ),
      ∀ g, infCompletionEmbedding ι p.1 (z fun i ↦ infLocalDecompHom ι p.1 (g i)) =
        ((Additive.toMul (f g) : (AlgebraicClosure v.Completion)ˣ) :
          AlgebraicClosure v.Completion) := by
  have hp := exists_level_infCompletionEmbedding_surjective ι
  obtain ⟨p, hp⟩ := hp
  have hsurj := hp p le_rfl
  have hinj := infLocalDecompHom_injective ι p.1 hsurj
  have hval : ∀ g, ∃ z : ((infPlaceOfEmbedding ι p.1 : NumberField.InfinitePlace p.1.1).Completion)ˣ,
      infCompletionEmbedding ι p.1 z = ((Additive.toMul (f g) :
        (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion) := by
    intro g
    have hy := hsurj ((Additive.toMul (f g) : (AlgebraicClosure v.Completion)ˣ) :
      AlgebraicClosure v.Completion)
    obtain ⟨y, hy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (Additive.toMul (f g) : (AlgebraicClosure v.Completion)ˣ).ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, by rw [Units.val_mk0, hy]⟩
  choose z hz using hval
  refine ⟨p, fun τ ↦ z fun i ↦ Function.surjInv (infLocalDecompHom_surjective ι p.1) (τ i),
    fun g ↦ ?_⟩
  have hg : (fun i ↦ Function.surjInv (infLocalDecompHom_surjective ι p.1)
      (infLocalDecompHom ι p.1 (g i))) = g :=
    funext fun i ↦ hinj (Function.surjInv_eq (infLocalDecompHom_surjective ι p.1) _)
  change infCompletionEmbedding ι p.1 (z fun i ↦ Function.surjInv
    (infLocalDecompHom_surjective ι p.1) (infLocalDecompHom ι p.1 (g i))) = _
  rw [hg]
  exact hz g

theorem exists_infLocalCochains_eq (m : ℕ)
    (x : (cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (infLocalLevelRep ι p.1)).X m),
      ((infLocalCochainsInfl ι p.1).f m).hom y = x := by
  have hfac := exists_infLevel_factor ι m (((cochainsComplexι (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).f m).hom x)
  obtain ⟨p, z, hz⟩ := hfac
  refine ⟨p, ⟨fun τ ↦ Additive.ofMul (z τ), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).f m)).1 inferInstance
  funext g
  exact congrArg Additive.ofMul (Units.ext ((infLocalUnitsMor_hom_apply ι p.1 _).trans (hz g)))

section Transition

variable {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

theorem infDecompRestrict_infLocalDecompHom
    (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) :
    infDecompRestrict (w := infPlaceOfEmbedding ι F) (w' := infPlaceOfEmbedding ι E)
      (infLocalDecompHom ι E σ) = infLocalDecompHom ι F σ := by
  apply Subtype.ext
  rw [coe_infDecompRestrict, coe_infLocalDecompHom]
  refine ((decompHom_eq_iff (infEmbedLevel ι F) σ _).2 fun x ↦ ?_).symm
  rw [infEmbedLevel_apply, infEmbedLevel_apply]
  have h1 := coe_levelRestrict_apply (K := K) (F := F) (E := E)
    (infLocalDecompHom ι E σ : Gal(E.1/K.1)) x
  have h2 := ι_infLocalDecompHom_apply ι E σ (algebraMap F.1 E.1 x)
  rw [← h1] at h2
  exact h2

theorem infLocalUnitsMor_infCompletionUnitsRep (a : Additive ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) :
    (infLocalUnitsMor ι E).hom ((infCompletionUnitsRep (w := infPlaceOfEmbedding ι F)
      (w' := infPlaceOfEmbedding ι E)).hom a) = (infLocalUnitsMor ι F).hom a :=
  congrArg Additive.ofMul (Units.ext (infCompletionEmbedding_completionMap ι _))

theorem infLocalCochains_comp :
    cochainsMapAlong (infDecompRestrict (w := infPlaceOfEmbedding ι F) (w' := infPlaceOfEmbedding ι E))
      continuous_of_discreteTopology infCompletionUnitsRep ≫ infLocalCochainsInfl ι E =
      infLocalCochainsInfl ι F := by
  rw [← cochainsMapAlong_comp]
  ext m x : 3
  apply Subtype.ext
  funext g
  have hfun : (fun i ↦ infDecompRestrict (w := infPlaceOfEmbedding ι F) (w' := infPlaceOfEmbedding ι E)
      (infLocalDecompHom ι E (g i))) = fun i ↦ infLocalDecompHom ι F (g i) :=
    funext fun i ↦ infDecompRestrict_infLocalDecompHom ι (g i)
  exact (infLocalUnitsMor_infCompletionUnitsRep ι _).trans
    (congrArg (fun τ ↦ (infLocalUnitsMor ι F).hom
      (((cochainsComplexι (infLocalLevelRep ι F)).f m).hom x τ)) hfun)

theorem infLocalTransition_comp_infLocalInfl (n : ℕ) :
    infLocalTransition K F E (infPlaceOfEmbedding ι F) (infPlaceOfEmbedding ι E) n ≫ infLocalInfl ι E n =
      infLocalInfl ι F n := by
  have h := congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
    (infLocalCochains_comp ι (F := F) (E := E))
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

end Transition

section Generic

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem exists_infLocalInfl_eq_homologyπ (n : ℕ)
    (z : (cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).cycles n)
    (y₀ : (cochainsComplex (infLocalLevelRep ι F)).X n)
    (hy₀ : ((infLocalCochainsInfl ι F).f n).hom y₀ = ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).iCycles n).hom z) :
    ∃ y : cohomology (infLocalLevelRep ι F) n, (infLocalInfl ι F n).hom y =
      ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).homologyπ n).hom z := by
  have hd : ((cochainsComplex (infLocalLevelRep ι F)).d n (n + 1)).hom y₀ = 0 := by
    apply infLocalCochains_injective ι F (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨((cochainsComplex (infLocalLevelRep ι F)).homologyπ n).hom w,
    (homologyMap_homologyπ_apply (infLocalCochainsInfl ι F) n w).trans (congrArg _ ?_)⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]

set_option maxHeartbeats 4000000 in

theorem exists_d_eq_of_infLocalInfl_eq_zero (n : ℕ) (w : (cochainsComplex (infLocalLevelRep ι F)).cycles n)
    (hy : (infLocalInfl ι F n).hom (((cochainsComplex (infLocalLevelRep ι F)).homologyπ n).hom w) = 0) :
    ∃ u : (cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).X ((ComplexShape.up ℕ).prev n),
      ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).d _ n).hom u =
        ((infLocalCochainsInfl ι F).f n).hom (((cochainsComplex (infLocalLevelRep ι F)).iCycles n).hom w) := by
  have hy' := (homologyMap_homologyπ_apply (infLocalCochainsInfl ι F) n w).symm.trans hy
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff _ _).1 hy'
  rw [iCycles_cyclesMap_apply] at hu
  exact ⟨u, hu⟩

end Generic

section GenericTransition

variable {F M E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ M)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [Fact (M ≤ E)] [F.1.fixingSubgroup.Normal] [M.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem infLocalTransition_homologyπ_eq_zero (n : ℕ) (w : (cochainsComplex (infLocalLevelRep ι F)).cycles n)
    (u' : (cochainsComplex (infLocalLevelRep ι M)).X ((ComplexShape.up ℕ).prev n))
    (hu : ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).d _ n).hom (((infLocalCochainsInfl ι M).f _).hom u') =
        ((infLocalCochainsInfl ι F).f n).hom (((cochainsComplex (infLocalLevelRep ι F)).iCycles n).hom w)) :
    (infLocalTransition K F E (infPlaceOfEmbedding ι F) (infPlaceOfEmbedding ι E) n).hom
      (((cochainsComplex (infLocalLevelRep ι F)).homologyπ n).hom w) = 0 := by
  refine (homologyMap_homologyπ_apply (cochainsMapAlong (infDecompRestrict (w := infPlaceOfEmbedding ι F)
    (w' := infPlaceOfEmbedding ι E)) continuous_of_discreteTopology infCompletionUnitsRep) n w).trans
    ((homologyπ_eq_zero_iff _ _).2 ⟨((cochainsMapAlong (infDecompRestrict (w := infPlaceOfEmbedding ι M)
      (w' := infPlaceOfEmbedding ι E)) continuous_of_discreteTopology infCompletionUnitsRep).f _).hom u',
      ?_⟩)
  rw [iCycles_cyclesMap_apply]
  apply infLocalCochains_injective ι E n
  rw [hom_f_d_apply]
  have e1 := congrArg (fun φ ↦ (φ.f _).hom u') (infLocalCochains_comp ι (F := M) (E := E))
  have e2 := congrArg (fun φ ↦ (φ.f n).hom (((cochainsComplex (infLocalLevelRep ι F)).iCycles n).hom w))
    (infLocalCochains_comp ι (F := F) (E := E))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  exact (congrArg (fun c ↦ ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).d _ n).hom c) e1).trans (hu.trans e2.symm)

end GenericTransition

set_option maxHeartbeats 4000000 in

theorem exists_infLocalInfl_eq (n : ℕ)
    (x : cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) n) :
    ∃ (p : GLevel K) (y : cohomology (infLocalLevelRep ι p.1) n), (infLocalInfl ι p.1 n).hom y = x := by
  have hz := (ModuleCat.epi_iff_surjective ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).homologyπ n)).1 inferInstance x
  obtain ⟨z, rfl⟩ := hz
  have hc := exists_infLocalCochains_eq ι n (((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).iCycles n).hom z)
  obtain ⟨p, y₀, hy₀⟩ := hc
  have hy := exists_infLocalInfl_eq_homologyπ ι p.1 n z y₀ hy₀
  obtain ⟨y, hy⟩ := hy
  exact ⟨p, y, hy⟩

set_option maxHeartbeats 4000000 in

theorem exists_infLocalTransition_eq_zero (n : ℕ) (p : GLevel K) (y : cohomology (infLocalLevelRep ι p.1) n)
    (hy : (infLocalInfl ι p.1 n).hom y = 0) :
    ∃ (q : GLevel K) (h : p ≤ q), (haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      (infLocalTransition K p.1 q.1 (infPlaceOfEmbedding ι p.1) (infPlaceOfEmbedding ι q.1) n).hom y) = 0 := by
  have hw := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (infLocalLevelRep ι p.1)).homologyπ n)).1 inferInstance y
  obtain ⟨w, rfl⟩ := hw
  have hu := exists_d_eq_of_infLocalInfl_eq_zero ι p.1 n w hy
  obtain ⟨u, hu⟩ := hu
  have hq := exists_infLocalCochains_eq ι _ u
  obtain ⟨q, u', hu'⟩ := hq
  have hr := GLevel.exists_ge p q
  obtain ⟨r, hpr, hqr⟩ := hr
  have : Fact (p.1 ≤ r.1) := ⟨hpr⟩
  have : Fact (q.1 ≤ r.1) := ⟨hqr⟩
  exact ⟨r, hpr, infLocalTransition_homologyπ_eq_zero ι (M := q.1) n w u' (by rw [hu', hu])⟩

end

end GroundTheory.ProfCoh
end
