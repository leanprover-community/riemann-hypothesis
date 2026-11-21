import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs
import GroundTheory.AutomorphicForms.Measures
import GroundTheory.AutomorphicForms.GL2.GJLeviZeta
import GroundTheory.AutomorphicForms.HaarCosets

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Measure Topology Set
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α]

variable (n) in

abbrev LeviIndex (β : Fin n → α) : Type := {ij : Fin n × Fin n // β ij.1 = β ij.2}

variable (F) in

def unipMatrix {β : Fin n → α} (u : UnipotentIndex n β → F) : Matrix (Fin n) (Fin n) F :=
  fun i j => if h : β i < β j then u ⟨(i, j), h⟩ else 0

theorem unipMatrix_apply_of_lt {β : Fin n → α} (u : UnipotentIndex n β → F) {i j : Fin n}
    (h : β i < β j) : unipMatrix F u i j = u ⟨(i, j), h⟩ := by
  simp [unipMatrix, h]

theorem unipMatrix_apply_of_not_lt {β : Fin n → α} (u : UnipotentIndex n β → F) {i j : Fin n}
    (h : ¬ β i < β j) : unipMatrix F u i j = 0 := by
  simp [unipMatrix, h]

section Chart

variable (F n) (β : Fin n → α)

def lieLevi : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | ∀ i j, β i ≠ β j → A i j = 0}
  add_mem' {A B} hA hB i j h := by simp [hA i j h, hB i j h]
  zero_mem' i j _ := rfl
  smul_mem' c A hA i j h := by simp [hA i j h]

variable {F n β} in
theorem mem_lieLevi {A : Matrix (Fin n) (Fin n) F} :
    A ∈ lieLevi F n β ↔ ∀ i j, β i ≠ β j → A i j = 0 :=
  Iff.rfl

variable {F n β} in

theorem mul_mem_lieLevi {A B : Matrix (Fin n) (Fin n) F} (hA : A ∈ lieLevi F n β)
    (hB : B ∈ lieLevi F n β) : A * B ∈ lieLevi F n β := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : β i = β k
  · rw [hB k j (fun e => h (hik.trans e)), mul_zero]
  · rw [hA i k hik, zero_mul]

def leviCoord : lieLevi F n β ≃ₗ[F] (LeviIndex n β → F) where
  toFun A s := (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  invFun x := ⟨Matrix.of fun i j => if h : β i = β j then x ⟨(i, j), h⟩ else 0,
    fun i j hij => by simp [hij]⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    ext i j
    by_cases h : β i = β j
    · simp [h]
    · simp [h, A.2 i j h]
  right_inv x := by
    funext s
    simp [s.2]

@[simp] theorem leviCoord_apply (A : lieLevi F n β) (s : LeviIndex n β) :
    leviCoord F n β A s = (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl

def leviCoordHomeomorph : lieLevi F n β ≃ₜ (LeviIndex n β → F) where
  toEquiv := (leviCoord F n β).toEquiv
  continuous_toFun := continuous_pi fun s =>
    (continuous_subtype_val.matrix_elem s.1.1 s.1.2 :
      Continuous fun A : lieLevi F n β => (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2)
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    by_cases h : β i = β j
    · simp only [Matrix.of_apply, h, dite_true]
      exact continuous_apply _
    · simp only [Matrix.of_apply, h, dite_false]
      exact continuous_const

def toLieLevi (m : levi F n β) : lieLevi F n β :=
  ⟨((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), fun i j h => mem_levi.1 m.2 i j h⟩

theorem isOpenEmbedding_toLieLevi : IsOpenEmbedding (toLieLevi F n β) := by
  have hemb : IsEmbedding (toLieLevi F n β) :=
    ((isOpenEmbedding_val F n).isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
      (lieLevi F n β : Set (Matrix (Fin n) (Fin n) F)) fun m : levi F n β =>
        fun i j h => mem_levi.1 m.2 i j h
  refine ⟨hemb, ?_⟩
  have : Set.range (toLieLevi F n β) = Subtype.val ⁻¹' Set.range
      (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) := by
    ext A
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, rfl⟩
    · rintro ⟨u, hu⟩
      refine ⟨⟨u, mem_levi.2 fun i j h => ?_⟩, Subtype.ext hu⟩
      rw [hu]
      exact A.2 i j h
  rw [this]
  exact (isOpenEmbedding_val F n).isOpen_range.preimage continuous_subtype_val

def mulLeftLieLevi (m : levi F n β) : lieLevi F n β ≃ₗ[F] lieLevi F n β :=
  (Units.mulLeftLinearEquiv F _ (m : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mul_mem_lieLevi (fun i j h => mem_levi.1 m.2 i j h) hA
    · refine ⟨((m⁻¹ : levi F n β) : GL (Fin n) F) * A,
        mul_mem_lieLevi (fun i j h => mem_levi.1 (m⁻¹).2 i j h) hA, ?_⟩
      simp [← mul_assoc])

def mulRightLieLevi (m : levi F n β) : lieLevi F n β ≃ₗ[F] lieLevi F n β :=
  (Units.mulRightLinearEquiv F (m : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mul_mem_lieLevi hA (fun i j h => mem_levi.1 m.2 i j h)
    · refine ⟨A * ((m⁻¹ : levi F n β) : GL (Fin n) F),
        mul_mem_lieLevi hA (fun i j h => mem_levi.1 (m⁻¹).2 i j h), ?_⟩
      simp [mul_assoc])

variable {F n}

def leviChart : LinearChart F (LeviIndex n β) (levi F n β) where
  toFun m := leviCoord F n β (toLieLevi F n β m)
  isOpenEmbedding :=
    (leviCoordHomeomorph F n β).isOpenEmbedding.comp (isOpenEmbedding_toLieLevi F n β)
  left m := (leviCoord F n β).symm.trans ((mulLeftLieLevi F n β m).trans (leviCoord F n β))
  right m := (leviCoord F n β).symm.trans ((mulRightLieLevi F n β m).trans (leviCoord F n β))
  toFun_mul_left g x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  toFun_mul_right h x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl

variable {β}

@[simp] theorem leviChart_apply (m : levi F n β) (s : LeviIndex n β) :
    (leviChart β).toFun m s = ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl

@[simp] theorem parabolicChart_apply (p : blockUpper F n β) (s : ParabolicIndex n β) :
    (parabolicChart F n β).toFun p s = ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl

end Chart

section ParabolicMk

variable {β : Fin n → α}

theorem blockTriangular_add_unipMatrix (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u).BlockTriangular β := by
  intro i j hji
  rw [Matrix.add_apply, mem_levi.1 m.2 i j (ne_of_gt hji),
    unipMatrix_apply_of_not_lt u (not_lt.2 hji.le), add_zero]

theorem det_add_unipMatrix (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u).det =
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
  classical
  have hm : ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular β :=
    fun i j h => mem_levi.1 m.2 i j (ne_of_gt h)
  rw [(blockTriangular_add_unipMatrix m u).det, hm.det]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  ext i j
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.add_apply]
  rw [unipMatrix_apply_of_not_lt u (by rw [i.2, j.2]; exact lt_irrefl _), add_zero]

theorem isUnit_add_unipMatrix (m : levi F n β) (u : UnipotentIndex n β → F) :
    IsUnit (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_add_unipMatrix, ← Matrix.isUnit_iff_isUnit_det]
  exact (m : GL (Fin n) F).isUnit

variable (β) in

def parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) : blockUpper F n β :=
  ⟨(isUnit_add_unipMatrix m u).unit, by
    rw [mem_blockUpper, IsUnit.unit_spec]
    exact blockTriangular_add_unipMatrix m u⟩

theorem coe_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((parabolicMk β m u : blockUpper F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u :=
  IsUnit.unit_spec _

theorem leviProj_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    leviProj F n β (parabolicMk β m u) = m := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [leviProj_apply, coe_parabolicMk]
  split_ifs with h
  · rw [Matrix.add_apply, unipMatrix_apply_of_not_lt u (by rw [h]; exact lt_irrefl _), add_zero]
  · exact (mem_levi.1 m.2 i j h).symm

def unipCoord (p : blockUpper F n β) : UnipotentIndex n β → F :=
  fun s => ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2

theorem unipCoord_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    unipCoord (parabolicMk β m u) = u := by
  funext s
  rw [unipCoord, coe_parabolicMk, Matrix.add_apply, mem_levi.1 m.2 _ _ (ne_of_lt s.2),
    unipMatrix_apply_of_lt u s.2, zero_add]

theorem parabolicMk_leviProj_unipCoord (p : blockUpper F n β) :
    parabolicMk β (leviProj F n β p) (unipCoord p) = p := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [coe_parabolicMk, Matrix.add_apply, leviProj_apply]
  rcases lt_trichotomy (β i) (β j) with h | h | h
  · rw [if_neg (ne_of_lt h), unipMatrix_apply_of_lt _ h, zero_add]
    rfl
  · rw [if_pos h, unipMatrix_apply_of_not_lt _ (by rw [h]; exact lt_irrefl _), add_zero]
  · rw [if_neg (ne_of_gt h), unipMatrix_apply_of_not_lt _ (not_lt.2 h.le), add_zero]
    exact ((mem_blockUpper F n).1 p.2 h).symm

end ParabolicMk

section Ratio

instance locallyCompactSpace_levi_chart (β : Fin n → α) : LocallyCompactSpace (levi F n β) :=
  isClosed_levi.isClosedEmbedding_subtypeVal.locallyCompactSpace

variable (β : Fin n → α)

def leviRatio : levi F n β →* ℝ≥0 where
  toFun m := (leviChart β).leftModulus m / (parabolicChart F n β).leftModulus (leviIncl m)
  map_one' := by
    borelize F ↥(levi F n β) ↥(blockUpper F n β)
    rw [map_one, ← LinearChart.leftModulusHom_apply, ← LinearChart.leftModulusHom_apply, map_one,
      map_one, div_one]
  map_mul' m m' := by
    borelize F ↥(levi F n β) ↥(blockUpper F n β)
    rw [map_mul, LinearChart.leftModulus_mul, LinearChart.leftModulus_mul, div_mul_div_comm]

theorem leviRatio_apply (m : levi F n β) :
    leviRatio β m = (leviChart β).leftModulus m / (parabolicChart F n β).leftModulus (leviIncl m) :=
  rfl

variable {β}

theorem continuous_leviRatio : Continuous (leviRatio (F := F) β) := by
  borelize F ↥(levi F n β) ↥(blockUpper F n β)
  show Continuous fun m : levi F n β =>
    (leviChart β).leftModulus m / (parabolicChart F n β).leftModulus (leviIncl m)
  refine Continuous.div (LinearChart.continuous_leftModulus _) ?_ fun m =>
    (LinearChart.leftModulus_pos _ _).ne'
  exact (LinearChart.continuous_leftModulus _).comp
    (continuous_subtype_val.subtype_mk _ : Continuous fun m : levi F n β => leviIncl m)

end Ratio

section Coordinates

variable (β : Fin n → α)

def coordAddEquiv : ((LeviIndex n β → F) × (UnipotentIndex n β → F)) ≃+ (ParabolicIndex n β → F) where
  toFun x s := if h : β s.1.1 = β s.1.2 then x.1 ⟨s.1, h⟩
    else x.2 ⟨s.1, lt_of_le_of_ne (not_lt.1 s.2) h⟩
  invFun y := (fun s => y ⟨s.1, not_lt.2 s.2.le⟩, fun s => y ⟨s.1, not_lt.2 s.2.le⟩)
  left_inv x := by
    ext s
    · simp [s.2]
    · simp [ne_of_lt s.2]
  right_inv y := by
    funext s
    by_cases h : β s.1.1 = β s.1.2 <;> simp [h]
  map_add' x y := by
    funext s
    by_cases h : β s.1.1 = β s.1.2 <;> simp [h]

theorem coordAddEquiv_apply (x : (LeviIndex n β → F) × (UnipotentIndex n β → F))
    (s : ParabolicIndex n β) :
    coordAddEquiv β x s = if h : β s.1.1 = β s.1.2 then x.1 ⟨s.1, h⟩
      else x.2 ⟨s.1, lt_of_le_of_ne (not_lt.1 s.2) h⟩ :=
  rfl

def coordEquiv : ((LeviIndex n β → F) × (UnipotentIndex n β → F)) ≃ₜ+ (ParabolicIndex n β → F) where
  toAddEquiv := coordAddEquiv β
  continuous_toFun := by
    refine continuous_pi fun s => ?_
    show Continuous fun x : (LeviIndex n β → F) × (UnipotentIndex n β → F) =>
      if h : β s.1.1 = β s.1.2 then x.1 ⟨s.1, h⟩ else x.2 ⟨s.1, lt_of_le_of_ne (not_lt.1 s.2) h⟩
    by_cases h : β s.1.1 = β s.1.2
    · simp only [h, dite_true]
      exact (continuous_apply _).comp continuous_fst
    · simp only [h, dite_false]
      exact (continuous_apply _).comp continuous_snd
  continuous_invFun := by
    refine Continuous.prodMk (continuous_pi fun s => ?_) (continuous_pi fun s => ?_) <;>
    exact continuous_apply _

theorem coe_coordEquiv : ⇑(coordEquiv (F := F) β) = coordAddEquiv β := rfl

variable {β}

theorem continuous_leviProj : Continuous (leviProj F n β) := by
  refine (leviChart β).isOpenEmbedding.isInducing.continuous_iff.2 ?_
  have : (leviChart β).toFun ∘ leviProj F n β = fun (p : blockUpper F n β) (s : LeviIndex n β) =>
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 := by
    funext p s
    simp only [Function.comp_apply, leviChart_apply, leviProj_apply, if_pos s.2]
  rw [this]
  exact continuous_pi fun s =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem s.1.1 s.1.2

theorem parabolicChart_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (parabolicChart F n β).toFun (parabolicMk β m u) = coordAddEquiv β ((leviChart β).toFun m, u) := by
  funext s
  rw [parabolicChart_apply, coe_parabolicMk, Matrix.add_apply, coordAddEquiv_apply]
  by_cases h : β s.1.1 = β s.1.2
  · rw [dif_pos h, unipMatrix_apply_of_not_lt u (by rw [h]; exact lt_irrefl _), add_zero]
    rfl
  · have hlt := lt_of_le_of_ne (not_lt.1 s.2) h
    rw [dif_neg h, mem_levi.1 m.2 _ _ h, unipMatrix_apply_of_lt u hlt, zero_add]

variable (β) in

def parabolicMkHomeomorph : (levi F n β × (UnipotentIndex n β → F)) ≃ₜ blockUpper F n β where
  toFun x := parabolicMk β x.1 x.2
  invFun p := (leviProj F n β p, unipCoord p)
  left_inv x := Prod.ext (leviProj_parabolicMk x.1 x.2) (unipCoord_parabolicMk x.1 x.2)
  right_inv p := parabolicMk_leviProj_unipCoord p
  continuous_toFun := by
    refine (parabolicChart F n β).isOpenEmbedding.isInducing.continuous_iff.2 ?_
    have : (parabolicChart F n β).toFun ∘ (fun x : levi F n β × (UnipotentIndex n β → F) =>
        parabolicMk β x.1 x.2) = fun x => coordEquiv β ((leviChart β).toFun x.1, x.2) := by
      funext x
      rw [Function.comp_apply, parabolicChart_parabolicMk]
      rfl
    rw [this]
    exact (coordEquiv β).continuous.comp
      (((leviChart β).isOpenEmbedding.continuous.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := by
    refine continuous_leviProj.prodMk (continuous_pi fun s => ?_)
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem s.1.1 s.1.2

end Coordinates

theorem eq_one_of_mem_compact {G : Type*} [Group G] [TopologicalSpace G] (χ : G →* ℝ≥0)
    (hχ : Continuous χ) {K : Subgroup G} (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) :
    χ k = 1 := by
  obtain ⟨B, hB⟩ := (hK.image hχ).bddAbove
  have hbd : ∀ x ∈ K, χ x ≤ B := fun x hx => hB ⟨x, hx, rfl⟩
  have key : ∀ x ∈ K, ¬ 1 < χ x := fun x hx h1 => by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt B h1
    rw [← map_pow] at hN
    exact (hbd _ (K.pow_mem hx N)).not_gt hN
  have hne : χ k ≠ 0 := by
    intro h0
    have := map_mul_eq_one χ (mul_inv_cancel k)
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  rcases lt_trichotomy (χ k) 1 with h | h | h
  · exfalso
    refine key k⁻¹ (K.inv_mem hk) ?_
    rw [map_inv]
    exact one_lt_inv₀ (pos_iff_ne_zero.2 hne) |>.2 h
  · exact h
  · exact absurd h (key k hk)

section Measures

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

variable {β : Fin n → α}

variable (β) in

def haarLevi (μ𝔪 : Measure (LeviIndex n β → F)) : Measure (levi F n β) :=
  (leviChart β).haar μ𝔪

instance isHaarMeasure_haarLevi (μ𝔪 : Measure (LeviIndex n β → F)) [μ𝔪.IsAddHaarMeasure] :
    (haarLevi β μ𝔪).IsHaarMeasure :=
  LinearChart.isHaarMeasure_haar _ μ𝔪

variable (β) in

def parabolicMeasure (μ𝔪 : Measure (LeviIndex n β → F)) (μ𝔫 : Measure (UnipotentIndex n β → F)) :
    Measure (ParabolicIndex n β → F) :=
  map (coordEquiv β) (μ𝔪.prod μ𝔫)

instance isAddHaarMeasure_parabolicMeasure (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure] :
    (parabolicMeasure β μ𝔪 μ𝔫).IsAddHaarMeasure :=
  ContinuousAddEquiv.isAddHaarMeasure_map _ _

theorem parabolicChart_leftModulus_of_mem {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ unipotentRadical F n β) :
    (parabolicChart F n β).leftModulus p = 1 := by
  obtain ⟨K, hKc, -, hK⟩ := exists_compactOpen_unipotentRadical
    ({⟨(p : GL (Fin n) F), hp⟩} : Finset (unipotentRadical F n β))
  have hle : ∀ x : unipotentRadical F n β, (x : GL (Fin n) F) ∈ blockUpper F n β :=
    fun x => (mem_unipotentRadical.1 x.2).1
  let φ : unipotentRadical F n β →* blockUpper F n β :=
    { toFun := fun x => ⟨x, hle x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Continuous φ := continuous_induced_rng.2 continuous_subtype_val
  have := eq_one_of_mem_compact (((parabolicChart F n β).leftModulusHom).comp φ)
    ((LinearChart.continuous_leftModulus _).comp hφ) hKc (hK _ (Finset.mem_singleton_self _))
  exact this

theorem parabolicChart_leftModulus_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (parabolicChart F n β).leftModulus (parabolicMk β m u) =
      (parabolicChart F n β).leftModulus (leviIncl m) := by
  have h := leviProj_inv_mul_mem (parabolicMk β m u)
  rw [leviProj_parabolicMk] at h
  have e : parabolicMk β m u = leviIncl m * ((leviIncl m)⁻¹ * parabolicMk β m u) := by group
  rw [e, LinearChart.leftModulus_mul, parabolicChart_leftModulus_of_mem h, mul_one]

theorem comap_parabolicMeasure (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure] :
    (parabolicMeasure β μ𝔪 μ𝔫).comap (parabolicChart F n β).toFun =
      map (parabolicMkHomeomorph β) ((μ𝔪.comap (leviChart β).toFun).prod μ𝔫) := by
  ext S hS
  have hSP := (parabolicChart F n β).measurableEmbedding.measurableSet_image.2 hS
  have hΘ : Measurable (parabolicMkHomeomorph (F := F) β) :=
    (parabolicMkHomeomorph β).continuous.measurable
  have hE : Measurable (coordEquiv (F := F) β) := (coordEquiv β).continuous.measurable
  rw [(parabolicChart F n β).measurableEmbedding.comap_apply, parabolicMeasure,
    map_apply hE hSP, map_apply hΘ hS, Measure.prod_apply (hE hSP), Measure.prod_apply (hΘ hS)]
  set G : (LeviIndex n β → F) → ℝ≥0∞ := fun a =>
    μ𝔫 (Prod.mk a ⁻¹' (coordEquiv β ⁻¹' ((parabolicChart F n β).toFun '' S))) with hG
  have hslice : ∀ m : levi F n β,
      μ𝔫 (Prod.mk m ⁻¹' (parabolicMkHomeomorph β ⁻¹' S)) = G ((leviChart β).toFun m) := by
    intro m
    rw [hG]
    congr 1
    ext u
    simp only [Set.mem_preimage]
    show parabolicMk β m u ∈ S ↔ coordEquiv β ((leviChart β).toFun m, u) ∈ _
    rw [coe_coordEquiv, ← parabolicChart_parabolicMk,
      (parabolicChart F n β).isOpenEmbedding.injective.mem_set_image]
  have hsupp : Function.support G ⊆ Set.range (leviChart β).toFun := by
    intro a ha
    obtain ⟨u, p, -, hp⟩ : ∃ u, coordEquiv β (a, u) ∈ (parabolicChart F n β).toFun '' S := by
      by_contra h
      push Not at h
      apply ha
      rw [hG]
      convert measure_empty (μ := μ𝔫)
      ext u
      simpa using h u
    refine ⟨leviProj F n β p, ?_⟩
    have e := congrArg (fun y => ((coordAddEquiv β).symm y).1) hp
    simp only [coe_coordEquiv, AddEquiv.symm_apply_apply] at e
    rw [← e]
    funext s
    rw [leviChart_apply, leviProj_apply, if_pos s.2]
    rfl
  rw [show (fun x : levi F n β => μ𝔫 (Prod.mk x ⁻¹' (parabolicMkHomeomorph β ⁻¹' S))) =
      fun m => G ((leviChart β).toFun m) from funext hslice,
    ← (leviChart β).measurableEmbedding.lintegral_map, (leviChart β).measurableEmbedding.map_comap,
    setLIntegral_eq_of_support_subset hsupp]

end Measures

section Main

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

variable {β : Fin n → α}

theorem withDensity_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y)
    (ν : Measure X) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (map e ν).withDensity f = map e (ν.withDensity (f ∘ e)) := by
  ext S hS
  rw [withDensity_apply _ hS, map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    setLIntegral_map hS hf e.measurable]
  rfl

theorem haarParabolic_eq_map (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure] :
    haarParabolic (parabolicMeasure β μ𝔪 μ𝔫) =
      map (parabolicMkHomeomorph β)
        (((haarLevi β μ𝔪).withDensity fun m => (leviRatio β m : ℝ≥0∞)).prod μ𝔫) := by
  have hθ : Measurable fun m : levi F n β => (leviRatio β m : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp continuous_leviRatio).measurable
  have hρM := (leviChart (F := F) β).measurable_density
  show ((parabolicMeasure β μ𝔪 μ𝔫).comap (parabolicChart F n β).toFun).withDensity _ = _
  rw [comap_parabolicMeasure, ← Homeomorph.toMeasurableEquiv_coe,
    withDensity_map_equiv _ _ (parabolicChart F n β).measurable_density]
  congr 1
  have hfun : ((fun p : blockUpper F n β =>
      ((((parabolicChart F n β).leftModulus p)⁻¹ : ℝ≥0) : ℝ≥0∞)) ∘
        (parabolicMkHomeomorph β).toMeasurableEquiv) =
      fun z => (fun m : levi F n β => ((((leviChart β).leftModulus m)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        (leviRatio β m : ℝ≥0∞)) z.1 * (1 : (UnipotentIndex n β → F) → ℝ≥0∞) z.2 := by
    funext z
    simp only [Function.comp_apply, Homeomorph.toMeasurableEquiv_coe, Pi.one_apply, mul_one]
    show ((((parabolicChart F n β).leftModulus (parabolicMk β z.1 z.2))⁻¹ : ℝ≥0) : ℝ≥0∞) = _
    rw [parabolicChart_leftModulus_parabolicMk, leviRatio_apply, ← ENNReal.coe_mul]
    congr 1
    have h1 := ((leviChart β).leftModulus_pos z.1).ne'
    have h2 := ((parabolicChart F n β).leftModulus_pos (leviIncl z.1)).ne'
    field_simp
  rw [hfun, ← prod_withDensity (f := fun m : levi F n β =>
      ((((leviChart β).leftModulus m)⁻¹ : ℝ≥0) : ℝ≥0∞) * (leviRatio β m : ℝ≥0∞))
      (hρM.mul hθ) measurable_one, withDensity_one]
  rw [show (fun m : levi F n β =>
      ((((leviChart β).leftModulus m)⁻¹ : ℝ≥0) : ℝ≥0∞) * (leviRatio β m : ℝ≥0∞)) =
      (fun m : levi F n β => ((((leviChart β).leftModulus m)⁻¹ : ℝ≥0) : ℝ≥0∞)) *
        (fun m : levi F n β => (leviRatio β m : ℝ≥0∞)) from rfl, withDensity_mul _ hρM hθ]
  rfl

theorem lintegral_haarParabolic (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure]
    {H : blockUpper F n β → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ p, H p ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
      ∫⁻ m, (leviRatio β m : ℝ≥0∞) * ∫⁻ u, H (parabolicMk β m u) ∂μ𝔫 ∂(haarLevi β μ𝔪) := by
  have hθ : Measurable fun m : levi F n β => (leviRatio β m : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp continuous_leviRatio).measurable
  have hHΘ : Measurable fun z : levi F n β × (UnipotentIndex n β → F) =>
      H (parabolicMkHomeomorph β z) := hH.comp (parabolicMkHomeomorph β).continuous.measurable
  rw [haarParabolic_eq_map, (parabolicMkHomeomorph β).measurableEmbedding.lintegral_map,
    lintegral_prod _ hHΘ.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hθ hHΘ.lintegral_prod_right']
  rfl

theorem integral_haarParabolic (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure]
    {H : blockUpper F n β → ℂ} (hH : Integrable H (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))) :
    ∫ p, H p ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
      ∫ m, (leviRatio β m : ℂ) * ∫ u, H (parabolicMk β m u) ∂μ𝔫 ∂(haarLevi β μ𝔪) := by
  have hθ : Measurable fun m : levi F n β => leviRatio β m :=
    continuous_leviRatio.measurable
  rw [haarParabolic_eq_map] at hH ⊢
  have hΘ := (parabolicMkHomeomorph (F := F) β).measurableEmbedding
  rw [hΘ.integral_map]
  calc ∫ z, H (parabolicMkHomeomorph β z)
        ∂((haarLevi β μ𝔪).withDensity fun m => (leviRatio β m : ℝ≥0∞)).prod μ𝔫
      = ∫ m, ∫ u, H (parabolicMkHomeomorph β (m, u)) ∂μ𝔫
          ∂((haarLevi β μ𝔪).withDensity fun m => (leviRatio β m : ℝ≥0∞)) :=
        integral_prod _ ((hΘ.integrable_map_iff).1 hH)
    _ = ∫ m, leviRatio β m • ∫ u, H (parabolicMkHomeomorph β (m, u)) ∂μ𝔫 ∂(haarLevi β μ𝔪) :=
        integral_withDensity_eq_integral_smul hθ _
    _ = _ := by
        congr 1

theorem isLeviSchwartz_integral (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔫.IsAddHaarMeasure]
    {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    IsLeviSchwartz β (fun X => ∫ u, Φ (X + unipMatrix F u) ∂μ𝔫) := by
  obtain ⟨r, A, hinv, hsupp⟩ := hΦ.exists_invariant
  refine ⟨r, A, fun X Y _ _ hY => ?_, fun X hX hne i j => ?_⟩
  · refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [add_right_comm]
    exact hinv _ Y hY
  · by_cases hij : β i = β j
    · by_contra h
      apply hne
      have hz : (fun u : UnipotentIndex n β → F => Φ (X + unipMatrix F u)) = 0 := by
        funext u
        by_contra h'
        apply h
        have := hsupp _ h' i j
        rwa [Matrix.add_apply, unipMatrix_apply_of_not_lt u (by rw [hij]; exact lt_irrefl _),
          add_zero] at this
      simp only
      rw [hz]
      exact integral_zero _ _
    · rw [hX i j hij, mul_zero]
      exact zero_mem _

end Main

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Polynomial ValuativeRel Topology
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem mem_valBall_neg_iff {A : ℕ} {x : F} :
    x ∈ LocalField.valBall F (-(A : ℤ)) ↔ (uniformizer F : F) ^ A * x ∈ 𝒪[F] := by
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hϖA : (uniformizer F : F) ^ A ∈ LocalField.valBall F (A : ℤ) :=
    (mem_valBall_iff_exists (r := A)).2 ⟨1, one_mem _, by rw [mul_one]⟩
  constructor
  · intro hx
    have := LocalField.mul_mem_valBall hϖA hx
    rw [add_neg_cancel] at this
    exact LocalField.mem_valBall_zero_iff.1 this
  · intro h
    by_cases hx : x = 0
    · rw [hx]; exact zero_mem _
    have h0 := LocalField.mem_valBall_zero_iff.2 h
    have hne : (uniformizer F : F) ^ A * x ≠ 0 := mul_ne_zero (pow_ne_zero _ hϖ) hx
    rw [LocalField.mem_valBall_iff_le_ord hne, LocalField.ord_mul (pow_ne_zero _ hϖ) hx,
      LocalField.ord_pow hϖ, LocalField.ord_uniformizer (irreducible_uniformizer F)] at h0
    rw [LocalField.mem_valBall_iff_le_ord hx]
    linarith

theorem ordDet_eq_zero_of_mem_integralGL {y : GL (Fin n) F} (hy : y ∈ integralGL F n) : ordDet y = 0 := by
  obtain ⟨u, rfl⟩ := hy
  have : ((integralGLHom F n u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      (((Matrix.GeneralLinearGroup.det u : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
    show ((RingHom.mapMatrix (𝒪[F]).subtype) (u : Matrix (Fin n) (Fin n) 𝒪[F])).det = _
    rw [← RingHom.map_det]
    rfl
  rw [ordDet, this]
  exact LocalField.ord_unit _

theorem detPow_mul_of_mem_integralGL (g : GL (Fin n) F) {y : GL (Fin n) F}
    (hy : y ∈ integralGL F n) (s : ℂ) : detPow (g * y) s = detPow g s := by
  have hg : (g : Matrix (Fin n) (Fin n) F).det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  have hy0 : (y : Matrix (Fin n) (Fin n) F).det ≠ 0 := (Matrix.GeneralLinearGroup.det y).ne_zero
  have : ordDet (g * y) = ordDet g := by
    have h := ordDet_eq_zero_of_mem_integralGL hy
    rw [ordDet] at h ⊢
    rw [Units.val_mul, Matrix.det_mul, LocalField.ord_mul hg hy0, h, add_zero]
    rfl
  rw [detPow_eq_qs_zpow, detPow_eq_qs_zpow, this]

theorem continuous_detPow (s : ℂ) : Continuous fun g : GL (Fin n) F => detPow g s := by
  refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg => ?_
  refine ⟨g • (integralGL F n : Set (GL (Fin n) F)), ?_, (isOpen_integralGL F n).smul g,
    ⟨1, one_mem _, mul_one g⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  simp only [Set.mem_preimage, smul_eq_mul, detPow_mul_of_mem_integralGL g hk]
  exact hg

section Parabolic

variable {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem det_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((parabolicMk β m u : blockUpper F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
  rw [coe_parabolicMk, det_add_unipMatrix]

theorem detPow_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) (s : ℂ) :
    detPow ((parabolicMk β m u : blockUpper F n β) : GL (Fin n) F) s =
      detPow (m : GL (Fin n) F) s := by
  rw [detPow, detPow, absDet, absDet, det_parabolicMk]

end Parabolic

theorem IsSchwartzBruhat.comp_mulRight {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (y : GL (Fin n) F) :
    IsSchwartzBruhat fun X => Φ (X * (y : Matrix (Fin n) (Fin n) F)) := by
  let T : Matrix (Fin n) (Fin n) F ≃ₜ Matrix (Fin n) (Fin n) F :=
    { toFun := fun X => X * (y : Matrix (Fin n) (Fin n) F)
      invFun := fun X => X * ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      left_inv := fun X => by
        show X * (y : Matrix (Fin n) (Fin n) F) * ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = X
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      right_inv := fun X => by
        show X * ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F) = X
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
      continuous_invFun := Continuous.matrix_mul continuous_id continuous_const }
  exact ⟨hΦ.1.comp_continuous T.continuous, hΦ.2.comp_homeomorph T⟩

omit [Field F] [ValuativeRel F] [IsNonarchimedeanLocalField F] in

theorem IsSchwartzBruhat.norm {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    IsSchwartzBruhat fun X => ((‖Φ X‖ : ℝ) : ℂ) :=
  ⟨hΦ.1.comp fun z => ((‖z‖ : ℝ) : ℂ),
    HasCompactSupport.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) hΦ.2 (by simp)⟩

theorem IsSchwartzBruhat.exists_mul_congruenceSubgroup {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∃ r : ℕ, ∀ X : Matrix (Fin n) (Fin n) F, ∀ k ∈ congruenceSubgroup F n r,
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := by
  obtain ⟨r₀, A, hinv, hsupp⟩ := hΦ.exists_invariant
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F

  have key : ∀ X : Matrix (Fin n) (Fin n) F, Φ X ≠ 0 → ∀ k ∈ congruenceSubgroup F n (r₀ + A),
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := by
    intro X hX k hk
    obtain ⟨-, hk⟩ := (mem_congruenceSubgroup_iff F n).1 hk
    have ha : ∀ i j, ∃ a ∈ 𝒪[F], (k : Matrix (Fin n) (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j = (uniformizer F : F) ^ (r₀ + A) * a := by
      intro i j
      refine ⟨((k : Matrix (Fin n) (Fin n) F) i j - (1 : Matrix (Fin n) (Fin n) F) i j) /
        (uniformizer F : F) ^ (r₀ + A), ?_, by field_simp⟩
      rw [Valuation.mem_integer_iff, map_div₀, map_pow]
      exact div_le_one_of_le₀ (hk i j) zero_le
    choose a ha hka using ha
    have hXA := hsupp X hX
    have hY : ∀ i j, ∃ b ∈ 𝒪[F], (X * ((k : Matrix (Fin n) (Fin n) F) - 1)) i j =
        (uniformizer F : F) ^ r₀ * b := by
      intro i j
      refine ⟨∑ l, ((uniformizer F : F) ^ A * X i l) * a l j,
        Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hXA i l) (ha l j), ?_⟩
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.sub_apply, hka l j, pow_add]
      ring
    have := hinv X _ hY
    rwa [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel] at this
  refine ⟨r₀ + A, fun X k hk => ?_⟩
  by_cases hX : Φ X = 0
  · rw [hX]
    by_contra hne
    have h2 := key _ hne k⁻¹ (inv_mem hk)
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h2
    exact hne (h2.symm.trans hX)
  · exact key X hX k hk

section Unip

variable {α : Type*} [LinearOrder α] {β : Fin n → α} [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem continuous_unipMatrix :
    Continuous fun u : UnipotentIndex n β → F => unipMatrix F u := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : β i < β j
  · simp only [unipMatrix_apply_of_lt _ h]
    exact continuous_apply _
  · simp only [unipMatrix_apply_of_not_lt _ h]
    exact continuous_const

theorem integrable_add_unipMatrix (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔫.IsAddHaarMeasure]
    {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) {X : Matrix (Fin n) (Fin n) F}
    (hX : ∀ i j, β i ≠ β j → X i j = 0) :
    Integrable (fun u => Φ (X + unipMatrix F u)) μ𝔫 := by
  obtain ⟨r, A, -, hsupp⟩ := hΦ.exists_invariant
  refine Continuous.integrable_of_hasCompactSupport
    (hΦ.1.continuous.comp (continuous_const.add continuous_unipMatrix)) ?_
  refine HasCompactSupport.intro (K := Set.univ.pi fun _ => (LocalField.valBall F (-(A : ℤ)) : Set F))
    (isCompact_univ_pi fun _ => LocalField.isCompact_valBall _) fun u hu => ?_
  by_contra hne
  apply hu
  intro t _
  obtain ⟨⟨i, j⟩, h⟩ := t
  have h1 := hsupp _ hne i j
  rw [Matrix.add_apply, hX i j (ne_of_lt h), zero_add, unipMatrix_apply_of_lt _ h] at h1
  exact mem_valBall_neg_iff.2 h1

end Unip

section Cosets

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H]

theorem lintegral_eq_sum_coset (μ : Measure H) [μ.IsMulLeftInvariant] (L : Subgroup H)
    (hL : IsOpen (L : Set H)) [Fintype (H ⧸ L)] {u : H → ℝ≥0∞}
    (hu : ∀ h, ∀ l ∈ L, u (h * l) = u h) :
    ∫⁻ h, u h ∂μ = μ L * ∑ q : H ⧸ L, u q.out := by
  classical
  have hdec : ∀ h, u h = ∑ q : H ⧸ L, ((q.out • (L : Set H)).indicator fun _ => u q.out) h := by
    intro h
    rw [Finset.sum_eq_single (QuotientGroup.mk h : H ⧸ L)]
    · obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L h
      rw [Set.indicator_of_mem, hl, hu h l l.2]
      rw [hl]
      exact ⟨l⁻¹, inv_mem l.2, by simp [smul_eq_mul, mul_assoc]⟩
    · intro q _ hq
      rw [Set.indicator_of_notMem]
      rintro ⟨l, hl, rfl⟩
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (QuotientGroup.eq.2 (by simpa using hl)).symm
    · intro h'; exact absurd (Finset.mem_univ _) h'
  calc ∫⁻ h, u h ∂μ
      = ∫⁻ h, ∑ q : H ⧸ L, ((q.out • (L : Set H)).indicator fun _ => u q.out) h ∂μ :=
        lintegral_congr hdec
    _ = ∑ q : H ⧸ L, ∫⁻ h, ((q.out • (L : Set H)).indicator fun _ => u q.out) h ∂μ :=
        lintegral_finsetSum _ fun q _ => measurable_const.indicator (hL.smul _).measurableSet
    _ = ∑ q : H ⧸ L, u q.out * μ L := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [lintegral_indicator_const (hL.smul _).measurableSet, measure_smul]
    _ = μ L * ∑ q : H ⧸ L, u q.out := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => mul_comm _ _

end Cosets

section Main

variable {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem continuous_monoidHom_of_eq_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (χ : G →* ℝ≥0) (V : OpenSubgroup G) (hV : ∀ v ∈ V, χ v = 1) :
    Continuous χ := by
  refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg =>
    ⟨g • (V : Set G), ?_, V.isOpen.smul g, ⟨1, V.one_mem, mul_one g⟩⟩
  rintro _ ⟨v, hv, rfl⟩
  simp only [Set.mem_preimage, smul_eq_mul, map_mul, hV v hv, mul_one]
  exact hg

variable (β) in

def leviSqrtModular : levi F n β →* ℝ≥0 where
  toFun m := NNReal.sqrt (Measure.modularCharacter (leviIncl m))
  map_one' := by simp
  map_mul' a b := by simp [NNReal.sqrt_mul]

theorem coe_leviSqrtModular (m : levi F n β) :
    ((leviSqrtModular β m : ℝ≥0) : ℂ) = sqrtModular F n β (leviIncl m) := rfl

theorem continuous_leviSqrtModular : Continuous (leviSqrtModular (F := F) β) := by
  refine continuous_monoidHom_of_eq_one _
    ⟨(integralGL F n).subgroupOf (levi F n β), isOpen_subgroupOf_levi (isOpen_integralGL F n)⟩ ?_
  intro v hv
  show NNReal.sqrt (Measure.modularCharacter (leviIncl v)) = 1
  rw [modularCharacter_eq_one_of_mem_integralGL (leviIncl v) (Subgroup.mem_subgroupOf.1 hv)]
  simp

def inducedIntegrand (Φ : Matrix (Fin n) (Fin n) F → ℂ) (φ : GL (Fin n) F → W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (g : GL (Fin n) F) : ℂ :=
  Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓ (φ g)

omit [LinearOrder α] in
theorem continuous_inducedIntegrand {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    {φ : GL (Fin n) F → W} (hφ : ∃ K : Subgroup (GL (Fin n) F), IsOpen (K : Set (GL (Fin n) F)) ∧
      ∀ k ∈ K, ∀ g, φ (g * k) = φ g) (ℓ : Module.Dual ℂ W) (s : ℂ) :
    Continuous (inducedIntegrand Φ φ ℓ s) := by
  obtain ⟨K, hKo, hK⟩ := hφ
  have hℓφ : Continuous fun g => ℓ (φ g) := by
    refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨g • (K : Set (GL (Fin n) F)), ?_, hKo.smul g, ⟨1, one_mem _, mul_one g⟩⟩
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_preimage, smul_eq_mul, hK k hk]
    exact hg
  exact ((hΦ.1.continuous.comp Units.continuous_val).mul (continuous_detPow s)).mul hℓφ

theorem inducedIntegrand_parabolicMk_mul {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    {y : GL (Fin n) F} (hy : y ∈ integralGL F n) (m : levi F n β)
    (u : UnipotentIndex n β → F) :
    inducedIntegrand Φ φ ℓ s (((parabolicMk β m u : blockUpper F n β) : GL (Fin n) F) * y) =
      Φ ((((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
          (y : Matrix (Fin n) (Fin n) F)) *
        (detPow (m : GL (Fin n) F) s * (sqrtModular F n β (leviIncl m) * ℓ (σ m (φ y)))) := by
  have h1 := hφ.1 (parabolicMk β m u) y
  rw [inflateTwist_apply, ← sqrtModular_leviProj, leviProj_parabolicMk] at h1
  rw [inducedIntegrand, Units.val_mul, coe_parabolicMk, detPow_mul_of_mem_integralGL _ hy,
    detPow_parabolicMk, h1, map_smul, smul_eq_mul]
  ring

theorem enorm_ofReal_complex {r : ℝ} (hr : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]

theorem enorm_coe_nnreal (x : ℝ≥0) : ‖((x : ℝ) : ℂ)‖ₑ = (x : ℝ≥0∞) := by
  rw [enorm_ofReal_complex (NNReal.coe_nonneg x), ENNReal.ofReal_coe_nnreal]

variable [MeasurableSpace F] [BorelSpace F]

theorem lintegral_inducedIntegrand_mul (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure]
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    {y : GL (Fin n) F} (hy : y ∈ integralGL F n) :
    ∫⁻ p, ‖inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y)‖ₑ
        ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
      ∫⁻ m, ‖leviIntegrand σ (leviRatio β * leviSqrtModular β)
          (fun X => ∫ u, ((‖Φ ((X + unipMatrix F u) * (y : Matrix (Fin n) (Fin n) F))‖ : ℝ) : ℂ) ∂μ𝔫)
          (φ y) ℓ s m‖ₑ ∂(haarLevi β μ𝔪) := by
  have hcont := continuous_inducedIntegrand hΦ hφ.2 ℓ s
  have hmeas : Measurable fun p : blockUpper F n β =>
      ‖inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y)‖ₑ :=
    (hcont.comp (continuous_subtype_val.mul continuous_const)).enorm.measurable
  rw [lintegral_haarParabolic μ𝔪 μ𝔫 hmeas]
  refine lintegral_congr fun m => ?_
  have hΦy := hΦ.comp_mulRight y
  have hint := integrable_add_unipMatrix μ𝔫 hΦy (X := ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (mem_levi.1 m.2)
  have hmu : Measurable fun u : UnipotentIndex n β → F =>
      ‖Φ ((((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
        (y : Matrix (Fin n) (Fin n) F))‖ₑ :=
    (hΦy.1.continuous.comp (continuous_const.add continuous_unipMatrix)).enorm.measurable
  simp_rw [inducedIntegrand_parabolicMk_mul hφ ℓ s hy m, enorm_mul]
  rw [lintegral_mul_const _ hmu, ← ofReal_integral_norm_eq_lintegral_enorm hint]
  have hI : 0 ≤ ∫ u, ‖Φ ((((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
      (y : Matrix (Fin n) (Fin n) F))‖ ∂μ𝔫 := integral_nonneg fun _ => norm_nonneg _
  have hI' : (∫ u, ((‖Φ ((((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
      (y : Matrix (Fin n) (Fin n) F))‖ : ℝ) : ℂ) ∂μ𝔫) =
      ((∫ u, ‖Φ ((((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
      (y : Matrix (Fin n) (Fin n) F))‖ ∂μ𝔫 : ℝ) : ℂ) := integral_complex_ofReal
  simp only [leviIntegrand, enorm_mul, MonoidHom.mul_apply]
  rw [hI', enorm_ofReal_complex hI, enorm_coe_nnreal, ← coe_leviSqrtModular, enorm_coe_nnreal,
    ENNReal.coe_mul]
  ring

theorem integral_inducedIntegrand_mul (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure]
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    {y : GL (Fin n) F} (hy : y ∈ integralGL F n)
    (hint : Integrable (fun p : blockUpper F n β => inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y))
      (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))) :
    ∫ p, inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y)
        ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
      ∫ m, leviIntegrand σ (leviRatio β * leviSqrtModular β)
          (fun X => ∫ u, Φ ((X + unipMatrix F u) * (y : Matrix (Fin n) (Fin n) F)) ∂μ𝔫)
          (φ y) ℓ s m ∂(haarLevi β μ𝔪) := by
  rw [integral_haarParabolic μ𝔪 μ𝔫 hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
  simp only
  simp_rw [inducedIntegrand_parabolicMk_mul hφ ℓ s hy m]
  rw [integral_mul_const]
  simp only [leviIntegrand, MonoidHom.mul_apply, NNReal.coe_mul, Complex.ofReal_mul,
    coe_leviSqrtModular]
  ring

omit [MeasurableSpace F] [BorelSpace F] in

theorem lintegral_eq_sum_parabolic [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure]
    (μP : Measure (blockUpper F n β)) [μP.IsHaarMeasure]
    (μK : Measure (integralGL F n)) [μK.IsHaarMeasure] {r : ℕ}
    [Fintype (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n))]
    {h : GL (Fin n) F → ℝ≥0∞} (hh : Measurable h)
    (hr : ∀ g, ∀ k ∈ congruenceSubgroup F n r, h (g * k) = h g) :
    μG (integralGL F n) * (μK ((congruenceSubgroup F n r).subgroupOf (integralGL F n)) *
      ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
        ∫⁻ p, h ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) ∂μP) =
      μP (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK Set.univ *
        ∫⁻ g, h g ∂μG := by
  classical
  have : BorelSpace (integralGL F n) := Subtype.borelSpace _
  have hLo : IsOpen (((congruenceSubgroup F n r).subgroupOf (integralGL F n) : Subgroup (integralGL F n)) : Set (integralGL F n)) :=
    (isOpen_congruenceSubgroup F n r).preimage continuous_subtype_val
  rw [← Measures.lintegral_mul_prod_eq (blockUpper F n β) (integralGL F n)
    (Measures.isClosed_blockUpper F n β) (isOpen_integralGL F n) (isCompact_integralGL F n)
    (fun g => exists_blockUpper_mul_integralGL' g) μG μP μK hh]
  congr 1
  have hinner : ∀ p : blockUpper F n β, ∫⁻ k, h ((p : GL (Fin n) F) * k) ∂μK =
      μK ((congruenceSubgroup F n r).subgroupOf (integralGL F n)) * ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
        h ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) := fun p =>
    lintegral_eq_sum_coset μK _ hLo (u := fun k => h ((p : GL (Fin n) F) * k)) fun k l hl => by
      show h ((p : GL (Fin n) F) * ((k * l : integralGL F n) : GL (Fin n) F)) =
        h ((p : GL (Fin n) F) * (k : GL (Fin n) F))
      rw [Subgroup.coe_mul, ← mul_assoc]
      exact hr _ _ (Subgroup.mem_subgroupOf.1 hl)
  simp_rw [hinner]
  have hmeas : ∀ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n), Measurable fun p : blockUpper F n β =>
      h ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) := fun q =>
    hh.comp (continuous_subtype_val.mul continuous_const).measurable
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun q _ => hmeas q),
    lintegral_finsetSum _ fun q _ => hmeas q]

omit [MeasurableSpace F] [BorelSpace F] in

theorem integral_eq_sum_parabolic [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure]
    (μP : Measure (blockUpper F n β)) [μP.IsHaarMeasure]
    (μK : Measure (integralGL F n)) [μK.IsHaarMeasure] {r : ℕ}
    [Fintype (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n))]
    {f : GL (Fin n) F → ℂ} (hf : Integrable f μG)
    (hr : ∀ g, ∀ k ∈ congruenceSubgroup F n r, f (g * k) = f g)
    (hint : ∀ y ∈ integralGL F n,
      Integrable (fun p : blockUpper F n β => f ((p : GL (Fin n) F) * y)) μP) :
    μG.real (integralGL F n) •
      (μK.real ((congruenceSubgroup F n r).subgroupOf (integralGL F n) : Set (integralGL F n)) •
        ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
          ∫ p, f ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) ∂μP) =
      (μP.real (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK.real Set.univ) •
        ∫ g, f g ∂μG := by
  classical
  have : BorelSpace (integralGL F n) := Subtype.borelSpace _
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hLo : IsOpen (((congruenceSubgroup F n r).subgroupOf (integralGL F n) : Subgroup (integralGL F n)) : Set (integralGL F n)) :=
    (isOpen_congruenceSubgroup F n r).preimage continuous_subtype_val
  have hLc : IsCompact (((congruenceSubgroup F n r).subgroupOf (integralGL F n) : Subgroup (integralGL F n)) : Set (integralGL F n)) :=
    (Subgroup.isClosed_of_isOpen _ hLo).isCompact
  rw [← Measures.integral_mul_prod_eq (blockUpper F n β) (integralGL F n)
    (Measures.isClosed_blockUpper F n β) (isOpen_integralGL F n) (isCompact_integralGL F n)
    (fun g => exists_blockUpper_mul_integralGL' g) μG μP μK hf]
  congr 1
  have hinner : ∀ p : blockUpper F n β, ∫ k, f ((p : GL (Fin n) F) * k) ∂μK =
      μK.real (((congruenceSubgroup F n r).subgroupOf (integralGL F n) : Subgroup (integralGL F n)) : Set (integralGL F n)) •
        ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
        f ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) := by
    intro p
    have := integral_eq_smul_finsum_coset μK ⟨(congruenceSubgroup F n r).subgroupOf (integralGL F n), hLo⟩ hLc
      (f := fun k : integralGL F n => f ((p : GL (Fin n) F) * k))
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
      (fun k l hl => by
        show f ((p : GL (Fin n) F) * ((k * l : integralGL F n) : GL (Fin n) F)) =
          f ((p : GL (Fin n) F) * (k : GL (Fin n) F))
        rw [Subgroup.coe_mul, ← mul_assoc]
        exact hr _ _ (Subgroup.mem_subgroupOf.1 hl))
    rw [this, finsum_eq_sum_of_fintype]
    rfl
  simp_rw [hinner]
  rw [integral_smul, integral_finsetSum _ fun q _ => hint _ (q.out).2]

theorem sum_eval_div_pow {ι : Type*} [Fintype ι] (N : ι → ℕ) (P : ι → ℂ[X]) (κ : ℂ) {x : ℂ}
    (hx : x ≠ 0) :
    κ * ∑ i, (P i).eval x / x ^ N i =
      (C κ * ∑ i, P i * X ^ (∑ j, N j - N i)).eval x / x ^ (∑ j, N j) := by
  classical
  rw [eval_mul, eval_C, eval_finsetSum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : N i ≤ ∑ j, N j := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
  have hpow : x ^ (∑ j, N j) = x ^ (∑ j, N j - N i) * x ^ N i := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [eval_mul, eval_pow, eval_X, hpow]
  field_simp

end Main

variable {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

theorem exists_inducedZeta (hσ : IsSmooth σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧
      ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ →
        ∀ φ ∈ parabolicIndSpace F n β σ, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
          (∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
            Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓ (φ g)) μG) ∧
          ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
            D.eval (qs F s) * ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓ (φ g) ∂μG =
              P.eval (qs F s) / qs F s ^ N := by
  classical
  borelize F
  have : BorelSpace (levi F n β) := Subtype.borelSpace _
  have : BorelSpace (integralGL F n) := Subtype.borelSpace _
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  let μ𝔪 : Measure (LeviIndex n β → F) := Measure.addHaar
  let μ𝔫 : Measure (UnipotentIndex n β → F) := Measure.addHaar
  let μK : Measure (integralGL F n) := Measure.haar
  let θ : levi F n β →* ℝ≥0 := leviRatio β * leviSqrtModular β
  have hθ : Continuous θ := continuous_leviRatio.mul continuous_leviSqrtModular
  obtain ⟨s₀, D, hD0, hM⟩ := exists_leviZeta hσ hc θ hθ (haarLevi β μ𝔪)
  refine ⟨s₀, D, hD0, fun Φ hΦ φ hφ ℓ hℓ => ?_⟩

  obtain ⟨r₁, hr₁⟩ := hΦ.exists_mul_congruenceSubgroup
  obtain ⟨K', hK'o, hK'⟩ := hφ.2
  obtain ⟨r₂, -, hr₂⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hK'o.mem_nhds K'.one_mem)
  have hinv : ∀ s : ℂ, ∀ g, ∀ k ∈ congruenceSubgroup F n (max r₁ r₂),
      inducedIntegrand Φ φ ℓ s (g * k) = inducedIntegrand Φ φ ℓ s g := by
    intro s g k hk
    have hk₀ : k ∈ integralGL F n := congruenceSubgroup_le F n _ hk
    simp only [inducedIntegrand, Units.val_mul]
    rw [hr₁ _ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk),
      detPow_mul_of_mem_integralGL g hk₀,
      hK' k (hr₂ (congruenceSubgroup_antitone F n (le_max_right _ _) hk)) g]
  have : Finite (integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n)) :=
    Subgroup.quotient_finite_of_isOpen _
      ((isOpen_congruenceSubgroup F n _).preimage continuous_subtype_val)
  let _ := Fintype.ofFinite
    (integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n))

  let Q := integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n)
  let y : Q → GL (Fin n) F := fun q => ((q.out : integralGL F n) : GL (Fin n) F)
  have hy : ∀ q, y q ∈ integralGL F n := fun q => (q.out).2
  let Ψ : Q → Matrix (Fin n) (Fin n) F → ℂ := fun q X =>
    ∫ u, Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F)) ∂μ𝔫
  let Ψa : Q → Matrix (Fin n) (Fin n) F → ℂ := fun q X =>
    ∫ u, ((‖Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F))‖ : ℝ) : ℂ) ∂μ𝔫
  have hΨ : ∀ q, IsLeviSchwartz β (Ψ q) := fun q =>
    isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight (y q))
  have hΨa : ∀ q, IsLeviSchwartz β (Ψa q) := fun q =>
    isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight (y q)).norm
  choose N Pq hNP using fun q => (hM (Ψ q) (hΨ q) (φ (y q)) ℓ hℓ).2
  have hcont : ∀ s, Continuous (inducedIntegrand Φ φ ℓ s) := fun s =>
    continuous_inducedIntegrand hΦ hφ.2 ℓ s

  have hintP : ∀ s : ℂ, s₀ < s.re → ∀ z ∈ integralGL F n,
      Integrable (fun p : blockUpper F n β => inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * z))
        (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) := by
    intro s hs z hz
    have hΨz := isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight z).norm
    refine ⟨((hcont s).comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * z)‖ₑ
      ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) < ⊤
    rw [lintegral_inducedIntegrand_mul μ𝔪 μ𝔫 hΦ hφ ℓ s hz]
    exact ((hM _ hΨz (φ z) ℓ hℓ).1 s hs).2

  have hP0 : haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)
      (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) ≠ 0 :=
    ((isOpen_integralGL F n).preimage continuous_subtype_val).measure_ne_zero _
      ⟨1, by simp [one_mem]⟩
  have hK0 : μK Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μK Set.univ_nonempty

  have hintG : ∀ s : ℂ, s₀ < s.re → Integrable (inducedIntegrand Φ φ ℓ s) μG := by
    intro s hs
    refine ⟨(hcont s).aestronglyMeasurable, ?_⟩
    have hC := lintegral_eq_sum_parabolic (β := β) μG (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))
      μK (hcont s).enorm.measurable (fun g k hk => by rw [hinv s g k hk])
    have hlt : μG (integralGL F n) * (μK ((congruenceSubgroup F n (max r₁ r₂)).subgroupOf
        (integralGL F n)) * ∑ q : Q, ∫⁻ p, ‖inducedIntegrand Φ φ ℓ s
          ((p : GL (Fin n) F) * y q)‖ₑ ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))) < ⊤ :=
      ENNReal.mul_lt_top (isCompact_integralGL F n).measure_lt_top
        (ENNReal.mul_lt_top (measure_lt_top _ _)
          (ENNReal.sum_lt_top.2 fun q _ => (hintP s hs (y q) (hy q)).2))
    rw [hC] at hlt
    exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne (mul_ne_zero hP0 hK0)

  set κ : ℝ := (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)).real
      (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK.real Set.univ with hκ
  set κ' : ℝ := μG.real (integralGL F n) * μK.real ((congruenceSubgroup F n (max r₁ r₂)).subgroupOf
      (integralGL F n) : Set (integralGL F n)) with hκ'
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    have hPc : IsCompact (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F)) :
        Set (blockUpper F n β)) :=
      (Measures.isClosed_blockUpper F n β).isClosedEmbedding_subtypeVal.isCompact_preimage
        (isCompact_integralGL F n)
    exact mul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨hP0, hPc.measure_lt_top.ne⟩)
      (ENNReal.toReal_ne_zero.2 ⟨hK0, measure_ne_top _ _⟩)
  have hformula : ∀ s : ℂ, s₀ < s.re → ∫ g, inducedIntegrand Φ φ ℓ s g ∂μG =
      ((κ⁻¹ * κ' : ℝ) : ℂ) * ∑ q : Q, ∫ m, leviIntegrand σ θ (Ψ q) (φ (y q)) ℓ s m ∂(haarLevi β μ𝔪) := by
    intro s hs
    have hC := integral_eq_sum_parabolic (β := β) μG (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) μK
      (hintG s hs) (hinv s) (hintP s hs)
    have hB : ∀ q : Q, ∫ p, inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y q)
        ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
        ∫ m, leviIntegrand σ θ (Ψ q) (φ (y q)) ℓ s m ∂(haarLevi β μ𝔪) := fun q =>
      integral_inducedIntegrand_mul μ𝔪 μ𝔫 hφ ℓ s (hy q) (hintP s hs _ (hy q))
    rw [Finset.sum_congr rfl fun q _ => hB q] at hC
    rw [Complex.real_smul, Complex.real_smul, Complex.real_smul] at hC
    have hκC : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ0
    rw [← hκ, ← mul_assoc, ← Complex.ofReal_mul, ← hκ'] at hC
    push_cast
    field_simp
    linear_combination hC.symm
  refine ⟨hintG, ∑ q, N q, C ((κ⁻¹ * κ' : ℝ) : ℂ) * ∑ q, Pq q * X ^ (∑ j, N j - N q),
    fun s hs => ?_⟩
  show D.eval (qs F s) * ∫ g, inducedIntegrand Φ φ ℓ s g ∂μG = _
  rw [hformula s hs, mul_left_comm, Finset.mul_sum,
    Finset.sum_congr rfl fun q _ => hNP q s hs]
  exact sum_eval_div_pow N Pq _ (qs_ne_zero s)

end GodementJacquet

end GroundTheory.Automorphic
end
end
