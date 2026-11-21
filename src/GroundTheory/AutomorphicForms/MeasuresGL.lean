import Mathlib
import GroundTheory.AutomorphicForms.MeasuresModulus
import GroundTheory.AutomorphicForms.RealGroupsHaar
import GroundTheory.AutomorphicForms.Cartan

section
namespace GroundTheory.Automorphic

open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

namespace Measures

structure LinearChart (F : Type*) [Field F] [TopologicalSpace F] (ι : Type*) (G : Type*) [Mul G]
    [TopologicalSpace G] where

  toFun : G → ι → F
  isOpenEmbedding : IsOpenEmbedding toFun

  left : G → ((ι → F) ≃ₗ[F] (ι → F))

  right : G → ((ι → F) ≃ₗ[F] (ι → F))
  toFun_mul_left : ∀ g x, toFun (g * x) = left g (toFun x)
  toFun_mul_right : ∀ h x, toFun (x * h) = right h (toFun x)

namespace LinearChart

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] (C : LinearChart F ι G)

noncomputable def leftModulus (g : G) : ℝ≥0 := distribHaarChar (ι → F) (C.left g)

noncomputable def rightModulus (h : G) : ℝ≥0 := distribHaarChar (ι → F) (C.right h)

theorem leftModulus_pos (g : G) : 0 < C.leftModulus g := distribHaarChar_pos

theorem rightModulus_pos (h : G) : 0 < C.rightModulus h := distribHaarChar_pos

theorem measurableEmbedding : MeasurableEmbedding C.toFun :=
  C.isOpenEmbedding.measurableEmbedding

theorem image_preimage_mul_left (g : G) (s : Set G) :
    C.toFun '' ((g * ·) ⁻¹' s) = (C.left g)⁻¹ • (C.toFun '' s) := by
  rw [← Set.preimage_smul]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g * x, hx, (C.toFun_mul_left g x).trans rfl⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨g⁻¹ * z, by simpa using hz, ?_⟩
    apply (C.left g).injective
    rw [← C.toFun_mul_left, mul_inv_cancel_left, hzy]
    rfl

theorem image_preimage_mul_right (h : G) (s : Set G) :
    C.toFun '' ((· * h) ⁻¹' s) = (C.right h)⁻¹ • (C.toFun '' s) := by
  rw [← Set.preimage_smul]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x * h, hx, (C.toFun_mul_right h x).trans rfl⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z * h⁻¹, by simpa using hz, ?_⟩
    apply (C.right h).injective
    rw [← C.toFun_mul_right, inv_mul_cancel_right, hzy]
    rfl

variable (μ₀ : Measure (ι → F)) [μ₀.IsAddHaarMeasure]

theorem map_mul_left_comap (g : G) :
    map (g * ·) (μ₀.comap C.toFun) = (C.leftModulus g)⁻¹ • μ₀.comap C.toFun := by
  ext s hs
  rw [map_apply (continuous_const_mul g).measurable hs, C.measurableEmbedding.comap_apply,
    Measure.smul_apply, C.measurableEmbedding.comap_apply, image_preimage_mul_left,
    ← distribHaarChar_mul, map_inv, ENNReal.smul_def, smul_eq_mul]
  rfl

theorem map_mul_right_comap (h : G) :
    map (· * h) (μ₀.comap C.toFun) = (C.rightModulus h)⁻¹ • μ₀.comap C.toFun := by
  ext s hs
  rw [map_apply (continuous_mul_const h).measurable hs, C.measurableEmbedding.comap_apply,
    Measure.smul_apply, C.measurableEmbedding.comap_apply, image_preimage_mul_right,
    ← distribHaarChar_mul, map_inv, ENNReal.smul_def, smul_eq_mul]
  rfl

theorem comap_lt_top_of_isCompact {K : Set G} (hK : IsCompact K) : μ₀.comap C.toFun K < ∞ := by
  rw [C.measurableEmbedding.comap_apply]
  exact (hK.image C.isOpenEmbedding.continuous).measure_lt_top

theorem comap_pos_of_isOpen {U : Set G} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < μ₀.comap C.toFun U := by
  rw [C.measurableEmbedding.comap_apply]
  exact (C.isOpenEmbedding.isOpenMap U hU).measure_pos μ₀ (hne.image _)

variable [LocallyCompactSpace G]

theorem eq_of_smul_comap_eq {a b : ℝ≥0} (h : a • μ₀.comap C.toFun = b • μ₀.comap C.toFun) :
    a = b := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : 0 < μ₀.comap C.toFun K :=
    (C.comap_pos_of_isOpen μ₀ isOpen_interior ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).trans_le
      (measure_mono interior_subset)
  have h' := congrArg (fun ν : Measure G => ν K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h'
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj hpos.ne'
    (C.comap_lt_top_of_isCompact μ₀ hK).ne).1 h')

theorem leftModulus_mul (g h : G) : C.leftModulus (g * h) = C.leftModulus g * C.leftModulus h := by
  let μ₀ : Measure (ι → F) := addHaar
  have e1 := C.map_mul_left_comap μ₀ (g * h)
  have e2 : map ((g * h) * ·) (μ₀.comap C.toFun) =
      map (g * ·) (map (h * ·) (μ₀.comap C.toFun)) := by
    rw [map_map (continuous_const_mul g).measurable (continuous_const_mul h).measurable]
    congr 1
    funext x
    simp [mul_assoc]
  rw [e2, C.map_mul_left_comap μ₀ h, Measure.map_smul, C.map_mul_left_comap μ₀ g, smul_smul]
    at e1
  have := C.eq_of_smul_comap_eq μ₀ e1
  rw [← mul_inv] at this
  rw [mul_comm]
  exact inv_injective this.symm

theorem rightModulus_mul (g h : G) :
    C.rightModulus (g * h) = C.rightModulus g * C.rightModulus h := by
  let μ₀ : Measure (ι → F) := addHaar
  have e1 := C.map_mul_right_comap μ₀ (g * h)
  have e2 : map (· * (g * h)) (μ₀.comap C.toFun) =
      map (· * h) (map (· * g) (μ₀.comap C.toFun)) := by
    rw [map_map (continuous_mul_const h).measurable (continuous_mul_const g).measurable]
    congr 1
    funext x
    simp [mul_assoc]
  rw [e2, C.map_mul_right_comap μ₀ g, Measure.map_smul, C.map_mul_right_comap μ₀ h, smul_smul]
    at e1
  have := C.eq_of_smul_comap_eq μ₀ e1
  rw [← mul_inv] at this
  exact inv_injective this.symm

noncomputable def leftModulusHom : G →* ℝ≥0 where
  toFun := C.leftModulus
  map_one' := by
    have h := C.leftModulus_mul 1 1
    rw [one_mul] at h
    exact ((mul_eq_left₀ (C.leftModulus_pos 1).ne').1 h.symm)
  map_mul' := C.leftModulus_mul

noncomputable def rightModulusHom : G →* ℝ≥0 where
  toFun := C.rightModulus
  map_one' := by
    have h := C.rightModulus_mul 1 1
    rw [one_mul] at h
    exact ((mul_eq_left₀ (C.rightModulus_pos 1).ne').1 h.symm)
  map_mul' := C.rightModulus_mul

@[simp] theorem leftModulusHom_apply (g : G) : C.leftModulusHom g = C.leftModulus g := rfl

@[simp] theorem rightModulusHom_apply (g : G) : C.rightModulusHom g = C.rightModulus g := rfl

theorem leftModulus_eq_one_of_preimage {g : G} {s : Set G} (hs : MeasurableSet s)
    (hgs : (g * ·) ⁻¹' s = s) (h0 : μ₀.comap C.toFun s ≠ 0) (hT : μ₀.comap C.toFun s ≠ ∞) :
    C.leftModulus g = 1 := by
  have e := congrArg (fun ν : Measure G => ν s) (C.map_mul_left_comap μ₀ g)
  simp only [map_apply (continuous_const_mul g).measurable hs, hgs, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul] at e
  have : ((C.leftModulus g)⁻¹ : ℝ≥0) = 1 := by
    have := (ENNReal.mul_eq_right h0 hT).1 e.symm
    exact_mod_cast this
  exact inv_eq_one.1 this

theorem rightModulus_eq_one_of_preimage {h : G} {s : Set G} (hs : MeasurableSet s)
    (hhs : (· * h) ⁻¹' s = s) (h0 : μ₀.comap C.toFun s ≠ 0) (hT : μ₀.comap C.toFun s ≠ ∞) :
    C.rightModulus h = 1 := by
  have e := congrArg (fun ν : Measure G => ν s) (C.map_mul_right_comap μ₀ h)
  simp only [map_apply (continuous_mul_const h).measurable hs, hhs, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul] at e
  have : ((C.rightModulus h)⁻¹ : ℝ≥0) = 1 := by
    have := (ENNReal.mul_eq_right h0 hT).1 e.symm
    exact_mod_cast this
  exact inv_eq_one.1 this

theorem modulus_eq_one_of_mem {V : OpenSubgroup G} (hV : IsCompact (V : Set G)) {v : G}
    (hv : v ∈ V) : C.leftModulus v = 1 ∧ C.rightModulus v = 1 := by
  let μ₀ : Measure (ι → F) := addHaar
  have h0 : μ₀.comap C.toFun V ≠ 0 :=
    (C.comap_pos_of_isOpen μ₀ V.isOpen ⟨1, V.one_mem⟩).ne'
  have hT : μ₀.comap C.toFun V ≠ ∞ := (C.comap_lt_top_of_isCompact μ₀ hV).ne
  refine ⟨C.leftModulus_eq_one_of_preimage μ₀ V.isOpen.measurableSet ?_ h0 hT,
    C.rightModulus_eq_one_of_preimage μ₀ V.isOpen.measurableSet ?_ h0 hT⟩
  · ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact (V : Subgroup G).mul_mem_cancel_left hv
  · ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact (V : Subgroup G).mul_mem_cancel_right hv

theorem continuous_of_eq_one_on_openSubgroup (χ : G →* ℝ≥0) (V : OpenSubgroup G)
    (hV : ∀ v ∈ V, χ v = 1) : Continuous χ := by
  refine IsLocallyConstant.continuous fun s => isOpen_iff_forall_mem_open.2 fun g hg =>
    ⟨g • (V : Set G), ?_, V.isOpen.smul g, ⟨1, V.one_mem, mul_one g⟩⟩
  rintro _ ⟨v, hv, rfl⟩
  simp only [Set.mem_preimage, smul_eq_mul, map_mul, hV v hv, mul_one]
  exact hg

variable [T2Space G] [TotallyDisconnectedSpace G]

theorem continuous_leftModulus : Continuous C.leftModulus := by
  obtain ⟨V, hV⟩ := exists_compactOpenSubgroup (G := G)
  exact continuous_of_eq_one_on_openSubgroup C.leftModulusHom V fun v hv =>
    (C.modulus_eq_one_of_mem hV hv).1

theorem continuous_rightModulus : Continuous C.rightModulus := by
  obtain ⟨V, hV⟩ := exists_compactOpenSubgroup (G := G)
  exact continuous_of_eq_one_on_openSubgroup C.rightModulusHom V fun v hv =>
    (C.modulus_eq_one_of_mem hV hv).2

theorem continuous_density : Continuous fun g : G => (C.leftModulus g)⁻¹ :=
  C.continuous_leftModulus.inv₀ fun g => (C.leftModulus_pos g).ne'

theorem measurable_density : Measurable fun g : G => (((C.leftModulus g)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp C.continuous_density).measurable

noncomputable def haar : Measure G :=
  (μ₀.comap C.toFun).withDensity fun g => (((C.leftModulus g)⁻¹ : ℝ≥0) : ℝ≥0∞)

theorem map_withDensity_of_scale {X : Type*} [MeasurableSpace X] {T : X → X} (hT : Measurable T)
    {ν : Measure X} {ρ : X → ℝ≥0∞} (hρ : Measurable ρ) {a b : ℝ≥0} (hν : map T ν = a • ν)
    (hρT : ∀ x, ρ x = b * ρ (T x)) : map T (ν.withDensity ρ) = (a * b) • ν.withDensity ρ := by
  ext s hs
  rw [map_apply hT hs, withDensity_apply _ (hT hs), Measure.smul_apply, withDensity_apply _ hs,
    ← lintegral_indicator (hT hs), ← lintegral_indicator hs]
  have h1 : (T ⁻¹' s).indicator ρ = fun x => (b : ℝ≥0∞) * s.indicator ρ (T x) := by
    funext x
    by_cases hx : T x ∈ s
    · rw [indicator_of_mem (show x ∈ T ⁻¹' s from hx), indicator_of_mem hx, hρT]
    · rw [indicator_of_notMem (show x ∉ T ⁻¹' s from hx), indicator_of_notMem hx, mul_zero]
  rw [h1]
  show ∫⁻ x, (b : ℝ≥0∞) * s.indicator ρ (T x) ∂ν = _
  rw [lintegral_const_mul (f := fun x => s.indicator ρ (T x)) _ ((hρ.indicator hs).comp hT),
    ← lintegral_map (hρ.indicator hs) hT, hν, lintegral_smul_measure, ENNReal.smul_def,
    smul_eq_mul, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul]
  ring

instance isMulLeftInvariant_haar : (C.haar μ₀).IsMulLeftInvariant := ⟨fun g => by
  rw [haar, map_withDensity_of_scale (continuous_const_mul g).measurable C.measurable_density
    (C.map_mul_left_comap μ₀ g) (b := C.leftModulus g) fun x => ?_,
    inv_mul_cancel₀ (C.leftModulus_pos g).ne', one_smul]
  rw [← ENNReal.coe_mul, ENNReal.coe_inj, C.leftModulus_mul, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (C.leftModulus_pos g).ne', one_mul]⟩

theorem map_mul_right_haar (h : G) :
    map (· * h) (C.haar μ₀) = (C.leftModulus h / C.rightModulus h) • C.haar μ₀ := by
  rw [haar, map_withDensity_of_scale (continuous_mul_const h).measurable C.measurable_density
    (C.map_mul_right_comap μ₀ h) (b := C.leftModulus h) fun x => ?_, div_eq_mul_inv, mul_comm]
  rw [← ENNReal.coe_mul, ENNReal.coe_inj, C.leftModulus_mul, mul_inv, mul_comm, mul_assoc,
    inv_mul_cancel₀ (C.leftModulus_pos h).ne', mul_one]

instance isHaarMeasure_haar : (C.haar μ₀).IsHaarMeasure where
  lt_top_of_isCompact := fun K hK => by
    rw [haar, withDensity_apply _ hK.isClosed.measurableSet]
    exact setLIntegral_lt_top_of_isCompact (C.comap_lt_top_of_isCompact μ₀ hK).ne hK
      C.continuous_density
  map_mul_left_eq_self := (C.isMulLeftInvariant_haar μ₀).map_mul_left_eq_self
  open_pos := fun U hU hne => by
    rw [haar, ne_eq, withDensity_apply_eq_zero' C.measurable_density.aemeasurable]
    have e : {g | (((C.leftModulus g)⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0} ∩ U = U :=
      Set.inter_eq_right.2 fun g _ => by
        simpa using (C.leftModulus_pos g).ne'
    rw [e]
    exact (C.comap_pos_of_isOpen μ₀ hU hne).ne'

theorem modularCharacter_eq (h : G) :
    modularCharacter h = C.leftModulus h / C.rightModulus h := by
  let μ₀ : Measure (ι → F) := addHaar
  change modularCharacterFun h = _
  rw [modularCharacterFun_eq_haarScalarFactor (C.haar μ₀) h]
  simp only [C.map_mul_right_haar μ₀ h]
  rw [haarScalarFactor_smul, haarScalarFactor_self, smul_eq_mul, mul_one]

end LinearChart

end Measures

end GroundTheory.Automorphic
end

section
namespace GroundTheory.Automorphic

open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

namespace Measures

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

noncomputable def entries : Matrix (Fin n) (Fin n) F ≃ₗ[F] (Fin n × Fin n → F) :=
  ((LinearEquiv.curry F F (Fin n) (Fin n)).trans (Matrix.ofLinearEquiv F)).symm

@[simp] theorem entries_apply (A : Matrix (Fin n) (Fin n) F) (ij : Fin n × Fin n) :
    entries F n A ij = A ij.1 ij.2 :=
  rfl

@[simp] theorem entries_symm_apply (x : Fin n × Fin n → F) (i j : Fin n) :
    (entries F n).symm x i j = x (i, j) :=
  rfl

noncomputable def entriesHomeomorph : Matrix (Fin n) (Fin n) F ≃ₜ (Fin n × Fin n → F) where
  toEquiv := (entries F n).toEquiv
  continuous_toFun := continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) := by
  refine ⟨Units.isEmbedding_val_mk' (f := fun A => A⁻¹) ?_ fun u => (Matrix.coe_units_inv u).symm,
    ?_⟩
  · have hdet : ContinuousOn (fun A : Matrix (Fin n) (Fin n) F => (A.det)⁻¹) {x | IsUnit x} :=
      (continuous_id.matrix_det).continuousOn.inv₀ fun A hA =>
        ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    refine (hdet.smul (continuous_id.matrix_adjugate).continuousOn).congr fun A _ => ?_
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  · have : Set.range (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) =
        (fun A : Matrix (Fin n) (Fin n) F => A.det) ⁻¹' {0}ᶜ := by
      ext A
      simp only [Set.mem_range, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨u, rfl⟩
        exact ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).ne_zero
      · intro h
        exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h)).unit, rfl⟩
    rw [this]
    exact isOpen_compl_singleton.preimage (continuous_id.matrix_det)

noncomputable def glChart : LinearChart F (Fin n × Fin n) (GL (Fin n) F) where
  toFun g := entries F n g
  isOpenEmbedding := (entriesHomeomorph F n).isOpenEmbedding.comp (isOpenEmbedding_val F n)
  left g := (entries F n).symm.trans ((Units.mulLeftLinearEquiv F _ g).trans (entries F n))
  right g := (entries F n).symm.trans ((Units.mulRightLinearEquiv F g).trans (entries F n))
  toFun_mul_left g x := by simp
  toFun_mul_right h x := by simp

theorem glChart_apply (g : GL (Fin n) F) (ij : Fin n × Fin n) :
    (glChart F n).toFun g ij = (g : Matrix (Fin n) (Fin n) F) ij.1 ij.2 :=
  rfl

theorem glChart_leftModulus (g : GL (Fin n) F) :
    (glChart F n).leftModulus g = distribHaarChar F (Matrix.GeneralLinearGroup.det g) ^ n := by
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq, ← map_pow]
  congr 1
  ext
  rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply]
  have := LinearMap.det_conj (LinearMap.mulLeft F (g : Matrix (Fin n) (Fin n) F)) (entries F n)
  rw [det_mulLeft_matrix, Fintype.card_fin] at this
  exact this

theorem glChart_rightModulus (g : GL (Fin n) F) :
    (glChart F n).rightModulus g = distribHaarChar F (Matrix.GeneralLinearGroup.det g) ^ n := by
  rw [LinearChart.rightModulus, distribHaarChar_pi_eq, ← map_pow]
  congr 1
  ext
  rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply]
  have := LinearMap.det_conj (LinearMap.mulRight F (g : Matrix (Fin n) (Fin n) F)) (entries F n)
  rw [det_mulRight_matrix, Fintype.card_fin] at this
  exact this

theorem modularCharacter_GL : (modularCharacter : GL (Fin n) F →* ℝ≥0) = 1 := by
  ext g
  borelize F (GL (Fin n) F)
  rw [(glChart F n).modularCharacter_eq, glChart_leftModulus, glChart_rightModulus,
    div_self (pow_pos distribHaarChar_pos n).ne', MonoidHom.one_apply]

theorem isMulRightInvariant_GL [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : modularCharacterFun g = 1 := by
    change modularCharacter g = 1
    rw [modularCharacter_GL, MonoidHom.one_apply]
  rw [isMulLeftInvariant_eq_smul (map (· * g) μ) μ, ← modularCharacterFun_eq_haarScalarFactor,
    this, one_smul]

section DoubleCoset

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem measure_preimage_mk_finset (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) (O : Finset (G ⧸ K)) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' (O : Set (G ⧸ K))) = O.card * μ K := by
  have hpre : ∀ a : G, (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {(a : G ⧸ K)} = (a⁻¹ * ·) ⁻¹' K := by
    intro a
    ext b
    rw [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.eq, ← K.inv_mem_iff, mul_inv_rev,
      inv_inv]
    rfl
  rw [show (QuotientGroup.mk : G → G ⧸ K) ⁻¹' (O : Set (G ⧸ K)) =
      ⋃ y ∈ O, (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {y} by ext; simp, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (g := fun _ => μ K) fun x _ => ?_, Finset.sum_const, nsmul_eq_mul]
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hpre, measure_preimage_mul]
  · intro x _ y _ hxy
    exact Set.disjoint_left.2 fun b hx hy => hxy (hx.symm.trans hy)
  · intro x _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hpre]
    exact (hK.preimage (continuous_const_mul _)).measurableSet

theorem mem_map_conj_iff {K : Subgroup G} {g k : G} :
    k ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * k * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem measure_doubleCoset (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (g : G) :
    μ (doubleCoset g (K : Set G) K) =
      ((K.map (MulAut.conj g).toMonoidHom).relIndex K : ℝ≥0∞) * μ K := by
  set H := K.map (MulAut.conj g).toMonoidHom with hH
  let O : Set (G ⧸ K) := MulAction.orbit K (g : G ⧸ K)
  have hstab : MulAction.stabilizer K (g : G ⧸ K) = H.subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_map_conj_iff]
    show ((k : G) • ((g : G) : G ⧸ K)) = ((g : G) : G ⧸ K) ↔ _
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul,
      show ((k : G) * g)⁻¹ * g = (g⁻¹ * k * g)⁻¹ by group, K.inv_mem_iff]
  have hdc : doubleCoset g (K : Set G) K = (QuotientGroup.mk : G → G ⧸ K) ⁻¹' O := by
    ext x
    rw [mem_doubleCoset, Set.mem_preimage, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
      refine ⟨⟨k₁, hk₁⟩, ?_⟩
      show ((k₁ : G) • ((g : G) : G ⧸ K)) = _
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simpa [mul_assoc] using hk₂
    · rintro ⟨k, hk⟩
      change ((k : G) • ((g : G) : G ⧸ K)) = _ at hk
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hk
      exact ⟨k, k.2, (k * g)⁻¹ * x, hk, by group⟩
  have hcK : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hopen : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) := by
    have : IsOpen (H : Set G) := by
      have e : (H : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' K := by
        ext x
        exact mem_map_conj_iff
      rw [e]
      exact hKo.preimage (by fun_prop)
    exact this.preimage continuous_subtype_val
  have hfin : Finite (K ⧸ H.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  have hOfin : O.Finite := by
    have : Finite O := by
      rw [← hstab] at hfin
      exact Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer K (g : G ⧸ K)).symm
    exact Set.toFinite O
  have hcard : hOfin.toFinset.card = H.relIndex K := by
    rw [← Nat.card_eq_card_finite_toFinset, Subgroup.relIndex, Subgroup.index, ← hstab]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer K (g : G ⧸ K))
  rw [hdc, ← hOfin.coe_toFinset, measure_preimage_mk_finset μ hKo, hcard]

end DoubleCoset


theorem inv_eq_self_GL [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.inv = μ := by
  have := isMulRightInvariant_GL F n μ
  set K := GLnLocal.integralGL F n
  have hK0 : μ K ≠ 0 := (GLnLocal.isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ∞ := (GLnLocal.isCompact_integralGL F n).measure_lt_top.ne
  have e := isMulLeftInvariant_eq_smul μ.inv μ
  have hc : haarScalarFactor μ.inv μ = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e
    simp only [Measure.inv_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have hKinv : (K : Set (GL (Fin n) F))⁻¹ = K := by
      ext x
      simp
    rw [hKinv] at h
    have := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    exact_mod_cast this
  rw [e, hc, one_smul]



variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

noncomputable def haarGL (μ₀ : Measure (Fin n × Fin n → F)) : Measure (GL (Fin n) F) :=
  (glChart F n).haar μ₀

variable (μ₀ : Measure (Fin n × Fin n → F)) [μ₀.IsAddHaarMeasure]

theorem haarGL_eq :
    haarGL F n μ₀ = (μ₀.comap fun (g : GL (Fin n) F) (ij : Fin n × Fin n) =>
      (g : Matrix (Fin n) (Fin n) F) ij.1 ij.2).withDensity
        fun g => (((distribHaarChar F (Matrix.GeneralLinearGroup.det g) ^ n)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [haarGL, LinearChart.haar]
  congr 1
  funext g
  rw [glChart_leftModulus]

instance isHaarMeasure_haarGL : (haarGL F n μ₀).IsHaarMeasure :=
  LinearChart.isHaarMeasure_haar _ μ₀

instance isMulRightInvariant_haarGL : (haarGL F n μ₀).IsMulRightInvariant :=
  isMulRightInvariant_GL F n _

theorem eq_smul_haarGL (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    μ = haarScalarFactor μ (haarGL F n μ₀) • haarGL F n μ₀ :=
  isMulLeftInvariant_eq_smul μ _

end Measures

end GroundTheory.Automorphic
end
