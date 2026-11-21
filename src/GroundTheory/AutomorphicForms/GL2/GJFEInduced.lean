import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEDefs

section
noncomputable section

namespace GroundTheory.Automorphic

namespace Measures

namespace LinearChart

open MeasureTheory Measure Set
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (C : LinearChart F ι G) (μ₀ : Measure (ι → F)) [μ₀.IsAddHaarMeasure]

theorem map_mul_right_haar_modular (h : G) :
    map (· * h) (C.haar μ₀) = modularCharacter h • C.haar μ₀ := by
  rw [C.map_mul_right_haar μ₀ h, C.modularCharacter_eq h]

include C in

theorem continuous_modularCharacter : Continuous (modularCharacter : G → ℝ≥0) := by
  have : (modularCharacter : G → ℝ≥0) = fun g => C.leftModulus g * (C.rightModulus g)⁻¹ := by
    funext g
    rw [C.modularCharacter_eq, div_eq_mul_inv]
  rw [this]
  exact C.continuous_leftModulus.mul
    (C.continuous_rightModulus.inv₀ fun g => (C.rightModulus_pos g).ne')

include C in
theorem measurable_modularCharacter :
    Measurable fun g : G => ((modularCharacter g : ℝ≥0) : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp (continuous_modularCharacter C)).measurable

theorem lintegral_mul_right_haar (h : G) {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (x * h) ∂C.haar μ₀ = modularCharacter h * ∫⁻ x, f x ∂C.haar μ₀ := by
  rw [← lintegral_map hf (measurable_mul_const h), C.map_mul_right_haar_modular,
    lintegral_smul_measure]
  rfl

include C in

theorem modularCharacter_eq_one_of_mem {V : OpenSubgroup G} (hV : IsCompact (V : Set G)) {v : G}
    (hv : v ∈ V) : modularCharacter v = 1 := by
  obtain ⟨h1, h2⟩ := C.modulus_eq_one_of_mem hV hv
  rw [C.modularCharacter_eq, h1, h2, div_one]

variable [SecondCountableTopology G]

theorem map_inv_withDensity_haar :
    map (·⁻¹) ((C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞)) = C.haar μ₀ := by
  set μ := C.haar μ₀ with hμ
  set Δ : G → ℝ≥0∞ := fun x => (modularCharacter x : ℝ≥0∞) with hΔ
  have hΔm : Measurable Δ := (measurable_modularCharacter C)
  set ν := map (·⁻¹) (μ.withDensity Δ) with hνdef
  have hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ x, f x⁻¹ * Δ x ∂μ := by
    intro f hf
    rw [hνdef, lintegral_map hf measurable_inv]
    have := lintegral_withDensity_eq_lintegral_mul μ hΔm (hf.comp measurable_inv)
    simp only [Function.comp_def, Pi.mul_apply] at this
    rw [this]
    congr 1
    funext x
    ring

  have hleft : ∀ g : G, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (g * x) ∂ν = ∫⁻ x, f x ∂ν := by
    intro g f hf
    rw [hν (fun x => f (g * x)) (hf.comp (measurable_const_mul g)), hν f hf]
    set L : G → ℝ≥0∞ := fun y => f y⁻¹ * Δ y with hLdef
    have hL : Measurable L := (hf.comp measurable_inv).mul hΔm
    have key : (fun x => f (g * x⁻¹) * Δ x) =
        fun x => (modularCharacter g : ℝ≥0∞) * L (x * g⁻¹) := by
      funext x
      have h1 : (x * g⁻¹)⁻¹ = g * x⁻¹ := by group
      have h2 : Δ x = (modularCharacter (x * g⁻¹) : ℝ≥0∞) * modularCharacter g := by
        rw [hΔ, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel_right]
      simp only [hLdef, h1, h2]
      ring
    show ∫⁻ x, f (g * x⁻¹) * Δ x ∂μ = ∫⁻ x, L x ∂μ
    rw [key, lintegral_const_mul (f := fun x => L (x * g⁻¹)) _ (hL.comp (measurable_mul_const _)),
      C.lintegral_mul_right_haar μ₀ g⁻¹ hL, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul,
      mul_inv_cancel, map_one, ENNReal.coe_one, one_mul]
  have hinv : ν.IsMulLeftInvariant := ⟨fun g => by
    ext s hs
    rw [map_apply (measurable_const_mul g) hs, ← lintegral_indicator_one hs,
      ← lintegral_indicator_one (measurable_const_mul g hs)]
    exact hleft g (s.indicator 1) (measurable_one.indicator hs)⟩
  have hfin : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    rw [hνdef, map_apply measurable_inv hK.isClosed.measurableSet,
      withDensity_apply _ (measurable_inv hK.isClosed.measurableSet)]
    have hK' : IsCompact ((·⁻¹) ⁻¹' K : Set G) := by
      rw [Set.inv_preimage]
      exact hK.inv
    exact setLIntegral_lt_top_of_isCompact (hK'.measure_lt_top).ne hK'
      (continuous_modularCharacter C)⟩
  have hsmul := isMulLeftInvariant_eq_smul ν μ
  obtain ⟨V, hV⟩ := exists_compactOpenSubgroup (G := G)
  have hVm : MeasurableSet (V : Set G) := V.isOpen.measurableSet
  have hVinv : ((·⁻¹) ⁻¹' (V : Set G) : Set G) = V := by
    ext x
    simp
  have hνV : ν V = μ V := by
    rw [hνdef, map_apply measurable_inv hVm, withDensity_apply _ (measurable_inv hVm), hVinv]
    rw [setLIntegral_congr_fun hVm (g := fun _ => (1 : ℝ≥0∞)) fun x hx => by
      simp [hΔ, modularCharacter_eq_one_of_mem C hV hx]]
    simp
  have hμV0 : μ V ≠ 0 := V.isOpen.measure_ne_zero μ ⟨1, V.one_mem⟩
  have hμVt : μ V ≠ ∞ := hV.measure_lt_top.ne
  have hc : haarScalarFactor ν μ = 1 := by
    have := congrArg (fun m : Measure G => m V) hsmul
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    rw [hνV] at this
    have h1 : (haarScalarFactor ν μ : ℝ≥0∞) * μ V = 1 * μ V := by rw [one_mul, ← this]
    exact_mod_cast (ENNReal.mul_left_inj hμV0 hμVt).1 h1
  rw [hsmul, hc, one_smul]

theorem lintegral_inv_haar {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x⁻¹ ∂C.haar μ₀ = ∫⁻ x, (modularCharacter x : ℝ≥0∞) * f x ∂C.haar μ₀ := by
  conv_lhs => rw [← C.map_inv_withDensity_haar μ₀]
  have h1 := lintegral_map (μ := (C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞))
    (f := fun x => f x⁻¹) (hf.comp measurable_inv) measurable_inv
  have h2 := lintegral_withDensity_eq_lintegral_mul (C.haar μ₀) (measurable_modularCharacter C) hf
  simp only [inv_inv] at h1
  rw [h1, h2]
  rfl

theorem integral_inv_haar {f : G → ℂ} (hf : Continuous f) :
    ∫ x, f x⁻¹ ∂C.haar μ₀ = ∫ x, (modularCharacter x : ℂ) * f x ∂C.haar μ₀ := by
  conv_lhs => rw [← C.map_inv_withDensity_haar μ₀]
  have h1 := integral_map (μ := (C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞))
    (φ := fun x : G => x⁻¹) (f := fun x => f x⁻¹) measurable_inv.aemeasurable
    (hf.comp continuous_inv).aestronglyMeasurable
  simp only [inv_inv] at h1
  rw [h1, integral_withDensity_eq_integral_smul (continuous_modularCharacter C).measurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Complex.real_smul]

end LinearChart

end Measures

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Measures MeasureTheory
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] in

theorem det_eq_prod_of_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → F) ≃ₗ[F] (ι → F)) (c : ι → F) (h : ∀ x s, L x s = c s * x s) :
    (LinearEquiv.det L : F) = ∏ s, c s := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  have : LinearMap.toMatrix' (L : (ι → F) →ₗ[F] (ι → F)) = Matrix.diagonal c := by
    ext s t
    rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, h, Matrix.diagonal_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [this, Matrix.det_diagonal]

omit [MeasurableSpace F] [BorelSpace F] in

theorem modulus_prod {ι : Type*} (s : Finset ι) (f : ι → F) :
    LocalField.modulus (∏ i ∈ s, f i) = ∏ i ∈ s, LocalField.modulus (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LocalField.modulus_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, LocalField.modulus_mul, ih]

theorem distribHaarChar_pi_eq_modulus {ι : Type*} [Fintype ι] [DecidableEq ι] (L : (ι → F) ≃ₗ[F] (ι → F)) :
    (distribHaarChar (ι → F) L : ℝ≥0) = LocalField.modulus (LinearEquiv.det L : F) := by
  rw [distribHaarChar_pi_eq, GroundTheory.LocalField.distribHaarChar_eq_modulus]

variable (β) in

abbrev leviDiag (μ : Fin n → ℤ) : levi F n β := ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩

theorem leviChart_leftModulus_diag (μ : Fin n → ℤ) :
    (leviChart β).leftModulus (leviDiag (F := F) β μ) =
      ∏ s : LeviIndex n β, LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) := by
  classical
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq_modulus,
    det_eq_prod_of_apply _ (fun s => (uniformizer F : F) ^ μ s.1.1), modulus_prod]
  intro x s
  show (((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((leviCoord F n β).symm x : lieLevi F n β) : Matrix (Fin n) (Fin n) F)) s.1.1 s.1.2 = _
  rw [Cartan.coe_diagPow, Matrix.diagonal_mul]
  congr 1
  simp [leviCoord, s.2]

theorem parabolicChart_leftModulus_diag (μ : Fin n → ℤ) :
    (parabolicChart F n β).leftModulus (leviIncl (leviDiag (F := F) β μ)) =
      ∏ s : ParabolicIndex n β, LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) := by
  classical
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq_modulus,
    det_eq_prod_of_apply _ (fun s => (uniformizer F : F) ^ μ s.1.1), modulus_prod]
  intro x s
  show (((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((parabolicCoord F n β).symm x : lieParabolic F n β) : Matrix (Fin n) (Fin n) F)) s.1.1 s.1.2 = _
  rw [Cartan.coe_diagPow, Matrix.diagonal_mul]
  congr 1
  simp [parabolicCoord, s.2]

theorem localField_modulus_eq_modulus {x : F} (hx : x ≠ 0) :
    LocalField.modulus x = Measures.modulus x := by
  rw [show x = ((Units.mk0 x hx : Fˣ) : F) from rfl, Measures.modulus_units,
    GroundTheory.LocalField.distribHaarChar_eq_modulus]

theorem modularCharacter_leviDiag (μ : Fin n → ℤ) :
    Measure.modularCharacter (leviIncl (leviDiag (F := F) β μ)) =
      ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2},
        LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) /
          LocalField.modulus ((uniformizer F : F) ^ μ s.1.2) := by
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  rw [modularCharacter_blockUpper_of_mem_borel' _ (diagPow_mem_borel μ)]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [leviIncl_coe, Cartan.coe_diagPow, Matrix.diagonal_apply_eq]
  rw [localField_modulus_eq_modulus (zpow_ne_zero _ hϖ),
    localField_modulus_eq_modulus (zpow_ne_zero _ hϖ)]

omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_det_diagPow (μ : Fin n → ℤ) :
    LocalField.modulus ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      ∏ i, LocalField.modulus ((uniformizer F : F) ^ μ i) := by
  rw [Cartan.coe_diagPow, Matrix.det_diagonal, modulus_prod]

omit [MeasurableSpace F] [BorelSpace F] in

theorem prod_leviIndex_eq (f : Fin n → ℝ≥0) :
    ∏ s : LeviIndex n β, f s.1.1 = ∏ i, f i ^ blockSize β (blockOf β i) := by
  classical
  rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 = β ij.2)
    (by simp) (fun ij => f ij.1), Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [blockSize, Fintype.card_subtype]
  congr 1
  ext j
  simp [blockOf, Set.rangeFactorization, Subtype.ext_iff, eq_comm]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviModulus_diag (μ : Fin n → ℤ) :
    leviModulus β (leviDiag (F := F) β μ) =
      ∏ s : LeviIndex n β, LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) := by
  classical
  have hblock : ∀ a, ((leviBlock F (leviDiag (F := F) β μ) a : GL (Fiber β a) F) :
      Matrix (Fiber β a) (Fiber β a) F).det = ∏ i : Fiber β a, (uniformizer F : F) ^ μ i.1 := by
    intro a
    rw [coe_leviBlock]
    have : blocks β F ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a =
        Matrix.diagonal fun i : Fiber β a => (uniformizer F : F) ^ μ i.1 := by
      ext i j
      simp only [blocks, Cartan.coe_diagPow, Matrix.diagonal_apply, Subtype.ext_iff]
    rw [this, Matrix.det_diagonal]
  rw [leviModulus, prod_leviIndex_eq (β := β) fun i => LocalField.modulus ((uniformizer F : F) ^ μ i)]
  simp_rw [hblock, modulus_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_fiberwise (blockOf β) fun i =>
    LocalField.modulus ((uniformizer F : F) ^ μ i) ^ blockSize β (blockOf β i)]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun i _ => ?_
  rw [i.2]

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] in
theorem prod_subtype_eq_ite {M : Type*} [CommMonoid M] (P : Fin n × Fin n → Prop) [DecidablePred P]
    (g : Fin n × Fin n → M) :
    ∏ s : {ij : Fin n × Fin n // P ij}, g s.1 = ∏ ij, if P ij then g ij else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype (Finset.univ.filter P) (by simp) g).symm

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] in

theorem prod_identity (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≠ 0) :
    ((∏ s : LeviIndex n β, t s.1.1) / ∏ s : ParabolicIndex n β, t s.1.1) ^ 2 *
      (∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2}, t s.1.1 / t s.1.2) * (∏ i, t i) ^ n =
      ∏ s : LeviIndex n β, t s.1.1 := by
  classical
  set A := ∏ ij : Fin n × Fin n, if β ij.1 = β ij.2 then t ij.1 else 1 with hAdef
  set U := ∏ ij : Fin n × Fin n, if β ij.1 < β ij.2 then t ij.1 else 1 with hUdef
  set L := ∏ ij : Fin n × Fin n, if β ij.2 < β ij.1 then t ij.1 else 1 with hLdef
  have hA : ∏ s : LeviIndex n β, t s.1.1 = A :=
    prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 = β ij.2) fun ij => t ij.1
  have hP : ∏ s : ParabolicIndex n β, t s.1.1 = A * U := by
    rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => ¬ β ij.2 < β ij.1) fun ij => t ij.1,
      hAdef, hUdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ij _ => ?_
    rcases lt_trichotomy (β ij.1) (β ij.2) with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  have hU : ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2}, t s.1.1 / t s.1.2 = U / L := by
    rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2) fun ij => t ij.1 / t ij.2]
    have hswap : L = ∏ ij : Fin n × Fin n, if β ij.1 < β ij.2 then t ij.2 else 1 :=
      Fintype.prod_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _ fun ij => rfl
    rw [hswap, hUdef, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun ij _ => ?_
    split_ifs <;> simp
  have hall : (∏ i, t i) ^ n = A * U * L := by
    have : (∏ i, t i) ^ n = ∏ ij : Fin n × Fin n, t ij.1 := by
      rw [Fintype.prod_prod_type, ← Finset.prod_pow]
      simp
    rw [this, hAdef, hUdef, hLdef, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ij _ => ?_
    rcases lt_trichotomy (β ij.1) (β ij.2) with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  have hne : ∀ P : Fin n × Fin n → Prop, ∀ [DecidablePred P],
      (∏ ij : Fin n × Fin n, if P ij then t ij.1 else 1) ≠ 0 := fun P _ =>
    Finset.prod_ne_zero_iff.2 fun ij _ => by split_ifs <;> simp [ht]
  have hA0 : A ≠ 0 := hne _
  have hU0 : U ≠ 0 := hne _
  have hL0 : L ≠ 0 := hne _
  rw [hA, hP, hU, hall]
  field_simp

variable (β) in

def leviAbsDet : levi F n β →* ℝ≥0 where
  toFun m := LocalField.modulus (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det)
  map_one' := by simp [LocalField.modulus_one]
  map_mul' m m' := by simp [Matrix.det_mul, LocalField.modulus_mul]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviAbsDet_apply (m : levi F n β) :
    leviAbsDet β m = LocalField.modulus (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det) :=
  rfl

variable (β) in

def leviModulusHom : levi F n β →* ℝ≥0 where
  toFun := leviModulus β
  map_one' := by
    simp only [leviModulus]
    refine Finset.prod_eq_one fun a _ => ?_
    rw [coe_leviBlock, OneMemClass.coe_one, Units.val_one, blocks_one, Matrix.det_one,
      LocalField.modulus_one, one_pow]
  map_mul' m m' := by
    simp only [leviModulus, leviBlock_mul, Units.val_mul, Matrix.det_mul, LocalField.modulus_mul,
      mul_pow, Finset.prod_mul_distrib]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviModulusHom_apply (m : levi F n β) : leviModulusHom β m = leviModulus β m := rfl

omit [MeasurableSpace F] [BorelSpace F] in

theorem modulus_eq_one_of_ord {x : F} (hx : x ≠ 0) (h : LocalField.ord x = 0) :
    LocalField.modulus x = 1 :=
  LocalField.modulus_eq_one_iff.2 ⟨hx, h⟩

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviAbsDet_of_mem_integralGL {k : levi F n β}
    (hk : (k : GL (Fin n) F) ∈ integralGL F n) : leviAbsDet β k = 1 :=
  modulus_eq_one_of_ord (det_ne_zero _) (ordDet_of_mem_integralGL hk)

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviModulus_of_mem_integralGL {k : levi F n β}
    (hk : (k : GL (Fin n) F) ∈ integralGL F n) : leviModulus β k = 1 := by
  refine Finset.prod_eq_one fun a _ => ?_
  rw [modulus_eq_one_of_ord (det_ne_zero_of_GL _) (blockOrd_of_mem_integralGL a hk), one_pow]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviRatio_of_mem_integralGL {k : levi F n β}
    (hk : (k : GL (Fin n) F) ∈ integralGL F n) : leviRatio β k = 1 :=
  eq_one_of_mem_compact (leviRatio β) continuous_leviRatio (isCompact_leviIntegral (F := F))
    (Subgroup.mem_subgroupOf.2 hk)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

theorem hom_cartan (f : levi F n β →* ℝ≥0)
    (hf : ∀ k : levi F n β, (k : GL (Fin n) F) ∈ integralGL F n → f k = 1) {k₁ k₂ : levi F n β}
    (h₁ : (k₁ : GL (Fin n) F) ∈ integralGL F n) (h₂ : (k₂ : GL (Fin n) F) ∈ integralGL F n)
    (d : levi F n β) : f (k₁ * d * k₂) = f d := by
  rw [map_mul, map_mul, hf k₁ h₁, hf k₂ h₂, one_mul, mul_one]

theorem leviRatio_sq_mul_modular_mul_det (m : levi F n β) :
    leviRatio β m ^ 2 * Measure.modularCharacter (leviIncl m) * leviAbsDet β m ^ n =
      leviModulus β m := by
  obtain ⟨μ, k₁, hk₁, k₂, hk₂, hm⟩ := exists_eq_mul_diagPow_mul_levi m.2
  have e : m = ⟨k₁, hk₁.1⟩ * leviDiag (F := F) β μ * ⟨k₂, hk₂.1⟩ := Subtype.ext hm
  have h1 := hom_cartan (leviRatio β) (fun k hk => leviRatio_of_mem_integralGL hk) (k₁ := ⟨k₁, hk₁.1⟩)
    (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  have h2 := hom_cartan (Measure.modularCharacter.comp leviIncl)
    (fun k hk => modularCharacter_eq_one_of_mem_integralGL _ hk) (k₁ := ⟨k₁, hk₁.1⟩)
    (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  have h3 := hom_cartan (leviAbsDet β) (fun k hk => leviAbsDet_of_mem_integralGL hk) (k₁ := ⟨k₁, hk₁.1⟩)
    (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  have h4 := hom_cartan (leviModulusHom β) (fun k hk => leviModulus_of_mem_integralGL hk)
    (k₁ := ⟨k₁, hk₁.1⟩) (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  simp only [MonoidHom.coe_comp, Function.comp_apply, leviModulusHom_apply] at h2 h4
  rw [e, h1, h2, h3, h4, leviRatio_apply, leviChart_leftModulus_diag,
    parabolicChart_leftModulus_diag, modularCharacter_leviDiag, leviAbsDet_apply,
    modulus_det_diagPow, leviModulus_diag]
  exact prod_identity (fun i => LocalField.modulus ((uniformizer F : F) ^ μ i)) fun i =>
    LocalField.modulus_ne_zero (zpow_ne_zero _ (Cartan.uniformizer_ne_zero F))

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Measures MeasureTheory GJMatrix
open scoped NNReal
open ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

def matrixTensor (g : Fin n × Fin n → F → ℂ) (X : Matrix (Fin n) (Fin n) F) : ℂ :=
  ∏ ij : Fin n × Fin n, g ij (X ij.1 ij.2)

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem matrixTensor_norm (g : Fin n × Fin n → F → ℂ) (X : Matrix (Fin n) (Fin n) F) :
    matrixTensor (fun ij x => ((‖g ij x‖ : ℝ) : ℂ)) X = ((‖matrixTensor g X‖ : ℝ) : ℂ) := by
  simp [matrixTensor, norm_prod]

theorem mem_span_matrixTensor {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    Φ ∈ Submodule.span ℂ (Set.range fun p : ℤ × (Fin n × Fin n → F) =>
      matrixTensor fun ij => cosetInd (LocalField.valBall F p.1) (p.2 ij)) := by
  have h := (isSchwartzBruhat_iff_comp_symm Φ).1 hΦ
  rw [localSchwartzBruhatPi_eq_span] at h
  let L : ((Fin n × Fin n → F) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin n) F → ℂ) :=
    LinearMap.funLeft ℂ ℂ (matrixCoordHomeomorph (Fin n) F)
  have hm := Submodule.mem_map_of_mem (f := L) h
  rw [Submodule.map_span, ← Set.range_comp] at hm
  have e1 : L (Φ ∘ (matrixCoordHomeomorph (Fin n) F).symm) = Φ := by
    funext X
    simp [L, LinearMap.funLeft_apply]
  have e2 : (⇑L ∘ fun p : ℤ × (Fin n × Fin n → F) =>
      localTensor fun i => cosetInd (LocalField.valBall F p.1) (p.2 i)) =
      fun p => matrixTensor fun ij => cosetInd (LocalField.valBall F p.1) (p.2 ij) := by
    funext p X
    rfl
  rw [e1, e2] at hm
  exact hm

section Unip

variable [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)

variable (β) in

def unipMeasure : Measure (UnipotentIndex n β → F) :=
  Measure.pi fun _ => LocalField.selfDualMeasure ψ

instance : (unipMeasure β ψ).IsAddHaarMeasure := by
  unfold unipMeasure
  infer_instance

variable (β) in

def tensorConst (g : Fin n × Fin n → F → ℂ) : ℂ :=
  (∏ s : UnipotentIndex n β,
    LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g s.1) 0) *
      ∏ ij : Fin n × Fin n, if β ij.2 < β ij.1 then g ij 0 else 1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] in

theorem prod_not_unip_eq {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0)
    (g : Fin n × Fin n → F → ℂ) :
    ∏ s : {ij : Fin n × Fin n // ¬ β ij.1 < β ij.2}, g s.1 (X s.1.1 s.1.2) =
      leviTensor β (fun s => g s.1) X * ∏ ij : Fin n × Fin n, if β ij.2 < β ij.1 then g ij 0 else 1 := by
  classical
  rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => ¬ β ij.1 < β ij.2) fun ij => g ij (X ij.1 ij.2),
    leviTensor, prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 = β ij.2)
      fun ij => g ij (X ij.1 ij.2), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ij _ => ?_
  rcases lt_trichotomy (β ij.1) (β ij.2) with h | h | h
  · simp [h, h.ne, not_lt.2 h.le]
  · simp [h]
  · simp [h, h.ne', not_lt.2 h.le, hX ij.1 ij.2 h.ne']

theorem integral_matrixTensor_add_unip (g : Fin n × Fin n → F → ℂ)
    {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0) :
    ∫ u, matrixTensor g (X + unipMatrix F u) ∂unipMeasure β ψ =
      tensorConst β ψ g * leviTensor β (fun s => g s.1) X := by
  classical
  have hsplit : ∀ u : UnipotentIndex n β → F, matrixTensor g (X + unipMatrix F u) =
      (∏ s : {ij : Fin n × Fin n // ¬ β ij.1 < β ij.2}, g s.1 (X s.1.1 s.1.2)) *
        ∏ s : UnipotentIndex n β, g s.1 (u s) := by
    intro u
    rw [matrixTensor, ← Fintype.prod_subtype_mul_prod_subtype
      (fun ij : Fin n × Fin n => β ij.1 < β ij.2), mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      rw [Matrix.add_apply, unipMatrix_apply_of_not_lt u s.2, add_zero]
    · refine Finset.prod_congr rfl fun s _ => ?_
      rw [Matrix.add_apply, hX _ _ (ne_of_lt s.2), zero_add, unipMatrix_apply_of_lt u s.2]
  simp_rw [hsplit]
  rw [integral_const_mul, unipMeasure,
    integral_fintype_prod_eq_prod (f := fun (s : UnipotentIndex n β) x => g s.1 x),
    prod_not_unip_eq hX, tensorConst]
  have h0 : ∀ s : UnipotentIndex n β, ∫ x, g s.1 x ∂LocalField.selfDualMeasure ψ =
      LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g s.1) 0 := by
    intro s
    simp [LocalField.localFourier]
  simp_rw [h0]
  ring

theorem localMatrixFourier_matrixTensor (g : Fin n × Fin n → F → ℂ) (Y : Matrix (Fin n) (Fin n) F) :
    localMatrixFourier ψ (matrixTensor g) Y = ∏ ij : Fin n × Fin n,
      LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij) (Y ij.2 ij.1) := by
  rw [localMatrixFourier_eq]
  have : matrixTensor g ∘ (matrixCoordHomeomorph (Fin n) F).symm = localTensor g := by
    funext x
    rfl
  rw [this, localFourierPi_localTensor]
  rfl

theorem localMatrixFourier_matrixTensor_eq (g : Fin n × Fin n → F → ℂ) :
    localMatrixFourier ψ (matrixTensor g) = matrixTensor fun ij =>
      LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij.swap) := by
  funext Z
  rw [localMatrixFourier_matrixTensor, matrixTensor]
  exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] in

theorem leviTensor_swap_eq (h : Fin n × Fin n → F → ℂ) (Y : Matrix (Fin n) (Fin n) F) :
    leviTensor β (fun s => h s.1.swap) Y = ∏ s : LeviIndex n β, h s.1 (Y s.1.2 s.1.1) := by
  rw [leviTensor]
  let e : LeviIndex n β ≃ LeviIndex n β :=
    { toFun := fun s => ⟨s.1.swap, s.2.symm⟩
      invFun := fun s => ⟨s.1.swap, s.2.symm⟩
      left_inv := fun s => rfl
      right_inv := fun s => rfl }
  exact Fintype.prod_equiv e _ _ fun s => rfl

theorem leviTensor_swap_eq_hat (g : Fin n × Fin n → F → ℂ) (Y : Matrix (Fin n) (Fin n) F) :
    leviTensor β (fun s => LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g s.1.swap)) Y =
      leviTensorHat β ψ (fun s => g s.1) Y :=
  leviTensor_swap_eq (fun ij => LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij)) Y

theorem integral_norm_matrixTensor_add_unip (g : Fin n × Fin n → F → ℂ)
    {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0) :
    ∫ u, ‖matrixTensor g (X + unipMatrix F u)‖ ∂unipMeasure β ψ =
      ‖tensorConst β ψ (fun ij x => ((‖g ij x‖ : ℝ) : ℂ))‖ * ‖leviTensor β (fun s => g s.1) X‖ := by
  have h := integral_matrixTensor_add_unip ψ (fun ij x => ((‖g ij x‖ : ℝ) : ℂ)) hX
  simp_rw [matrixTensor_norm] at h
  rw [integral_complex_ofReal] at h
  have h2 := congrArg (‖·‖) h
  simp only [Complex.norm_real, norm_mul] at h2
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at h2
  rw [h2]
  congr 1
  simp [leviTensor, norm_prod]

variable {ψ} in

theorem integral_norm_fourier_matrixTensor_add_unip (g : Fin n × Fin n → F → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Y : Matrix (Fin n) (Fin n) F}, (∀ i j, β i ≠ β j → Y i j = 0) →
      ∫ u, ‖localMatrixFourier ψ (matrixTensor g) (Y + unipMatrix F u)‖ ∂unipMeasure β ψ =
        C * ‖leviTensorHat β ψ (fun s => g s.1) Y‖ := by
  set g' : Fin n × Fin n → F → ℂ := fun ij =>
    LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij.swap)
  refine ⟨‖tensorConst β ψ (fun ij x => ((‖g' ij x‖ : ℝ) : ℂ))‖, norm_nonneg _, fun hY => ?_⟩
  rw [localMatrixFourier_matrixTensor_eq, integral_norm_matrixTensor_add_unip ψ g' hY,
    leviTensor_swap_eq_hat]

variable {ψ} in

theorem integral_fourier_matrixTensor_add_unip (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {g : Fin n × Fin n → F → ℂ} (hg : ∀ ij, g ij ∈ LocalField.schwartzBruhat F)
    {Y : Matrix (Fin n) (Fin n) F} (hY : ∀ i j, β i ≠ β j → Y i j = 0) :
    ∫ u, localMatrixFourier ψ (matrixTensor g) (Y + unipMatrix F u) ∂unipMeasure β ψ =
      tensorConst β ψ g * leviTensorHat β ψ (fun s => g s.1) Y := by
  classical
  set gh : Fin n × Fin n → F → ℂ := fun ij =>
    LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij) with hgh
  set g' : Fin n × Fin n → F → ℂ := fun ij => gh ij.swap with hg'
  have hT : ∀ Z, localMatrixFourier ψ (matrixTensor g) Z = matrixTensor g' Z := by
    intro Z
    rw [localMatrixFourier_matrixTensor, matrixTensor]
    exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl
  simp_rw [hT]
  rw [integral_matrixTensor_add_unip ψ g' hY]
  congr 1
  · have hinv : ∀ ij : Fin n × Fin n,
        LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g' ij) 0 = g ij.swap 0 := by
      intro ij
      rw [hg', hgh]
      simp only
      rw [LocalField.localFourier_localFourier_selfDual hψ hψ1 (hg _), neg_zero]
    rw [tensorConst, tensorConst]
    simp_rw [hinv]
    rw [mul_comm]
    congr 1
    · rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2) fun ij => gh ij 0]
      exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl
    · rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2)
        fun ij => g ij.swap 0]
      exact (Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl).symm
  · rw [leviTensor, leviTensorHat]
    let e : LeviIndex n β ≃ LeviIndex n β :=
      { toFun := fun s => ⟨s.1.swap, s.2.symm⟩
        invFun := fun s => ⟨s.1.swap, s.2.symm⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    exact Fintype.prod_equiv e _ _ fun s => rfl

end Unip

section Translate

variable [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

theorem mul_mem_integer_iff {y : GL (Fin n) F} (hy : y ∈ integralGL F n)
    (X : Matrix (Fin n) (Fin n) F) :
    (∀ i j, (X * (y : Matrix (Fin n) (Fin n) F)) i j ∈ 𝒪[F]) ↔ ∀ i j, X i j ∈ 𝒪[F] := by
  obtain ⟨h₁, h₂⟩ := (mem_integralGL_iff F n).1 hy
  have key : ∀ (A B : Matrix (Fin n) (Fin n) F), (∀ i j, A i j ∈ 𝒪[F]) → (∀ i j, B i j ∈ 𝒪[F]) →
      ∀ i j, (A * B) i j ∈ 𝒪[F] := fun A B hA hB i j => by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)
  refine ⟨fun h i j => ?_, fun h => key _ _ h h₁⟩
  have := key _ _ h h₂ i j
  rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this

def mulRightEquiv (y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F ≃ₜ+ Matrix (Fin n) (Fin n) F where
  toFun X := X * (y : Matrix (Fin n) (Fin n) F)
  invFun X := X * ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  left_inv X := by simp [Matrix.mul_assoc]
  right_inv X := by simp [Matrix.mul_assoc]
  map_add' X Y := Matrix.add_mul X Y _
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

omit [MeasurableSpace F] [BorelSpace F] in
theorem mulRightEquiv_apply (y : GL (Fin n) F) (X : Matrix (Fin n) (Fin n) F) :
    mulRightEquiv y X = X * (y : Matrix (Fin n) (Fin n) F) := rfl

theorem measurePreserving_mul_right {y : GL (Fin n) F} (hy : y ∈ integralGL F n) :
    MeasurePreserving (mulRightEquiv y)
      (matrixMeasure (LocalField.selfDualMeasure ψ)) (matrixMeasure (LocalField.selfDualMeasure ψ)) := by
  set μ : Measure (Matrix (Fin n) (Fin n) F) := matrixMeasure (LocalField.selfDualMeasure ψ) with hμ
  have hH : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
      LocalField.selfDualMeasure ψ : Measure (Fin n → Fin n → F)).IsAddHaarMeasure := by
    have : (Measure.pi fun _ : Fin n => LocalField.selfDualMeasure ψ).IsAddHaarMeasure :=
      inferInstance
    infer_instance
  have : μ.IsAddHaarMeasure := hH
  set e := mulRightEquiv y
  have hmap : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hsmul := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ
  set B : Set (Matrix (Fin n) (Fin n) F) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => (LocalField.valBall F 0 : Set F) with hB
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => LocalField.isOpen_valBall 0
  have hBc : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    LocalField.isCompact_valBall 0
  have hmemB : ∀ X, X ∈ B ↔ ∀ i j, X i j ∈ 𝒪[F] := by
    intro X
    rw [hB]
    constructor
    · intro h i j
      exact LocalField.mem_valBall_zero_iff.1 (h i (Set.mem_univ _) j (Set.mem_univ _))
    · intro h i _ j _
      exact LocalField.mem_valBall_zero_iff.2 (h i j)
  have hpre : e ⁻¹' B = B := by
    ext X
    rw [Set.mem_preimage, hmemB, hmemB]
    exact mul_mem_integer_iff hy X
  have h0 : μ B ≠ 0 := hBo.measure_ne_zero μ ⟨0, fun _ _ _ _ => by simp [zero_mem]⟩
  have ht : μ B ≠ ⊤ := hBc.measure_lt_top.ne
  have hc : Measure.addHaarScalarFactor (μ.map e) μ = 1 := by
    have h1 := congrArg (fun m : Measure (Matrix (Fin n) (Fin n) F) => m B) hsmul
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    have hme : Measurable e := e.continuous.measurable
    rw [Measure.map_apply hme hBo.measurableSet, hpre] at h1
    have h2 : (Measure.addHaarScalarFactor (μ.map e) μ : ENNReal) * μ B = 1 * μ B := by
      rw [one_mul, ← h1]
    exact_mod_cast (ENNReal.mul_left_inj h0 ht).1 h2
  refine ⟨e.continuous.measurable, ?_⟩
  rw [hsmul, hc, one_smul]

theorem localMatrixFourier_mul_right (Φ : Matrix (Fin n) (Fin n) F → ℂ) {y : GL (Fin n) F}
    (hy : y ∈ integralGL F n) (Z : Matrix (Fin n) (Fin n) F) :
    localMatrixFourier ψ (fun X => Φ (X * (y : Matrix (Fin n) (Fin n) F))) Z =
      localMatrixFourier ψ Φ (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z) := by
  have hm := measurePreserving_mul_right ψ hy
  have he : MeasurableEmbedding (mulRightEquiv y) :=
    (mulRightEquiv y).toHomeomorph.measurableEmbedding
  rw [localMatrixFourier, localMatrixFourier]
  have key : ∀ X : Matrix (Fin n) (Fin n) F,
      Φ (X * (y : Matrix (Fin n) (Fin n) F)) * (ψ (trace (X * Z)) : ℂ) =
        (fun W => Φ W * (ψ (trace (W * (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z))) :
          ℂ)) (mulRightEquiv y X) := by
    intro X
    simp only [mulRightEquiv_apply]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (y : Matrix (Fin n) (Fin n) F), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  simp_rw [key]
  exact hm.integral_comp he (fun W => Φ W *
    (ψ (trace (W * (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z))) : ℂ))

end Translate

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory GJMatrix
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

variable (β) in

def leviCoordMeasure (ψ : AddChar F Circle) : Measure (LeviIndex n β → F) :=
  Measure.pi fun _ => LocalField.selfDualMeasure ψ

instance (ψ : AddChar F Circle) : (leviCoordMeasure β ψ).IsAddHaarMeasure := by
  unfold leviCoordMeasure
  infer_instance

variable (β) in

def leviAbsDetShift : levi F n β →* ℝ≥0 where
  toFun m := leviAbsDet β m ^ (((n : ℝ) - 1) / 2)
  map_one' := by simp
  map_mul' m m' := by simp [NNReal.mul_rpow]

variable (β) in

def inducedChar : levi F n β →* ℝ≥0 :=
  leviRatio β * leviSqrtModular β * leviAbsDetShift β

omit [MeasurableSpace F] [BorelSpace F] in
theorem detPow_eq_cpow (g : GL (Fin n) F) (s : ℂ) :
    detPow g s = ((LocalField.modulus ((g : Matrix (Fin n) (Fin n) F).det) : ℝ) : ℂ) ^ s := rfl

omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_det_pos (g : GL (Fin n) F) :
    0 < LocalField.modulus ((g : Matrix (Fin n) (Fin n) F).det) :=
  LocalField.modulus_pos (det_ne_zero g)

omit [MeasurableSpace F] [BorelSpace F] in

theorem detPow_add_shift (m : levi F n β) (s : ℂ) :
    detPow (m : GL (Fin n) F) (s + ((n : ℂ) - 1) / 2) =
      detPow (m : GL (Fin n) F) s * ((leviAbsDetShift β m : ℝ≥0) : ℂ) := by
  have hx := modulus_det_pos (m : GL (Fin n) F)
  rw [detPow_eq_cpow, detPow_eq_cpow, Complex.cpow_add _ _ (by exact_mod_cast hx.ne')]
  congr 1
  rw [leviAbsDetShift, MonoidHom.coe_mk, OneHom.coe_mk, leviAbsDet_apply, NNReal.coe_rpow,
    Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  push_cast
  rfl

omit [MeasurableSpace F] [BorelSpace F] in

theorem leviIntegrand_shift (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W)
    (s : ℂ) (m : levi F n β) :
    leviIntegrand σ (leviRatio β * leviSqrtModular β) Ψ w ℓ (s + ((n : ℂ) - 1) / 2) m =
      leviIntegrand σ (inducedChar β) Ψ w ℓ s m := by
  simp only [leviIntegrand, inducedChar, MonoidHom.mul_apply, detPow_add_shift]
  push_cast
  ring

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] in

theorem monoidHom_ne_zero {G : Type*} [Group G] (χ : G →* ℝ≥0) (g : G) : χ g ≠ 0 :=
  left_ne_zero_of_mul_eq_one (map_mul_eq_one χ (mul_inv_cancel g))

theorem weightB_eq (m : levi F n β) (s : ℂ) :
    ((leviRatio β m * leviSqrtModular β m : ℝ≥0) : ℂ) *
        detPow (m : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2) =
      (((inducedChar β m)⁻¹ * leviModulus β m : ℝ≥0) : ℂ) * detPow (m : GL (Fin n) F) (-s) := by
  set x : ℝ≥0 := leviAbsDet β m with hxdef
  have hx : x ≠ 0 := (modulus_det_pos (m : GL (Fin n) F)).ne'
  set c : ℝ := ((n : ℝ) - 1) / 2 with hc
  have hsplit : detPow (m : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2) =
      ((x ^ (1 + c) : ℝ≥0) : ℂ) * detPow (m : GL (Fin n) F) (-s) := by
    have hx' : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
    rw [detPow_eq_cpow, detPow_eq_cpow]
    show ((x : ℝ) : ℂ) ^ (1 - s + ((n : ℂ) - 1) / 2) = ((x ^ (1 + c) : ℝ≥0) : ℂ) * ((x : ℝ) : ℂ) ^ (-s)
    rw [show (1 - s + ((n : ℂ) - 1) / 2) = ((1 + c : ℝ) : ℂ) + (-s) by rw [hc]; push_cast; ring,
      Complex.cpow_add _ _ hx', NNReal.coe_rpow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  have hid : leviRatio β m ^ 2 * Measure.modularCharacter (leviIncl m) * x ^ n = leviModulus β m :=
    leviRatio_sq_mul_modular_mul_det (F := F) m
  have hsq : leviSqrtModular β m * leviSqrtModular β m =
      Measure.modularCharacter (leviIncl m) := by
    simp [leviSqrtModular, NNReal.mul_self_sqrt]
  have hpow : x ^ c * x ^ (1 + c) = x ^ n := by
    rw [← NNReal.rpow_add hx, show c + (1 + c) = (n : ℝ) by rw [hc]; ring, NNReal.rpow_natCast]
  have hκ : inducedChar β m = leviRatio β m * leviSqrtModular β m * x ^ c := rfl
  have hκ0 : inducedChar β m ≠ 0 := monoidHom_ne_zero _ m
  have key : leviRatio β m * leviSqrtModular β m * x ^ (1 + c) =
      (inducedChar β m)⁻¹ * leviModulus β m := by
    rw [eq_inv_mul_iff_mul_eq₀ hκ0, hκ, ← hid, ← hsq, ← hpow]
    ring
  rw [hsplit, ← mul_assoc, ← Complex.ofReal_mul, ← NNReal.coe_mul, key]

theorem leviIntegrandB_eq (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W)
    (s : ℂ) (m : levi F n β) :
    Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (((leviRatio β m * leviSqrtModular β m : ℝ≥0) : ℂ) *
          detPow (m : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2)) * ℓ (σ m⁻¹ w) =
      leviIntegrandB σ (inducedChar β) Ψ w ℓ s m := by
  rw [weightB_eq, leviIntegrandB]
  ring

section ParabolicB

omit [MeasurableSpace F] [BorelSpace F] in

theorem modularCharacter_leviProj (p : blockUpper F n β) :
    Measure.modularCharacter (leviIncl (leviProj F n β p)) = Measure.modularCharacter p := by
  have h := modularCharacter_eq_one_of_mem _ (leviProj_inv_mul_mem p)
  rw [map_mul, map_inv] at h
  exact (inv_mul_eq_one₀ (monoidHom_ne_zero _ _)).1 h

omit [MeasurableSpace F] [BorelSpace F] in
theorem modularCharacter_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    Measure.modularCharacter (parabolicMk β m u) = Measure.modularCharacter (leviIncl m) := by
  rw [← modularCharacter_leviProj, leviProj_parabolicMk]

omit [MeasurableSpace F] [BorelSpace F] in
theorem sqrtModular_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    sqrtModular F n β (parabolicMk β m u) = ((leviSqrtModular β m : ℝ≥0) : ℂ) := by
  rw [coe_leviSqrtModular, ← sqrtModular_leviProj, leviProj_parabolicMk]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviSqrtModular_mul_self (m : levi F n β) :
    leviSqrtModular β m * leviSqrtModular β m = Measure.modularCharacter (leviIncl m) := by
  simp [leviSqrtModular, NNReal.mul_self_sqrt]

variable (β) in

def parabolicB (Ξ : Matrix (Fin n) (Fin n) F → ℂ) (φ : GL (Fin n) F → W) (ℓ : Module.Dual ℂ W)
    (s : ℂ) (y : GL (Fin n) F) (p : blockUpper F n β) : ℂ :=
  Ξ ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
    detPow (p : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2) * ℓ (φ ((p : GL (Fin n) F)⁻¹ * y))

omit [MeasurableSpace F] [BorelSpace F] in

theorem modular_mul_parabolicB {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ)
    (Ξ : Matrix (Fin n) (Fin n) F → ℂ) (ℓ : Module.Dual ℂ W) (s : ℂ) (y : GL (Fin n) F)
    (m : levi F n β) (u : UnipotentIndex n β → F) :
    (Measure.modularCharacter (parabolicMk β m u) : ℂ) * parabolicB β Ξ φ ℓ s y (parabolicMk β m u) =
      Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
        (((leviSqrtModular β m : ℝ≥0) : ℂ) *
          detPow (m : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2) * ℓ (σ m⁻¹ (φ y))) := by
  have h1 := hφ.1 (parabolicMk β m u)⁻¹ y
  rw [inflateTwist_apply, map_inv, map_inv, leviProj_parabolicMk, sqrtModular_parabolicMk,
    Subgroup.coe_inv] at h1
  have hs0 : ((leviSqrtModular β m : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast monoidHom_ne_zero (leviSqrtModular β) m
  rw [parabolicB, h1, map_smul, smul_eq_mul, modularCharacter_parabolicMk,
    ← leviSqrtModular_mul_self, coe_parabolicMk, detPow_parabolicMk]
  push_cast
  field_simp

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (ψ : AddChar F Circle)

variable (β) in

abbrev measureP : Measure (blockUpper F n β) :=
  haarParabolic (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ))

variable (β) in

abbrev measureM : Measure (levi F n β) := haarLevi β (leviCoordMeasure β ψ)

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem continuous_parabolicB {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ)
    {Ξ : Matrix (Fin n) (Fin n) F → ℂ} (hΞ : IsSchwartzBruhat Ξ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (y : GL (Fin n) F) : Continuous (parabolicB β Ξ φ ℓ s y) := by
  obtain ⟨K, hKo, hK⟩ := hφ.2
  have hℓφ : Continuous fun g => ℓ (φ g) := by
    refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨g • (K : Set (GL (Fin n) F)), ?_, hKo.smul g, ⟨1, one_mem _, mul_one g⟩⟩
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_preimage, smul_eq_mul, hK k hk]
    exact hg
  have hv : Continuous fun p : blockUpper F n β => (p : GL (Fin n) F) := continuous_subtype_val
  exact ((hΞ.1.continuous.comp (Units.continuous_val.comp hv)).mul
    ((continuous_detPow _).comp hv)).mul (hℓφ.comp ((hv.inv).mul continuous_const))

theorem lintegral_parabolicB_inv {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ)
    {Ξ : Matrix (Fin n) (Fin n) F → ℂ} (hΞ : IsSchwartzBruhat Ξ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (y : GL (Fin n) F) :
    ∫⁻ p, ‖parabolicB β Ξ φ ℓ s y p⁻¹‖ₑ ∂measureP β ψ =
      ∫⁻ m, ‖leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, ((‖Ξ (X + unipMatrix F u)‖ : ℝ) : ℂ) ∂unipMeasure β ψ) (φ y) ℓ s m‖ₑ
          ∂measureM β ψ := by
  have : SecondCountableTopology (blockUpper F n β) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hc := continuous_parabolicB hφ hΞ ℓ s y
  have hmeas : Measurable fun p => ‖parabolicB β Ξ φ ℓ s y p‖ₑ := hc.enorm.measurable
  have hΔ := LinearChart.measurable_modularCharacter (parabolicChart F n β)
  rw [show measureP β ψ = (parabolicChart F n β).haar
      (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ)) from rfl,
    LinearChart.lintegral_inv_haar _ _ hmeas,
    show (parabolicChart F n β).haar (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ)) =
      measureP β ψ from rfl,
    lintegral_haarParabolic (leviCoordMeasure β ψ) (unipMeasure β ψ)
      (H := fun p => (Measure.modularCharacter p : ℝ≥0∞) * ‖parabolicB β Ξ φ ℓ s y p‖ₑ)
      (hΔ.mul hmeas)]
  refine lintegral_congr fun m => ?_
  have hint := integrable_add_unipMatrix (unipMeasure β ψ) hΞ
    (X := ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) (mem_levi.1 m.2)
  set c : ℂ := ((leviSqrtModular β m : ℝ≥0) : ℂ) *
    detPow (m : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2) * ℓ (σ m⁻¹ (φ y)) with hcdef
  have hpt : ∀ u, (Measure.modularCharacter (parabolicMk β m u) : ℝ≥0∞) *
      ‖parabolicB β Ξ φ ℓ s y (parabolicMk β m u)‖ₑ =
        ‖Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖ₑ * ‖c‖ₑ := by
    intro u
    rw [← enorm_coe_nnreal, ← enorm_mul]
    have := modular_mul_parabolicB (σ := σ) hφ Ξ ℓ s y m u
    rw [this, enorm_mul]
  simp_rw [hpt]
  have hΞm : Measurable fun u : UnipotentIndex n β → F =>
      ‖Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖ₑ :=
    (hΞ.1.continuous.comp (continuous_const.add continuous_unipMatrix)).enorm.measurable
  rw [lintegral_mul_const _ hΞm, ← ofReal_integral_norm_eq_lintegral_enorm hint]
  have hI : 0 ≤ ∫ u, ‖Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖
      ∂unipMeasure β ψ := integral_nonneg fun _ => norm_nonneg _
  rw [← leviIntegrandB_eq, integral_complex_ofReal, hcdef]
  simp only [enorm_mul]
  rw [enorm_ofReal_complex hI, enorm_coe_nnreal, enorm_coe_nnreal]
  push_cast
  ring

theorem integral_parabolicB_inv {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ)
    {Ξ : Matrix (Fin n) (Fin n) F → ℂ} (hΞ : IsSchwartzBruhat Ξ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (y : GL (Fin n) F)
    (hint : Integrable (fun p => parabolicB β Ξ φ ℓ s y p⁻¹) (measureP β ψ)) :
    ∫ p, parabolicB β Ξ φ ℓ s y p⁻¹ ∂measureP β ψ =
      ∫ m, leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, Ξ (X + unipMatrix F u) ∂unipMeasure β ψ) (φ y) ℓ s m ∂measureM β ψ := by
  have : SecondCountableTopology (blockUpper F n β) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hc := continuous_parabolicB hφ hΞ ℓ s y
  have hΔc : Continuous fun p : blockUpper F n β => ((Measure.modularCharacter p : ℝ≥0) : ℂ) :=
    (Complex.continuous_ofReal.comp NNReal.continuous_coe).comp
      (LinearChart.continuous_modularCharacter (parabolicChart F n β))
  have hint2 : Integrable (fun p => ((Measure.modularCharacter p : ℝ≥0) : ℂ) *
      parabolicB β Ξ φ ℓ s y p) (measureP β ψ) := by
    refine ⟨(hΔc.mul hc).aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖((Measure.modularCharacter p : ℝ≥0) : ℂ) * parabolicB β Ξ φ ℓ s y p‖ₑ
      ∂measureP β ψ < ⊤
    have h1 : ∫⁻ p, ‖((Measure.modularCharacter p : ℝ≥0) : ℂ) * parabolicB β Ξ φ ℓ s y p‖ₑ
        ∂measureP β ψ = ∫⁻ p, ‖parabolicB β Ξ φ ℓ s y p⁻¹‖ₑ ∂measureP β ψ := by
      rw [show measureP β ψ = (parabolicChart F n β).haar
          (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ)) from rfl,
        LinearChart.lintegral_inv_haar _ _ hc.enorm.measurable]
      refine lintegral_congr fun p => ?_
      rw [enorm_mul, enorm_coe_nnreal]
    rw [h1]
    exact hint.2
  rw [show measureP β ψ = (parabolicChart F n β).haar
      (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ)) from rfl,
    LinearChart.integral_inv_haar _ _ hc,
    show (parabolicChart F n β).haar (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ)) =
      measureP β ψ from rfl,
    integral_haarParabolic (leviCoordMeasure β ψ) (unipMeasure β ψ) hint2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
  simp only
  simp_rw [modular_mul_parabolicB (σ := σ) hφ Ξ ℓ s y m]
  rw [integral_mul_const, ← leviIntegrandB_eq]
  push_cast
  ring

end ParabolicB

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory GJMatrix
open scoped NNReal ENNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

def cosetFamily (p : ℤ × (Fin n × Fin n → F)) : Fin n × Fin n → F → ℂ :=
  fun ij => cosetInd (LocalField.valBall F p.1) (p.2 ij)

omit [MeasurableSpace F] [BorelSpace F] in
theorem cosetFamily_mem (p : ℤ × (Fin n × Fin n → F)) (ij : Fin n × Fin n) :
    cosetFamily p ij ∈ LocalField.schwartzBruhat F :=
  cosetInd_valBall_mem p.1 (p.2 ij)

omit [MeasurableSpace F] [BorelSpace F] in

theorem isSchwartzBruhat_matrixTensor {g : Fin n × Fin n → F → ℂ}
    (hg : ∀ ij, g ij ∈ LocalField.schwartzBruhat F) : IsSchwartzBruhat (matrixTensor g) := by
  rw [isSchwartzBruhat_iff_comp_symm]
  have : matrixTensor g ∘ (matrixCoordHomeomorph (Fin n) F).symm = localTensor g := by
    funext x
    rfl
  rw [this]
  exact localTensor_mem hg

omit [MeasurableSpace F] [BorelSpace F] in

theorem exists_matrixTensor_decomp {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    ∃ (S : Finset (ℤ × (Fin n × Fin n → F))) (c : ℤ × (Fin n × Fin n → F) → ℂ),
      ∀ X, Φ X = ∑ p ∈ S, c p * matrixTensor (cosetFamily p) X := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_matrixTensor hΦ)
  refine ⟨c.support, c, fun X => ?_⟩
  rw [← hc, Finsupp.sum, Finset.sum_apply]
  rfl

instance isAddHaarMeasure_matrixMeasure (ψ : AddChar F Circle) :
    (matrixMeasure (LocalField.selfDualMeasure ψ) : Measure (Matrix (Fin n) (Fin n) F)).IsAddHaarMeasure := by
  have : (Measure.pi fun _ : Fin n => LocalField.selfDualMeasure ψ).IsAddHaarMeasure :=
    inferInstance
  have hH : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
      LocalField.selfDualMeasure ψ : Measure (Fin n → Fin n → F)).IsAddHaarMeasure := inferInstance
  exact hH

theorem localMatrixFourier_sum (ψ : AddChar F Circle) (hψ : Continuous ψ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) {T : ι → Matrix (Fin n) (Fin n) F → ℂ}
    (hT : ∀ p ∈ S, IsSchwartzBruhat (T p)) (Z : Matrix (Fin n) (Fin n) F) :
    localMatrixFourier ψ (fun X => ∑ p ∈ S, c p * T p X) Z =
      ∑ p ∈ S, c p * localMatrixFourier ψ (T p) Z := by
  simp only [localMatrixFourier, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext X
    ring
  · intro p hp
    have hc : Continuous fun X : Matrix (Fin n) (Fin n) F => (ψ (trace (X * Z)) : ℂ) :=
      (continuous_subtype_val.comp hψ).comp (continuous_id.matrix_mul continuous_const).matrix_trace
    exact (((hT p hp).1.continuous.const_smul (c p)).mul hc).integrable_of_hasCompactSupport
      (((hT p hp).2.smul_left (f := fun _ => c p)).mul_right)

theorem lintegral_lt_top_of_le_sum {X ι : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    {S : Finset ι} {g : ι → X → ℂ} {a : ι → ℝ} (ha : ∀ p, 0 ≤ a p)
    (hg : ∀ p ∈ S, Integrable (g p) μ) (hle : ∀ x, ‖f x‖ ≤ ∑ p ∈ S, a p * ‖g p x‖) :
    ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤ := by
  calc ∫⁻ x, ‖f x‖ₑ ∂μ ≤ ∫⁻ x, ∑ p ∈ S, ENNReal.ofReal (a p) * ‖g p x‖ₑ ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm]
        calc ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal (∑ p ∈ S, a p * ‖g p x‖) :=
              ENNReal.ofReal_le_ofReal (hle x)
          _ = ∑ p ∈ S, ENNReal.ofReal (a p) * ‖g p x‖ₑ := by
              rw [ENNReal.ofReal_sum_of_nonneg fun p _ => mul_nonneg (ha p) (norm_nonneg _)]
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [ENNReal.ofReal_mul (ha p), ofReal_norm]
    _ = ∑ p ∈ S, ENNReal.ofReal (a p) * ∫⁻ x, ‖g p x‖ₑ ∂μ := by
        rw [lintegral_finsetSum' _ fun p hp =>
          ((hg p hp).aestronglyMeasurable.enorm).const_mul _]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.sum_lt_top.2 fun p hp =>
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hg p hp).2

omit [MeasurableSpace F] [BorelSpace F] in
theorem norm_leviIntegrand (κ : levi F n β →* ℝ≥0) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (m : levi F n β) :
    ‖leviIntegrand σ κ Ψ w ℓ s m‖ = ‖Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖ *
      ‖((κ m : ℝ≥0) : ℂ) * detPow (m : GL (Fin n) F) s * ℓ (σ m w)‖ := by
  simp only [leviIntegrand, norm_mul]
  ring

omit [MeasurableSpace F] [BorelSpace F] in
theorem norm_leviIntegrandB (κ : levi F n β →* ℝ≥0) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (m : levi F n β) :
    ‖leviIntegrandB σ κ Ψ w ℓ s m‖ = ‖Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖ *
      ‖((((κ m)⁻¹ * leviModulus β m : ℝ≥0)) : ℂ) * detPow (m : GL (Fin n) F) (-s) * ℓ (σ m⁻¹ w)‖ := by
  simp only [leviIntegrandB, norm_mul]
  ring

omit [IsNonarchimedeanLocalField F] in

instance borelSpace_GL : BorelSpace (GL (Fin n) F) := by
  refine ⟨?_⟩
  have hM : (measurableSpace_matrix : MeasurableSpace (Matrix (Fin n) (Fin n) F)) =
      _root_.borel (Matrix (Fin n) (Fin n) F) := BorelSpace.measurable_eq
  show MeasurableSpace.comap Units.val _ = _
  rw [hM, ← borel_comap, ← (Measures.isOpenEmbedding_val F n).isEmbedding.eq_induced]

theorem levi_decomp {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {γ : RatFunc ℂ}
    (hL : LeviFE F σ (inducedChar β) (measureM β ψ) ψ γ) {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (w : W) {ℓ : Module.Dual ℂ W}
    (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    (∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → ∫⁻ m, ‖leviIntegrand σ (inducedChar β)
        (fun X => ∫ u, ((‖Φ (X + unipMatrix F u)‖ : ℝ) : ℂ) ∂unipMeasure β ψ) w ℓ s m‖ₑ
          ∂measureM β ψ < ⊤) ∧
    (∃ s₁ : ℝ, ∀ s : ℂ, s.re < s₁ → ∫⁻ m, ‖leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, ((‖localMatrixFourier ψ Φ (X + unipMatrix F u)‖ : ℝ) : ℂ) ∂unipMeasure β ψ)
          w ℓ s m‖ₑ ∂measureM β ψ < ⊤) ∧
    RatFE F γ
      (fun s => ∫ m, leviIntegrand σ (inducedChar β)
        (fun X => ∫ u, Φ (X + unipMatrix F u) ∂unipMeasure β ψ) w ℓ s m ∂measureM β ψ)
      (fun s => ∫ m, leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, localMatrixFourier ψ Φ (X + unipMatrix F u) ∂unipMeasure β ψ) w ℓ s m
          ∂measureM β ψ) := by
  classical
  obtain ⟨S, c, hc⟩ := exists_matrixTensor_decomp hΦ
  set T : ℤ × (Fin n × Fin n → F) → Matrix (Fin n) (Fin n) F → ℂ :=
    fun p => matrixTensor (cosetFamily p) with hTdef
  set L : ℤ × (Fin n × Fin n → F) → Matrix (Fin n) (Fin n) F → ℂ :=
    fun p => leviTensor β fun s => cosetFamily p s.1 with hLdef
  set Lh : ℤ × (Fin n × Fin n → F) → Matrix (Fin n) (Fin n) F → ℂ :=
    fun p => leviTensorHat β ψ fun s => cosetFamily p s.1 with hLhdef
  set K : ℤ × (Fin n × Fin n → F) → ℂ := fun p => tensorConst β ψ (cosetFamily p) with hKdef
  have hTsb : ∀ p, IsSchwartzBruhat (T p) := fun p =>
    isSchwartzBruhat_matrixTensor fun ij => cosetFamily_mem p ij
  have hLev := fun p => hL (fun s => cosetFamily p s.1) (fun s => cosetFamily_mem p s.1) w ℓ hℓ
  choose sA hA using fun p => (hLev p).1
  choose sB hB using fun p => (hLev p).2.1
  have hR := fun p => (hLev p).2.2
  have hΦeq : Φ = fun X => ∑ p ∈ S, c p * T p X := funext hc

  have hΨA : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      ∫ u, Φ (X + unipMatrix F u) ∂unipMeasure β ψ = ∑ p ∈ S, c p * (K p * L p X) := by
    intro X hX
    rw [hΦeq]
    simp only
    rw [integral_finsetSum _ fun p _ =>
      (integrable_add_unipMatrix (unipMeasure β ψ) (hTsb p) hX).const_mul (c p)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul, integral_matrixTensor_add_unip ψ _ hX]
  have hΦh : ∀ Z, localMatrixFourier ψ Φ Z = ∑ p ∈ S, c p * localMatrixFourier ψ (T p) Z := by
    intro Z
    rw [hΦeq]
    exact localMatrixFourier_sum ψ hψ S c (fun p _ => hTsb p) Z
  have hΨB : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      ∫ u, localMatrixFourier ψ Φ (X + unipMatrix F u) ∂unipMeasure β ψ =
        ∑ p ∈ S, c p * (K p * Lh p X) := by
    intro X hX
    simp_rw [hΦh]
    rw [integral_finsetSum _ fun p _ =>
      (integrable_add_unipMatrix (unipMeasure β ψ) ((hTsb p).localMatrixFourier hψ hψ1) hX).const_mul
        (c p)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul, integral_fourier_matrixTensor_add_unip hψ hψ1
      (fun ij => cosetFamily_mem p ij) hX]
  set s₁ : ℝ := ∑ p ∈ S, (|sA p| + |sB p|) with hs₁
  have hsA : ∀ p ∈ S, sA p ≤ s₁ := fun p hp =>
    (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun p => |sA p| + |sB p|)
        (fun p _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hp))
  have hsB : ∀ p ∈ S, -s₁ ≤ sB p := fun p hp => by
    have h1 : |sB p| ≤ s₁ := (le_add_of_nonneg_left (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun p => |sA p| + |sB p|)
        (fun p _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hp)
    linarith [neg_abs_le (sB p)]

  have hRsum : RatFE F γ
      (fun s => ∑ p ∈ S, c p * K p *
        ∫ m, leviIntegrand σ (inducedChar β) (L p) w ℓ s m ∂measureM β ψ)
      (fun s => ∑ p ∈ S, c p * K p *
        ∫ m, leviIntegrandB σ (inducedChar β) (Lh p) w ℓ s m ∂measureM β ψ) :=
    RatFE.sum S fun p _ => RatFE.const_mul (c p * K p) (hR p)
  have hptA : ∀ s : ℂ, ∀ m : levi F n β, leviIntegrand σ (inducedChar β)
      (fun X => ∫ u, Φ (X + unipMatrix F u) ∂unipMeasure β ψ) w ℓ s m =
        ∑ p ∈ S, c p * K p * leviIntegrand σ (inducedChar β) (L p) w ℓ s m := by
    intro s m
    simp only [leviIntegrand]
    rw [hΨA _ (mem_levi.1 m.2), Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hptB : ∀ s : ℂ, ∀ m : levi F n β, leviIntegrandB σ (inducedChar β)
      (fun X => ∫ u, localMatrixFourier ψ Φ (X + unipMatrix F u) ∂unipMeasure β ψ) w ℓ s m =
        ∑ p ∈ S, c p * K p * leviIntegrandB σ (inducedChar β) (Lh p) w ℓ s m := by
    intro s m
    simp only [leviIntegrandB]
    rw [hΨB _ (mem_levi.1 m.2), Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring

  have hnA : ∀ m : levi F n β, ∫ u, ‖Φ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
      unipMatrix F u)‖ ∂unipMeasure β ψ ≤ ∑ p ∈ S, ‖c p‖ *
        (‖tensorConst β ψ (fun ij x => ((‖cosetFamily p ij x‖ : ℝ) : ℂ))‖ *
          ‖L p ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖) := by
    intro m
    have hX := mem_levi.1 m.2
    have hint : ∀ p, Integrable (fun u => T p (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
        unipMatrix F u)) (unipMeasure β ψ) := fun p =>
      integrable_add_unipMatrix (unipMeasure β ψ) (hTsb p) hX
    calc ∫ u, ‖Φ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖
          ∂unipMeasure β ψ
        ≤ ∫ u, ∑ p ∈ S, ‖c p‖ * ‖T p (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
            unipMatrix F u)‖ ∂unipMeasure β ψ := by
          refine integral_mono (integrable_add_unipMatrix (unipMeasure β ψ) hΦ hX).norm
            (integrable_finsetSum _ fun p _ => (hint p).norm.const_mul _) fun u => ?_
          rw [hc]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun p _ => norm_mul _ _
      _ = ∑ p ∈ S, ‖c p‖ * (‖tensorConst β ψ (fun ij x => ((‖cosetFamily p ij x‖ : ℝ) : ℂ))‖ *
            ‖L p ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖) := by
          rw [integral_finsetSum _ fun p _ => (hint p).norm.const_mul _]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [integral_const_mul, integral_norm_matrixTensor_add_unip ψ _ hX]
  choose C hC0 hC using fun p => integral_norm_fourier_matrixTensor_add_unip (β := β) (ψ := ψ)
    (cosetFamily p)
  have hnB : ∀ m : levi F n β, ∫ u, ‖localMatrixFourier ψ Φ
      (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖ ∂unipMeasure β ψ ≤
        ∑ p ∈ S, ‖c p‖ * (C p * ‖Lh p ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖) := by
    intro m
    have hX := mem_levi.1 m.2
    have hint : ∀ p, Integrable (fun u => localMatrixFourier ψ (T p)
        (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)) (unipMeasure β ψ) :=
      fun p => integrable_add_unipMatrix (unipMeasure β ψ) ((hTsb p).localMatrixFourier hψ hψ1) hX
    calc ∫ u, ‖localMatrixFourier ψ Φ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
          unipMatrix F u)‖ ∂unipMeasure β ψ
        ≤ ∫ u, ∑ p ∈ S, ‖c p‖ * ‖localMatrixFourier ψ (T p)
            (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖
              ∂unipMeasure β ψ := by
          refine integral_mono (integrable_add_unipMatrix (unipMeasure β ψ)
            (hΦ.localMatrixFourier hψ hψ1) hX).norm
            (integrable_finsetSum _ fun p _ => (hint p).norm.const_mul _) fun u => ?_
          rw [hΦh]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun p _ => norm_mul _ _
      _ = ∑ p ∈ S, ‖c p‖ * (C p * ‖Lh p ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖) := by
          rw [integral_finsetSum _ fun p _ => (hint p).norm.const_mul _]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [integral_const_mul, hC p hX]
  have hnorm : ∀ (m : levi F n β) (Ξ : Matrix (Fin n) (Fin n) F → ℂ),
      ‖∫ u, ((‖Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖ : ℝ) : ℂ)
        ∂unipMeasure β ψ‖ =
        ∫ u, ‖Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖
          ∂unipMeasure β ψ := fun m Ξ => by
    rw [integral_complex_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  refine ⟨⟨s₁, fun s hs => ?_⟩, ⟨-s₁, fun s hs => ?_⟩, hRsum.congr ⟨s₁, fun s hs => ?_⟩
    ⟨-s₁, fun s hs => ?_⟩⟩
  · refine lintegral_lt_top_of_le_sum (S := S)
      (a := fun p => ‖c p‖ * ‖tensorConst β ψ (fun ij x => ((‖cosetFamily p ij x‖ : ℝ) : ℂ))‖)
      (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun p hp => hA p s (lt_of_le_of_lt (hsA p hp) hs)) fun m => ?_
    rw [norm_leviIntegrand, hnorm]
    refine (mul_le_mul_of_nonneg_right (hnA m) (norm_nonneg _)).trans (le_of_eq ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [norm_leviIntegrand]
    ring
  · refine lintegral_lt_top_of_le_sum (S := S) (a := fun p => ‖c p‖ * C p)
      (fun p => mul_nonneg (norm_nonneg _) (hC0 p))
      (fun p hp => hB p s (lt_of_lt_of_le hs (hsB p hp))) fun m => ?_
    rw [norm_leviIntegrandB, hnorm]
    refine (mul_le_mul_of_nonneg_right (hnB m) (norm_nonneg _)).trans (le_of_eq ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [norm_leviIntegrandB]
    ring
  · simp_rw [hptA s]
    rw [integral_finsetSum _ fun p hp =>
      (hA p s (lt_of_le_of_lt (hsA p hp) hs)).const_mul (c p * K p)]
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _
  · simp_rw [hptB s]
    rw [integral_finsetSum _ fun p hp =>
      (hB p s (lt_of_lt_of_le hs (hsB p hp))).const_mul (c p * K p)]
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory GJMatrix
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

variable (β) in

def leviMeasure (ψ : AddChar F Circle) : Measure (levi F n β) :=
  haarLevi β (leviCoordMeasure β ψ)

instance (ψ : AddChar F Circle) : (leviMeasure β ψ).IsHaarMeasure := by
  unfold leviMeasure
  infer_instance

omit [MeasurableSpace F] [BorelSpace F] in

theorem continuous_inducedChar : Continuous (inducedChar (F := F) β) := by
  have h3 : Continuous (leviAbsDetShift (F := F) β) := by
    refine continuous_monoidHom_of_eq_one _
      ⟨leviIntegral F n β, isOpen_leviIntegral (F := F)⟩ fun k hk => ?_
    show leviAbsDet β k ^ (((n : ℝ) - 1) / 2) = 1
    rw [leviAbsDet_of_mem_integralGL (Subgroup.mem_subgroupOf.1 hk), NNReal.one_rpow]
  exact (continuous_leviRatio.mul continuous_leviSqrtModular).mul h3

theorem iwasawa_transfer (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure]
    (μP : Measure (blockUpper F n β)) [μP.IsHaarMeasure] (r : ℕ)
    [Fintype (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n))] :
    ∃ C : ℂ, ∀ f : GL (Fin n) F → ℂ, Continuous f →
      (∀ g, ∀ k ∈ congruenceSubgroup F n r, f (g * k) = f g) →
      (∀ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
        Integrable (fun p : blockUpper F n β =>
          f ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F))) μP) →
      Integrable f μG ∧ ∫ g, f g ∂μG = C * ∑ q : integralGL F n ⧸
        (congruenceSubgroup F n r).subgroupOf (integralGL F n),
          ∫ p, f ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) ∂μP := by
  classical
  have : BorelSpace (integralGL F n) := Subtype.borelSpace _
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  let μK : Measure (integralGL F n) := Measure.haar
  set κ : ℝ := μP.real (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK.real Set.univ
    with hκ
  set κ' : ℝ := μG.real (integralGL F n) * μK.real ((congruenceSubgroup F n r).subgroupOf
      (integralGL F n) : Set (integralGL F n)) with hκ'
  refine ⟨((κ⁻¹ * κ' : ℝ) : ℂ), fun f hf hr hint => ?_⟩
  have hintP : ∀ y ∈ integralGL F n,
      Integrable (fun p : blockUpper F n β => f ((p : GL (Fin n) F) * y)) μP := by
    intro y hy
    obtain ⟨h, hq⟩ := QuotientGroup.mk_out_eq_mul
      ((congruenceSubgroup F n r).subgroupOf (integralGL F n)) (⟨y, hy⟩ : integralGL F n)
    have heq : ∀ p : blockUpper F n β, f ((p : GL (Fin n) F) * y) =
        f ((p : GL (Fin n) F) * (((QuotientGroup.mk ⟨y, hy⟩ : integralGL F n ⧸
          (congruenceSubgroup F n r).subgroupOf (integralGL F n)).out : integralGL F n) :
            GL (Fin n) F)) := by
      intro p
      rw [hq, Subgroup.coe_mul, ← mul_assoc]
      exact (hr _ _ (Subgroup.mem_subgroupOf.1 h.2)).symm
    simp_rw [heq]
    exact hint _
  have hP0 : μP (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) ≠ 0 :=
    ((isOpen_integralGL F n).preimage continuous_subtype_val).measure_ne_zero _
      ⟨1, by simp [one_mem]⟩
  have hK0 : μK Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μK Set.univ_nonempty
  have hintG : Integrable f μG := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    have hC := lintegral_eq_sum_parabolic (β := β) (r := r) μG μP μK hf.enorm.measurable
      (h := fun g => ‖f g‖ₑ) (fun g k hk => by simp only [hr g k hk])
    have hlt : μG (integralGL F n) * (μK ((congruenceSubgroup F n r).subgroupOf
        (integralGL F n)) * ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf
          (integralGL F n), ∫⁻ p, ‖f ((p : GL (Fin n) F) *
          ((q.out : integralGL F n) : GL (Fin n) F))‖ₑ ∂μP) < ⊤ :=
      ENNReal.mul_lt_top (isCompact_integralGL F n).measure_lt_top
        (ENNReal.mul_lt_top (measure_lt_top _ _)
          (ENNReal.sum_lt_top.2 fun q _ => (hint q).2))
    rw [hC] at hlt
    exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne (mul_ne_zero hP0 hK0)
  refine ⟨hintG, ?_⟩
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    have hPc : IsCompact (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F)) :
        Set (blockUpper F n β)) :=
      (Measures.isClosed_blockUpper F n β).isClosedEmbedding_subtypeVal.isCompact_preimage
        (isCompact_integralGL F n)
    exact mul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨hP0, hPc.measure_lt_top.ne⟩)
      (ENNReal.toReal_ne_zero.2 ⟨hK0, measure_ne_top _ _⟩)
  have hC := integral_eq_sum_parabolic (β := β) μG μP μK hintG hr hintP
  rw [Complex.real_smul, Complex.real_smul, Complex.real_smul] at hC
  have hκC : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ0
  rw [← hκ, ← mul_assoc, ← Complex.ofReal_mul, ← hκ'] at hC
  push_cast
  field_simp
  linear_combination hC.symm

omit [MeasurableSpace F] [BorelSpace F] in
theorem detPow_inv_mul_of_mem {y : GL (Fin n) F} (hy : y ∈ integralGL F n) (g : GL (Fin n) F)
    (s : ℂ) : detPow (y⁻¹ * g) s = detPow g s := by
  rw [detPow_mul, detPow_of_mem_integralGL ((integralGL F n).inv_mem hy), one_mul]

theorem inducedFE_of_leviFE [mG : MeasurableSpace (GL (Fin n) F)] [hGB : BorelSpace (GL (Fin n) F)]
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) {γ : RatFunc ℂ} (hL : LeviFE F σ (inducedChar β) (leviMeasure β ψ) ψ γ) :
    InducedFE F σ μG ψ γ := by
  classical
  obtain rfl : mG = Units.instMeasurableSpace :=
    hGB.measurable_eq.trans (borelSpace_GL (F := F) (n := n)).measurable_eq.symm
  intro Φ hΦ φ hφ ℓ hℓ

  obtain ⟨r₁, hr₁⟩ := hΦ.exists_mul_congruenceSubgroup
  obtain ⟨K', hK'o, hK'⟩ := hφ.2
  obtain ⟨r₂, -, hr₂⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hK'o.mem_nhds K'.one_mem)
  set r := max r₁ r₂ with hrdef
  have hΦr : ∀ X : Matrix (Fin n) (Fin n) F, ∀ k ∈ congruenceSubgroup F n r,
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := fun X k hk =>
    hr₁ X k (congruenceSubgroup_antitone F n (le_max_left _ _) hk)
  have hφr : ∀ g, ∀ k ∈ congruenceSubgroup F n r, φ (g * k) = φ g := fun g k hk =>
    hK' k (hr₂ (congruenceSubgroup_antitone F n (le_max_right _ _) hk)) g
  have hk₀ : ∀ k ∈ congruenceSubgroup F n r, k ∈ integralGL F n := fun k hk =>
    congruenceSubgroup_le F n r hk
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have : Finite (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n)) :=
    Subgroup.quotient_finite_of_isOpen _
      ((isOpen_congruenceSubgroup F n r).preimage continuous_subtype_val)
  let _ := Fintype.ofFinite
    (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n))
  obtain ⟨C, hCf⟩ := iwasawa_transfer (β := β) μG (measureP β ψ) r
  set y : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n) →
    GL (Fin n) F := fun q => ((q.out : integralGL F n) : GL (Fin n) F) with hydef
  have hy : ∀ q, y q ∈ integralGL F n := fun q => (q.out).2

  have hD := fun q => levi_decomp hψ hψ1 hL (hΦ.comp_mulRight (y q)) (φ (y q)) hℓ
  choose sA hsA using fun q => (hD q).1
  choose sB hsB using fun q => (hD q).2.1
  have hRq := fun q => (hD q).2.2
  set s₁ : ℝ := ∑ q, (|sA q| + |sB q|) with hs₁
  have hsA' : ∀ q, sA q ≤ s₁ := fun q =>
    (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun q => |sA q| + |sB q|)
        (fun q _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ q)))
  have hsB' : ∀ q, -s₁ ≤ sB q := fun q => by
    have h1 : |sB q| ≤ s₁ := (le_add_of_nonneg_left (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun q => |sA q| + |sB q|)
        (fun q _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ q))
    linarith [neg_abs_le (sB q)]

  have hcontA : ∀ s : ℂ, Continuous fun g : GL (Fin n) F =>
      Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g) :=
    fun s => continuous_inducedIntegrand hΦ hφ.2 ℓ _
  have hrA : ∀ s : ℂ, ∀ g, ∀ k ∈ congruenceSubgroup F n r,
      Φ ((g * k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          detPow (g * k) (s + ((n : ℂ) - 1) / 2) * ℓ (φ (g * k)) =
        Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g) := by
    intro s g k hk
    rw [Units.val_mul, hΦr _ k hk, detPow_mul_of_mem_integralGL g (hk₀ k hk), hφr g k hk]
  have hPA : ∀ s : ℂ, s₁ < s.re → ∀ q, Integrable (fun p : blockUpper F n β =>
      Φ (((p : GL (Fin n) F) * y q : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        detPow ((p : GL (Fin n) F) * y q) (s + ((n : ℂ) - 1) / 2) *
          ℓ (φ ((p : GL (Fin n) F) * y q))) (measureP β ψ) := by
    intro s hs q
    refine ⟨((hcontA s).comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable,
      ?_⟩
    show ∫⁻ p, ‖inducedIntegrand Φ φ ℓ (s + ((n : ℂ) - 1) / 2) ((p : GL (Fin n) F) * y q)‖ₑ
      ∂measureP β ψ < ⊤
    rw [lintegral_inducedIntegrand_mul (leviCoordMeasure β ψ) (unipMeasure β ψ) hΦ hφ ℓ _ (hy q)]
    simp_rw [leviIntegrand_shift]
    exact hsA q s (lt_of_le_of_lt (hsA' q) hs)
  have hformA : ∀ s : ℂ, s₁ < s.re →
      Integrable (fun g : GL (Fin n) F =>
        Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g)) μG ∧
      ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g) ∂μG =
        C * ∑ q, ∫ m, leviIntegrand σ (inducedChar β)
          (fun X => ∫ u, Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F))
            ∂unipMeasure β ψ) (φ (y q)) ℓ s m ∂measureM β ψ := by
    intro s hs
    obtain ⟨hint, heq⟩ := hCf _ (hcontA s) (hrA s) (hPA s hs)
    refine ⟨hint, heq.trans ?_⟩
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    have := integral_inducedIntegrand_mul (leviCoordMeasure β ψ) (unipMeasure β ψ) hφ ℓ
      (s + ((n : ℂ) - 1) / 2) (hy q) (hPA s hs q)
    simp only [inducedIntegrand] at this
    rw [this]
    simp_rw [leviIntegrand_shift]

  set fB : ℂ → GL (Fin n) F → ℂ := fun s g =>
    localMatrixFourier ψ Φ (g : Matrix (Fin n) (Fin n) F) *
      detPow g (1 - s + ((n : ℂ) - 1) / 2) * ℓ (φ g⁻¹) with hfB
  have hΦh : IsSchwartzBruhat (localMatrixFourier ψ Φ) := hΦ.localMatrixFourier hψ hψ1
  have hℓφ : Continuous fun g => ℓ (φ g) := by
    refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨g • (K' : Set (GL (Fin n) F)), ?_, hK'o.smul g, ⟨1, one_mem _, mul_one g⟩⟩
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_preimage, smul_eq_mul, hK' k hk]
    exact hg
  have hcontB : ∀ s : ℂ, Continuous fun g : GL (Fin n) F => fB s g⁻¹ := fun s =>
    ((hΦh.1.continuous.comp (Units.continuous_val.comp continuous_inv)).mul
      ((continuous_detPow _).comp continuous_inv)).mul (hℓφ.comp (continuous_inv.comp continuous_inv))
  have hΦhr : ∀ Z : Matrix (Fin n) (Fin n) F, ∀ k ∈ congruenceSubgroup F n r,
      localMatrixFourier ψ Φ (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z) =
        localMatrixFourier ψ Φ Z := by
    intro Z k hk
    rw [← localMatrixFourier_mul_right ψ Φ (hk₀ k hk) Z]
    congr 1
    funext X
    exact hΦr X k hk
  have hrB : ∀ s : ℂ, ∀ g, ∀ k ∈ congruenceSubgroup F n r, fB s (g * k)⁻¹ = fB s g⁻¹ := by
    intro s g k hk
    simp only [hfB, _root_.mul_inv_rev, inv_inv, Units.val_mul]
    rw [hΦhr _ k hk, detPow_inv_mul_of_mem (hk₀ k hk), hφr g k hk]
  have hΞ : ∀ q, IsSchwartzBruhat
      (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F))) := fun q =>
    (hΦ.comp_mulRight (y q)).localMatrixFourier hψ hψ1
  have hBeq : ∀ s : ℂ, ∀ q, ∀ p : blockUpper F n β, fB s ((p : GL (Fin n) F) * y q)⁻¹ =
      parabolicB β (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
        φ ℓ s (y q) p⁻¹ := by
    intro s q p
    simp only [hfB, parabolicB, _root_.mul_inv_rev, inv_inv, Subgroup.coe_inv, Units.val_mul]
    rw [localMatrixFourier_mul_right ψ Φ (hy q), detPow_inv_mul_of_mem (hy q)]
  have hPB : ∀ s : ℂ, s.re < -s₁ → ∀ q, Integrable (fun p : blockUpper F n β =>
      fB s ((p : GL (Fin n) F) * y q)⁻¹) (measureP β ψ) := by
    intro s hs q
    simp_rw [hBeq s q]
    refine ⟨((continuous_parabolicB hφ (hΞ q) ℓ s (y q)).comp
      continuous_inv).aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖parabolicB β (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
      φ ℓ s (y q) p⁻¹‖ₑ ∂measureP β ψ < ⊤
    rw [lintegral_parabolicB_inv ψ hφ (hΞ q) ℓ s (y q)]
    exact hsB q s (lt_of_lt_of_le hs (hsB' q))
  have hinvG : μG.IsInvInvariant := ⟨inv_eq_self_GL F n μG⟩
  have hformB : ∀ s : ℂ, s.re < -s₁ → Integrable (fB s) μG ∧
      ∫ g, fB s g ∂μG = C * ∑ q, ∫ m, leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, localMatrixFourier ψ (fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
          (X + unipMatrix F u) ∂unipMeasure β ψ) (φ (y q)) ℓ s m ∂measureM β ψ := by
    intro s hs
    obtain ⟨hint, heq⟩ := hCf (fun g => fB s g⁻¹) (hcontB s) (hrB s) (hPB s hs)
    refine ⟨?_, ?_⟩
    · simpa using hint.comp_inv
    · rw [← integral_inv_eq_self (fB s) μG, heq]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      have hint2 : Integrable (fun p => parabolicB β
          (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
            φ ℓ s (y q) p⁻¹) (measureP β ψ) := by
        have := hPB s hs q
        simp_rw [hBeq s q] at this
        exact this
      refine (integral_congr_ae (Filter.Eventually.of_forall fun p => hBeq s q p)).trans ?_
      exact integral_parabolicB_inv ψ hφ (hΞ q) ℓ s (y q) hint2
  refine ⟨⟨s₁, fun s hs => (hformA s hs).1⟩, ⟨-s₁, fun s hs => (hformB s hs).1⟩, ?_⟩
  have hR := (RatFE.sum Finset.univ fun q _ => hRq q).const_mul C
  exact hR.congr ⟨s₁, fun s hs => (hformA s hs).2⟩ ⟨-s₁, fun s hs => (hformB s hs).2⟩

end GodementJacquet

end GroundTheory.Automorphic
end
end
