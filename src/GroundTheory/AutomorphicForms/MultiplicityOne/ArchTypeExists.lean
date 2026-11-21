import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.Functional
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.SmoothRep
import GroundTheory.AutomorphicForms.WhittakerCriterion

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep (normOneGL K n) H}

variable (μ σ) in

def cuspIntertwiners : Submodule ℂ (H →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ)) where
  carrier := {T | T ∈ σ.intertwiners (rightRegularRep Γ₁ μ) ∧ ∀ v, T v ∈ cuspidalL2 μ}
  add_mem' hS hT := ⟨add_mem hS.1 hT.1, fun v => add_mem (hS.2 v) (hT.2 v)⟩
  zero_mem' := ⟨zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ hT := ⟨Submodule.smul_mem _ c hT.1, fun v => Submodule.smul_mem _ c (hT.2 v)⟩

theorem cuspIntertwiners_map (T : cuspIntertwiners μ σ) (x : normOneGL K n) (w : H) :
    T.1 (σ x w) = rightRegularRep Γ₁ μ x (T.1 w) :=
  T.2.1 x w

theorem cuspIntertwiners_integrated (T : cuspIntertwiners μ σ)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (v : H) :
    T.1 (σ.integrated μ (UnitaryRep.ccToL1 μ f) v) =
      (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) (T.1 v) :=
  congrArg (fun L : H →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ) => L v)
    (UnitaryRep.comp_integrated_of_mem_intertwiners σ μ T.2.1 (UnitaryRep.ccToL1 μ f))

theorem hasContRep_intertwiner_integrated (T : cuspIntertwiners μ σ)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (v : H) :
    HasContRep μ (T.1 (σ.integrated μ (UnitaryRep.ccToL1 μ f) v)) (rconv Γ₁ μ f (T.1 v)) :=
  Eq.subst (motive := fun φ => HasContRep μ φ (rconv Γ₁ μ f (T.1 v)))
    (cuspIntertwiners_integrated T f v).symm (hasContRep_rconv μ f (T.1 v))

theorem hasContRep_intertwiner_generator (T : cuspIntertwiners μ σ) (x : normOneGL K n)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (v : H) :
    HasContRep μ (T.1 (σ x (σ.integrated μ (UnitaryRep.ccToL1 μ f) v)))
      (fun y => rconv Γ₁ μ f (T.1 v) (y * x)) :=
  Eq.subst (motive := fun φ => HasContRep μ φ (fun y => rconv Γ₁ μ f (T.1 v) (y * x)))
    (cuspIntertwiners_map T x _).symm ((hasContRep_intertwiner_integrated T f v).translate x)

theorem exists_hasContRep (T : cuspIntertwiners μ σ) {w : H} (hw : w ∈ smoothSpan μ σ) :
    ∃ F, HasContRep μ (T.1 w) F := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, f, v, -, rfl⟩ := hw
    exact ⟨_, hasContRep_intertwiner_generator T x f v⟩
  | zero =>
    exact ⟨0, Eq.subst (motive := fun φ => HasContRep μ φ 0) (map_zero T.1).symm hasContRep_zero⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨F₁, h₁⟩ := h₁
    obtain ⟨F₂, h₂⟩ := h₂
    exact ⟨F₁ + F₂, Eq.subst (motive := fun φ => HasContRep μ φ (F₁ + F₂))
      (map_add T.1 w₁ w₂).symm (h₁.add h₂)⟩
  | smul c w _ h =>
    obtain ⟨F, h⟩ := h
    exact ⟨c • F, Eq.subst (motive := fun φ => HasContRep μ φ (c • F))
      (map_smul T.1 c w).symm (h.smul c)⟩

open Classical in
variable (μ σ) in

def whittakerAt (T : cuspIntertwiners μ σ) (w : H) : ℂ :=
  if h : ∃ F, HasContRep μ (T.1 w) F then whittakerOne h.choose 1 else 0

theorem whittakerAt_eq {T : cuspIntertwiners μ σ} {w : H} {F : normOneGL K n → ℂ}
    (h : HasContRep μ (T.1 w) F) : whittakerAt μ σ T w = whittakerOne F 1 := by
  have hex : ∃ F, HasContRep μ (T.1 w) F := ⟨F, h⟩
  rw [whittakerAt, dif_pos hex, hex.choose_spec.unique h]

def whittakerOf (T : cuspIntertwiners μ σ) : Module.Dual ℂ (smoothSpan μ σ) where
  toFun w := whittakerAt μ σ T w
  map_add' w₁ w₂ := by
    obtain ⟨F₁, h₁⟩ := exists_hasContRep T w₁.2
    obtain ⟨F₂, h₂⟩ := exists_hasContRep T w₂.2
    have h : HasContRep μ (T.1 ((w₁ + w₂ : smoothSpan μ σ) : H)) (F₁ + F₂) :=
      Eq.subst (motive := fun φ => HasContRep μ φ (F₁ + F₂))
        (map_add T.1 (w₁ : H) (w₂ : H)).symm (h₁.add h₂)
    rw [whittakerAt_eq h, whittakerAt_eq h₁, whittakerAt_eq h₂, whittakerOne_add h₁.1 h₂.1]
  map_smul' c w := by
    obtain ⟨F, h₁⟩ := exists_hasContRep T w.2
    have h : HasContRep μ (T.1 ((c • w : smoothSpan μ σ) : H)) (c • F) :=
      Eq.subst (motive := fun φ => HasContRep μ φ (c • F)) (map_smul T.1 c (w : H)).symm (h₁.smul c)
    rw [whittakerAt_eq h, whittakerAt_eq h₁, whittakerOne_smul, RingHom.id_apply, smul_eq_mul]


theorem whittakerOf_mk (T : cuspIntertwiners μ σ) {a : H} (ha : a ∈ smoothSpan μ σ)
    {F : normOneGL K n → ℂ} (h : HasContRep μ (T.1 a) F) :
    whittakerOf T ⟨a, ha⟩ = whittakerOne F 1 :=
  whittakerAt_eq h

theorem whittakerOf_generator (T : cuspIntertwiners μ σ) (x : normOneGL K n)
    {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ} (hf : IsSmoothTest f) (v : H) :
    whittakerOf T ⟨σ x (σ.integrated μ (UnitaryRep.ccToL1 μ f) v),
        map_mem_smoothSpan σ x (integrated_mem_smoothSpan σ hf v)⟩ =
      whittakerOne (rconv Γ₁ μ f (T.1 v)) x := by
  refine (whittakerOf_mk T _ (hasContRep_intertwiner_generator T x f v)).trans ?_
  exact (whittakerOne_mul_right _ 1 x).trans (congrArg _ (one_mul x))

set_option maxHeartbeats 1000000 in

theorem continuous_whittakerOne_rconv_intertwiner (T : cuspIntertwiners μ σ)
    {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ} (hf : IsSmoothTest f) :
    Continuous fun v : H => whittakerOne (rconv Γ₁ μ f (T.1 v)) 1 := by
  obtain ⟨ν, hν, U, hU, β, hβ, hβc, hβu, g, rfl⟩ := hf
  obtain ⟨B, hB⟩ := exists_norm_rconv_le_uniform μ ν hβ hβc hβu U hU g
  let L : H →ₗ[ℂ] ℂ :=
    { toFun := fun v => whittakerOne (rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g))
        (T.1 v)) 1
      map_add' := fun v v' => by
        have e : rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) (T.1 (v + v')) =
            rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) (T.1 v) +
              rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) (T.1 v') := by
          funext y
          exact (congrArg (fun φ => rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) φ y)
            (map_add T.1 v v')).trans (rconv_add Γ₁ μ _ _ _ y)
        exact (congrArg (fun F => whittakerOne F 1) e).trans
          (whittakerOne_add (continuous_rconv Γ₁ μ _ _) (continuous_rconv Γ₁ μ _ _) 1)
      map_smul' := fun c v => by
        have e : rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) (T.1 (c • v)) =
            c • rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) (T.1 v) := by
          funext y
          exact (congrArg (fun φ => rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) φ y)
            (map_smul T.1 c v)).trans (rconv_smul Γ₁ μ _ _ _ y)
        exact (congrArg (fun F => whittakerOne F 1) e).trans (whittakerOne_smul c _ 1) }
  refine AddMonoidHomClass.continuous_of_bound L (max B 0 * ‖T.1‖) fun v => ?_
  calc ‖L v‖ ≤ B * ‖T.1 v‖ := norm_whittakerOne_le (fun y => hB _ (T.2.2 v) y) 1
    _ ≤ max B 0 * ‖T.1 v‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max B 0 * (‖T.1‖ * ‖v‖) := mul_le_mul_of_nonneg_left (T.1.le_opNorm v) (le_max_right _ _)
    _ = max B 0 * ‖T.1‖ * ‖v‖ := (mul_assoc _ _ _).symm

theorem whittakerOf_mem (T : cuspIntertwiners μ σ) : whittakerOf T ∈ whittakerFunctionals μ σ := by
  refine ⟨fun X w => ?_, fun f hf => ?_⟩
  · obtain ⟨F, hF⟩ := exists_hasContRep T w.2
    have h : HasContRep μ (T.1 (σ (uOne X) w)) (fun y => F (y * uOne X)) :=
      Eq.subst (motive := fun φ => HasContRep μ φ (fun y => F (y * uOne X)))
        (cuspIntertwiners_map T (uOne X) w).symm (hF.translate (uOne X))
    have h1 : (1 : normOneGL K n) * uOne X = uOne X * 1 := (one_mul _).trans (mul_one _).symm
    refine (whittakerOf_mk T _ h).trans ?_
    refine (whittakerOne_mul_right _ 1 (uOne X)).trans ((congrArg _ h1).trans
      ((whittakerOne_uOne_mul hF.1 hF.2.1 X 1).trans ?_))
    exact congrArg _ (whittakerAt_eq hF).symm
  · have e : ∀ v : H, whittakerOf T ⟨σ.integrated μ (UnitaryRep.ccToL1 μ f) v,
        integrated_mem_smoothSpan σ hf v⟩ = whittakerOne (rconv Γ₁ μ f (T.1 v)) 1 :=
      fun v => whittakerOf_mk T _ (hasContRep_intertwiner_integrated T f v)
    exact (continuous_whittakerOne_rconv_intertwiner T hf).congr fun v => (e v).symm

set_option maxHeartbeats 1000000 in

theorem eq_zero_of_whittakerOf_eq_zero (T : cuspIntertwiners μ σ) (h : whittakerOf T = 0) :
    T = 0 := by
  have key : ∀ v, T.1 v = 0 := by
    intro v
    refine eq_zero_of_forall_whittakerOne_rconv_eq_zero μ (T.2.2 v) fun f hf x => ?_
    have e := whittakerOf_generator T x hf v
    have e2 := LinearMap.congr_fun h ⟨σ x (σ.integrated μ (UnitaryRep.ccToL1 μ f) v),
      map_mem_smoothSpan σ x (integrated_mem_smoothSpan σ hf v)⟩
    exact e.symm.trans e2
  exact Subtype.ext (ContinuousLinearMap.ext key)

theorem whittakerAt_add (T₁ T₂ : cuspIntertwiners μ σ) {w : H} {F₁ F₂ : normOneGL K n → ℂ}
    (h₁ : HasContRep μ (T₁.1 w) F₁) (h₂ : HasContRep μ (T₂.1 w) F₂) :
    whittakerAt μ σ (T₁ + T₂) w = whittakerAt μ σ T₁ w + whittakerAt μ σ T₂ w := by
  have h : HasContRep μ ((T₁ + T₂).1 w) (F₁ + F₂) := by
    rw [Submodule.coe_add, add_apply]
    exact h₁.add h₂
  rw [whittakerAt_eq h, whittakerAt_eq h₁, whittakerAt_eq h₂, whittakerOne_add h₁.1 h₂.1]

theorem whittakerAt_smul (c : ℂ) (T₁ : cuspIntertwiners μ σ) {w : H} {F₁ : normOneGL K n → ℂ}
    (h₁ : HasContRep μ (T₁.1 w) F₁) :
    whittakerAt μ σ (c • T₁) w = c * whittakerAt μ σ T₁ w := by
  have h : HasContRep μ ((c • T₁).1 w) (c • F₁) := by
    rw [Submodule.coe_smul, smul_apply]
    exact h₁.smul c
  rw [whittakerAt_eq h, whittakerAt_eq h₁, whittakerOne_smul]

set_option maxHeartbeats 2000000 in
theorem whittakerAt_add' (T₁ T₂ : cuspIntertwiners μ σ) {w : H} (hw : w ∈ smoothSpan μ σ) :
    whittakerAt μ σ (T₁ + T₂) w = whittakerAt μ σ T₁ w + whittakerAt μ σ T₂ w := by
  obtain ⟨F₁, h₁⟩ := exists_hasContRep T₁ hw
  obtain ⟨F₂, h₂⟩ := exists_hasContRep T₂ hw
  exact whittakerAt_add T₁ T₂ h₁ h₂

set_option maxHeartbeats 2000000 in
theorem whittakerAt_smul' (c : ℂ) (T₁ : cuspIntertwiners μ σ) {w : H} (hw : w ∈ smoothSpan μ σ) :
    whittakerAt μ σ (c • T₁) w = c * whittakerAt μ σ T₁ w := by
  obtain ⟨F₁, h₁⟩ := exists_hasContRep T₁ hw
  exact whittakerAt_smul c T₁ h₁

theorem whittakerOf_add (T₁ T₂ : cuspIntertwiners μ σ) :
    whittakerOf (T₁ + T₂ : cuspIntertwiners μ σ) = whittakerOf T₁ + whittakerOf T₂ :=
  LinearMap.ext fun w => whittakerAt_add' T₁ T₂ w.2

theorem whittakerOf_smul (c : ℂ) (T₁ : cuspIntertwiners μ σ) :
    whittakerOf (c • T₁ : cuspIntertwiners μ σ) = c • whittakerOf T₁ :=
  LinearMap.ext fun w => whittakerAt_smul' c T₁ w.2

variable (μ σ) in

def whittakerMap : cuspIntertwiners μ σ →ₗ[ℂ] whittakerFunctionals μ σ where
  toFun T := ⟨whittakerOf T, whittakerOf_mem T⟩
  map_add' T₁ T₂ := Subtype.ext (whittakerOf_add T₁ T₂)
  map_smul' c T₁ := Subtype.ext (whittakerOf_smul c T₁)

theorem whittakerMap_injective : Function.Injective (whittakerMap μ σ) := by
  refine (injective_iff_map_eq_zero _).2 fun T hT => ?_
  exact eq_zero_of_whittakerOf_eq_zero T (congrArg Subtype.val hT)

set_option maxHeartbeats 2000000 in
variable (μ σ) in

theorem rank_cuspIntertwiners_le_one (h : Module.rank ℂ (whittakerFunctionals μ σ) ≤ 1) :
    Module.rank ℂ (cuspIntertwiners μ σ) ≤ 1 := by
  have h1 := LinearMap.lift_rank_le_of_injective (whittakerMap μ σ) whittakerMap_injective
  exact Cardinal.lift_le_one_iff.1 (h1.trans (Cardinal.lift_le_one_iff.2 h))

end MultiplicityOne

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep (normOneGL K n) H}

set_option maxHeartbeats 2000000 in

theorem isCompactOperator_integrated_comp_of_bound (T : cuspIntertwiners μ σ)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (B : ℝ)
    (hB : ∀ φ ∈ cuspidalL2 μ, ∀ x, ‖rconv Γ₁ μ f φ x‖ ≤ B * ‖φ‖) :
    IsCompactOperator ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L T.1) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  let e : RightCosetSpace Γ₁ → StrongDual ℂ H := fun q =>
    (rconvCLM Γ₁ μ f (Quotient.out q)).comp T.1
  have he : ∀ q, ‖e q‖ ≤ max B 0 * ‖T.1‖ := by
    intro q
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (le_max_right _ _) (norm_nonneg _)) fun v => ?_
    change ‖rconv Γ₁ μ f (T.1 v) (Quotient.out q)‖ ≤ _
    refine (hB _ (T.2.2 v) _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul (le_max_left _ _) (T.1.le_opNorm v) (norm_nonneg _) (le_max_right _ _)
  have hout : ∀ (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (q : RightCosetSpace Γ₁),
      rconvQ Γ₁ μ f φ q = rconv Γ₁ μ f φ (Quotient.out q) := by
    intro φ q
    obtain ⟨a, rfl⟩ := mk_surjective Γ₁ q
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Γ₁)).1 (Quotient.out_eq (mk Γ₁ a))
    rw [rconvQ_mk, ← hγ]
    exact (rconv_mul_left Γ₁ μ f φ γ.2 a).symm
  have hae : ∀ v, ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L T.1) v =ᵐ[quotientMeasure Γ₁ μ]
      fun q => e q v := by
    intro v
    filter_upwards [integrated_ae_eq_rconvQ Γ₁ μ f (T.1 v)] with q hq
    exact hq.trans (hout _ q)
  exact (isHilbertSchmidt_of_ae_eq_dual _ e _ he hae).isCompactOperator

omit [NumberField K] [μ.IsHaarMeasure] [CompleteSpace H] in
theorem exists_pos_mul_add_one_lt {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' * (a + 1) < ε := by
  refine ⟨ε / (2 * (a + 1)), div_pos hε (by positivity), ?_⟩
  have h : ε / (2 * (a + 1)) * (a + 1) = ε / 2 := by field_simp
  rw [h]
  linarith

set_option maxHeartbeats 8000000 in

theorem isCompactOperator_integrated_comp (T : cuspIntertwiners μ σ)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    IsCompactOperator ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L T.1) := by
  have hcl := isClosed_setOfPred_isCompactOperator (𝕜₁ := ℂ) (σ₁₂ := RingHom.id ℂ)
    (M₁ := H) (M₂ := Lp ℂ 2 (quotientMeasure Γ₁ μ))
  refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨ε', hε', hεε⟩ := exists_pos_mul_add_one_lt (norm_nonneg T.1) hε
  obtain ⟨f', ⟨B, hB⟩, hff'⟩ :=
    exists_approx_bound μ (Measure.haar : Measure (ArchUnits K n)) f hε'
  refine ⟨_, isCompactOperator_integrated_comp_of_bound T f' B hB, ?_⟩
  rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
  calc ‖((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) -
        (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f')) ∘L T.1‖
      ≤ ‖(rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) -
        (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f')‖ * ‖T.1‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ε' * (‖T.1‖ + 1) := by
        refine mul_le_mul ?_ (le_add_of_nonneg_right zero_le_one) (norm_nonneg _) hε'.le
        rw [← dist_eq_norm]
        exact ((rightRegularRep Γ₁ μ).dist_integrated_ccToL1_le μ f f').trans hff'
    _ < ε := hεε

set_option maxHeartbeats 4000000 in

theorem isCompactOperator_integrated_of_irreducible (hσ : σ.IsIrreducible)
    (T : cuspIntertwiners μ σ) (hT0 : T ≠ 0)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    IsCompactOperator (σ.integrated μ (UnitaryRep.ccToL1 μ f)) := by
  obtain ⟨c, hc⟩ := hσ.exists_eq_smul_one (UnitaryRep.comp_mem_intertwiners
    (UnitaryRep.adjoint_mem_intertwiners T.2.1) T.2.1)
  have hT0' : T.1 ≠ 0 := fun h => hT0 (Subtype.ext h)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hT0'
    refine ContinuousLinearMap.ext fun k => ?_
    have h := congrArg (fun A : H →L[ℂ] H => inner ℂ k (A k)) hc
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, zero_smul] at h
    simpa using h
  have hint := UnitaryRep.comp_integrated_of_mem_intertwiners σ μ T.2.1 (UnitaryRep.ccToL1 μ f)
  have e : ContinuousLinearMap.adjoint T.1 ∘L
      ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L T.1) =
      c • σ.integrated μ (UnitaryRep.ccToL1 μ f) := by
    rw [← hint, ← ContinuousLinearMap.comp_assoc, hc, ContinuousLinearMap.smul_comp,
      ← ContinuousLinearMap.mul_def, one_mul]
  have e2 : σ.integrated μ (UnitaryRep.ccToL1 μ f) = c⁻¹ • (ContinuousLinearMap.adjoint T.1 ∘L
      ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L T.1)) := by
    rw [e, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e2, FunLike.coe_smul, ContinuousLinearMap.coe_comp]
  exact ((isCompactOperator_integrated_comp T f).clm_comp (ContinuousLinearMap.adjoint T.1)).smul c⁻¹

end MultiplicityOne

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (K n) in

def finComp : normOneGL K n →* AdelicGLn.FiniteAdelicGL K n :=
  (MonoidHom.snd _ _).comp ((AdelicGLn.prodEquiv K n).toMonoidHom.comp (normOneGL K n).subtype)

theorem finComp_apply (x : normOneGL K n) :
    finComp K n x = (AdelicGLn.prodEquiv K n (x : AdelicGLn.AdelicGL K n)).2 := rfl

theorem continuous_finComp : Continuous (finComp K n) :=
  continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp continuous_subtype_val)

theorem finComp_archProj (A : ArchUnits K n) : finComp K n (archProj K n A) = 1 := by
  rw [finComp_apply, coe_archProj, map_mul, map_inv]
  have h1 : (AdelicGLn.prodEquiv K n (archIncl K n A)).2 = 1 := by
    show (AdelicGLn.prodEquiv K n (infEmb K n ⟨A, trivial⟩)).2 = 1
    rw [prodEquiv_infEmb]
  have h2 : (AdelicGLn.prodEquiv K n (centralSection K n
      (detModule K n (archIncl K n A)))).2 = 1 := by
    rw [centralSection, MonoidHom.comp_apply, scalarUnits_apply]
    exact prodEquiv_diagUnits_posIdele_snd (K := K) (n := n)
      (fun _ => ((rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ (detModule K n (archIncl K n A)) :
        {r : ℝ // 0 < r}) : ℝ)) (fun _ => (rpowHom _ _).2)
  simp only [Prod.snd_mul, Prod.snd_inv, h1, h2, inv_one, mul_one]

theorem finComp_finProj (u : AdelicGLn.FiniteAdelicGL K n) : finComp K n (finProj K n u) = u := by
  rw [finComp_apply, coe_finProj, map_mul, map_inv]
  have h1 : (AdelicGLn.prodEquiv K n (finEmb K n u)).2 = u := by rw [prodEquiv_finEmb]
  have h2 : (AdelicGLn.prodEquiv K n (centralSection K n
      (detModule K n (finEmb K n u)))).2 = 1 := by
    rw [centralSection, MonoidHom.comp_apply, scalarUnits_apply]
    exact prodEquiv_diagUnits_posIdele_snd (K := K) (n := n)
      (fun _ => ((rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ (detModule K n (finEmb K n u)) :
        {r : ℝ // 0 < r}) : ℝ)) (fun _ => (rpowHom _ _).2)
  simp only [Prod.snd_mul, Prod.snd_inv, h1, h2, inv_one, mul_one]

variable (K n) in

def levelSubgroup (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) : Subgroup (normOneGL K n) :=
  U.comap (finComp K n)

theorem mem_levelSubgroup {U : Subgroup (AdelicGLn.FiniteAdelicGL K n)} {x : normOneGL K n} :
    x ∈ levelSubgroup K n U ↔ finComp K n x ∈ U := Iff.rfl

theorem isOpen_levelSubgroup {U : Subgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hU : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n))) :
    IsOpen (levelSubgroup K n U : Set (normOneGL K n)) :=
  hU.preimage continuous_finComp



theorem exists_of_mem_levelSubgroup {U : Subgroup (AdelicGLn.FiniteAdelicGL K n)}
    {x : normOneGL K n} (hx : x ∈ levelSubgroup K n U) :
    ∃ (A : ArchUnits K n) (u : AdelicGLn.FiniteAdelicGL K n), u ∈ U ∧
      archProj K n A * finProj K n u = x := by
  obtain ⟨A, u, rfl⟩ := exists_archProj_mul_finProj x
  refine ⟨A, u, ?_, rfl⟩
  have := (mem_levelSubgroup).1 hx
  rwa [map_mul, finComp_archProj, finComp_finProj, one_mul] at this

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fixedSubspace (σ : UnitaryRep (normOneGL K n) H) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) :
    Submodule ℂ H where
  carrier := {v | ∀ u ∈ U, σ (finProj K n u) v = v}
  add_mem' hv hw u hu := by rw [map_add, hv u hu, hw u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

theorem mem_fixedSubspace {σ : UnitaryRep (normOneGL K n) H}
    {U : Subgroup (AdelicGLn.FiniteAdelicGL K n)} {v : H} :
    v ∈ fixedSubspace σ U ↔ ∀ u ∈ U, σ (finProj K n u) v = v := Iff.rfl

theorem isClosed_fixedSubspace (σ : UnitaryRep (normOneGL K n) H)
    (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) :
    IsClosed (fixedSubspace σ U : Set H) := by
  have e : (fixedSubspace σ U : Set H) =
      ⋂ u ∈ U, {v | σ (finProj K n u) v = v} := by
    ext v
    simp only [SetLike.mem_coe, mem_fixedSubspace, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [e]
  exact isClosed_biInter fun u _ => isClosed_eq (σ (finProj K n u)).continuous continuous_id

theorem isInvariant_fixedSubspace (σ : UnitaryRep (normOneGL K n) H)
    (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) :
    (σ.compHom (levelSubgroup K n U).subtype continuous_subtype_val).IsInvariant
      (fixedSubspace σ U) := by
  rintro ⟨x, hx⟩ v hv u hu
  obtain ⟨A, u', hu', rfl⟩ := exists_of_mem_levelSubgroup hx
  show σ (finProj K n u) (σ (archProj K n A * finProj K n u') v) = σ (archProj K n A * finProj K n u') v
  have e : finProj K n u * (archProj K n A * finProj K n u') =
      archProj K n A * finProj K n u' * finProj K n (u'⁻¹ * u * u') := by
    rw [map_mul, map_mul, map_inv, ← mul_assoc, finProj_mul_archProj_comm]
    group
  rw [← UnitaryRep.map_mul_apply, e, UnitaryRep.map_mul_apply,
    hv _ (U.mul_mem (U.mul_mem (U.inv_mem hu') hu) hu')]

variable (σ : UnitaryRep (normOneGL K n) H) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n))

instance : CompleteSpace (fixedSubspace σ U) := (isClosed_fixedSubspace σ U).completeSpace_coe

def levelRep : UnitaryRep (levelSubgroup K n U) (fixedSubspace σ U) :=
  (σ.compHom (levelSubgroup K n U).subtype continuous_subtype_val).restrict (fixedSubspace σ U)
    (isInvariant_fixedSubspace σ U)

@[simp] theorem coe_levelRep_apply (x : levelSubgroup K n U) (v : fixedSubspace σ U) :
    ((levelRep σ U x v : fixedSubspace σ U) : H) = σ x v := rfl

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

set_option maxHeartbeats 4000000 in

theorem isCompactOperator_levelRep (hσ : σ.IsIrreducible) (T : cuspIntertwiners μ σ) (hT0 : T ≠ 0)
    (hU : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)))
    (f : CompactlySupportedContinuousMap (levelSubgroup K n U) ℂ) :
    haveI := UnitaryRep.isFiniteMeasureOnCompacts_comap μ (isOpen_levelSubgroup (K := K) (n := n) hU)
    IsCompactOperator ((levelRep σ U).integrated (μ.comap ((↑) : levelSubgroup K n U → normOneGL K n))
      (UnitaryRep.ccToL1 (μ.comap ((↑) : levelSubgroup K n U → normOneGL K n)) f)) := by
  have := UnitaryRep.isFiniteMeasureOnCompacts_comap μ (isOpen_levelSubgroup (K := K) (n := n) hU)
  refine UnitaryRep.isCompactOperator_restrict_integrated _ _ (isClosed_fixedSubspace σ U)
    (isInvariant_fixedSubspace σ U) _ ?_
  exact UnitaryRep.isCompactOperator_compHom_subtype σ μ (isOpen_levelSubgroup hU)
    (isCompactOperator_integrated_of_irreducible hσ T hT0) f

end MultiplicityOne

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep (normOneGL K n) H)

abbrev archRep : UnitaryRep (ArchUnits K n) H := σ.compHom (archProj K n) continuous_archProj

variable (V₀ : Submodule ℂ H) [CompleteSpace V₀] (hV₀ : (archRep σ).IsInvariant V₀)

def archType : UnitaryRep (ArchUnits K n) V₀ := (archRep σ).restrict V₀ hV₀

def homArch : Submodule ℂ (V₀ →L[ℂ] H) := (archType σ V₀ hV₀).intertwiners (archRep σ)

theorem finProj_comp_mem_homArch (w : AdelicGLn.FiniteAdelicGL K n) {S : V₀ →L[ℂ] H}
    (hS : S ∈ homArch σ V₀ hV₀) : σ (finProj K n w) ∘L S ∈ homArch σ V₀ hV₀ := by
  intro A v
  show σ (finProj K n w) (S (archType σ V₀ hV₀ A v)) = σ (archProj K n A) (σ (finProj K n w) (S v))
  rw [hS A v]
  show σ (finProj K n w) (σ (archProj K n A) (S v)) = σ (archProj K n A) (σ (finProj K n w) (S v))
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, finProj_mul_archProj_comm]

def HomSpace : Type _ := homArch σ V₀ hV₀

instance : AddCommGroup (HomSpace σ V₀ hV₀) := inferInstanceAs (AddCommGroup (homArch σ V₀ hV₀))

instance : Module ℂ (HomSpace σ V₀ hV₀) := inferInstanceAs (Module ℂ (homArch σ V₀ hV₀))

def HomSpace.op (S : HomSpace σ V₀ hV₀) : V₀ →L[ℂ] H := (S : homArch σ V₀ hV₀).1

def finRep : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) (HomSpace σ V₀ hV₀) where
  toFun w :=
    { toFun := fun S => (⟨σ (finProj K n w) ∘L (S : homArch σ V₀ hV₀).1,
        finProj_comp_mem_homArch σ V₀ hV₀ w (S : homArch σ V₀ hV₀).2⟩ : homArch σ V₀ hV₀)
      map_add' := fun S S' => Subtype.ext (ContinuousLinearMap.comp_add _ _ _)
      map_smul' := fun c S => Subtype.ext (ContinuousLinearMap.comp_smul _ _ _) }
  map_one' := by
    refine LinearMap.ext fun S => Subtype.ext ?_
    show σ (finProj K n 1) ∘L (S : homArch σ V₀ hV₀).1 = (S : homArch σ V₀ hV₀).1
    rw [map_one, UnitaryRep.map_one]
    exact ContinuousLinearMap.id_comp _
  map_mul' w w' := by
    refine LinearMap.ext fun S => Subtype.ext ?_
    show σ (finProj K n (w * w')) ∘L (S : homArch σ V₀ hV₀).1 =
      σ (finProj K n w) ∘L (σ (finProj K n w') ∘L (S : homArch σ V₀ hV₀).1)
    rw [map_mul, UnitaryRep.map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

def FinitePartSpace : Type _ := smoothVectors (finRep σ V₀ hV₀)

instance : AddCommGroup (FinitePartSpace σ V₀ hV₀) :=
  inferInstanceAs (AddCommGroup (smoothVectors (finRep σ V₀ hV₀)))

instance : Module ℂ (FinitePartSpace σ V₀ hV₀) :=
  inferInstanceAs (Module ℂ (smoothVectors (finRep σ V₀ hV₀)))

def finitePart : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) (FinitePartSpace σ V₀ hV₀) :=
  smoothPart (finRep σ V₀ hV₀)

def fpOp (S : FinitePartSpace σ V₀ hV₀) : V₀ →L[ℂ] H :=
  HomSpace.op σ V₀ hV₀ (S : smoothVectors (finRep σ V₀ hV₀)).1

theorem fpOp_finitePart (w : AdelicGLn.FiniteAdelicGL K n) (S : FinitePartSpace σ V₀ hV₀) :
    fpOp σ V₀ hV₀ (finitePart σ V₀ hV₀ w S) = σ (finProj K n w) ∘L fpOp σ V₀ hV₀ S := rfl

theorem fpOp_mem_homArch (S : FinitePartSpace σ V₀ hV₀) : fpOp σ V₀ hV₀ S ∈ homArch σ V₀ hV₀ :=
  ((S : smoothVectors (finRep σ V₀ hV₀)).1 : homArch σ V₀ hV₀).2

section Admissible

variable {σ V₀}
variable {U₀ : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hV₀U : V₀ ≤ fixedSubspace σ U₀)

include hV₀ hV₀U in

theorem isInvariant_levelSubgroup {U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hU' : U' ≤ U₀) :
    (σ.compHom (levelSubgroup K n U').subtype continuous_subtype_val).IsInvariant V₀ := by
  rintro ⟨x, hx⟩ v hv
  obtain ⟨A, u, hu, rfl⟩ := exists_of_mem_levelSubgroup hx
  show σ (archProj K n A * finProj K n u) v ∈ V₀
  rw [UnitaryRep.map_mul_apply, hV₀U hv u (hU' hu)]
  exact hV₀ A v hv

def levelType {U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hU' : U' ≤ U₀) :
    UnitaryRep (levelSubgroup K n U') V₀ :=
  (σ.compHom (levelSubgroup K n U').subtype continuous_subtype_val).restrict V₀
    (isInvariant_levelSubgroup hV₀ hV₀U hU')

theorem fpOp_fixed {U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)}
    (S : fixedVectors (finitePart σ V₀ hV₀) U') {u : AdelicGLn.FiniteAdelicGL K n} (hu : u ∈ U')
    (v : V₀) : σ (finProj K n u) (fpOp σ V₀ hV₀ S.1 v) = fpOp σ V₀ hV₀ S.1 v := by
  have h := congrArg (fpOp σ V₀ hV₀) (S.2 u hu)
  rw [fpOp_finitePart] at h
  exact congrArg (fun T : V₀ →L[ℂ] H => T v) h

def toLevelHom {U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hU' : U' ≤ U₀) :
    fixedVectors (finitePart σ V₀ hV₀) U' →ₗ[ℂ]
      (levelType hV₀ hV₀U hU').intertwiners (levelRep σ U') where
  toFun S := ⟨(fpOp σ V₀ hV₀ S.1).codRestrict (fixedSubspace σ U')
      (fun v u hu => fpOp_fixed hV₀ S hu v),
    by
      rintro ⟨x, hx⟩ v
      obtain ⟨A, u, hu, rfl⟩ := exists_of_mem_levelSubgroup hx
      refine Subtype.ext ?_
      have hvA : σ (archProj K n A * finProj K n u) v = σ (archProj K n A) v := by
        rw [UnitaryRep.map_mul_apply, hV₀U v.2 u (hU' hu)]
      have e : (levelType hV₀ hV₀U hU' ⟨_, hx⟩ v : V₀) = archType σ V₀ hV₀ A v := Subtype.ext hvA
      calc fpOp σ V₀ hV₀ S.1 (levelType hV₀ hV₀U hU' ⟨_, hx⟩ v)
          = fpOp σ V₀ hV₀ S.1 (archType σ V₀ hV₀ A v) := congrArg _ e
        _ = σ (archProj K n A) (fpOp σ V₀ hV₀ S.1 v) := fpOp_mem_homArch σ V₀ hV₀ S.1 A v
        _ = σ (archProj K n A * finProj K n u) (fpOp σ V₀ hV₀ S.1 v) := by
            rw [UnitaryRep.map_mul_apply, fpOp_fixed hV₀ S hu v]⟩
  map_add' S S' := rfl
  map_smul' c S := rfl

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

end Admissible

end MultiplicityOne

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep (normOneGL K n) H}
variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

theorem map_integrated_of_left_invariant {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    {h : normOneGL K n} (hf : ∀ x, f (h⁻¹ * x) = f x) (v : H) :
    σ h (σ.integrated μ (UnitaryRep.ccToL1 μ f) v) = σ.integrated μ (UnitaryRep.ccToL1 μ f) v := by
  have e := σ.map_comp_integrated μ h (UnitaryRep.ccToL1 μ f)
  have e2 : UnitaryRep.leftTranslate μ h (UnitaryRep.ccToL1 μ f) = UnitaryRep.ccToL1 μ f := by
    refine Lp.ext ?_
    have hc := (f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 1)
      f.hasCompactSupport).coeFn_toLp
    filter_upwards [UnitaryRep.coeFn_leftTranslate μ h (UnitaryRep.ccToL1 μ f), hc,
      (measurePreserving_mul_left μ h⁻¹).quasiMeasurePreserving.ae_eq_comp hc] with x h1 h2 h3
    rw [h1]
    change (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) (h⁻¹ * x) = (UnitaryRep.ccToL1 μ f) x
    rw [show (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) (h⁻¹ * x) = f (h⁻¹ * x) from h3,
      show (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) x = f x from h2]
    exact hf x
  rw [e2] at e
  exact congrArg (fun A : H →L[ℂ] H => A v) e

theorem exists_fixedSubspace_ne_bot (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (hσ : σ.IsIrreducible) :
    ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n))
      (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))),
      fixedSubspace σ (openSubgroupOf U hU : Subgroup (AdelicGLn.FiniteAdelicGL K n)) ≠ ⊥ := by
  have := hσ.1
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨g, hg⟩ := UnitaryRep.exists_integrated_ne_zero σ μ hv
  obtain ⟨f, hf, hfv⟩ : ∃ f, IsSmoothTest f ∧ σ.integrated μ (UnitaryRep.ccToL1 μ f) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg (UnitaryRep.integrated_eq_zero_of_dense σ μ IsSmoothTest
      (fun g' ε hε => exists_isSmoothTest_near μ g' hε) hcon g)
  obtain ⟨U, hU, hinv⟩ := hf.exists_finOne_mul
  refine ⟨U, hU, fun hbot => hfv ?_⟩
  have hmem : σ.integrated μ (UnitaryRep.ccToL1 μ f) v ∈
      fixedSubspace σ (openSubgroupOf U hU : Subgroup (AdelicGLn.FiniteAdelicGL K n)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.coe_subtype, finProj_eq_finOne]
    refine map_integrated_of_left_invariant (fun x => ?_) v
    rw [← map_inv]
    exact hinv u⁻¹ (U.inv_mem hu) x
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℂ).1 hmem

end MultiplicityOne

end

end GroundTheory.Automorphic
end
