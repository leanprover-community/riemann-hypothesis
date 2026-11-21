import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalUnfold
import GroundTheory.AutomorphicForms.GL2.GJGlobalMean
import GroundTheory.AutomorphicForms.GL2.GJGlobalHaar
import GroundTheory.AutomorphicForms.GL2.IdeleModuleDetOfMemMaxCompact
import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import GroundTheory.AutomorphicForms.GL2.GJGlobalLatticeSummable

section
open Matrix

namespace GroundTheory.Automorphic

namespace GJGlobal

variable {K : Type*} [Field K] {n : ℕ}

theorem rank_eq_iff_isUnit_det (ξ : Matrix (Fin n) (Fin n) K) : ξ.rank = n ↔ IsUnit ξ.det := by
  constructor
  · intro h
    rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
    have hs : Function.Surjective ξ.mulVecLin := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      exact h
    exact LinearMap.injective_iff_surjective.2 hs
  · intro h
    have := rank_of_isUnit ξ ((isUnit_iff_isUnit_det ξ).2 h)
    rwa [Fintype.card_fin] at this

theorem rank_lt_of_det_eq_zero {ξ : Matrix (Fin n) (Fin n) K} (h : ξ.det = 0) : ξ.rank < n := by
  have hle : ξ.rank ≤ n := by
    have := rank_le_card_width ξ
    rwa [Fintype.card_fin] at this
  refine lt_of_le_of_ne hle fun he => ?_
  have := (rank_eq_iff_isUnit_det ξ).1 he
  rw [h] at this
  exact not_isUnit_zero this

theorem rank_eq_zero_iff {ξ : Matrix (Fin n) (Fin n) K} : ξ.rank = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    have hr : LinearMap.range ξ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h
    have hz : ξ.mulVecLin = 0 := LinearMap.range_eq_bot.1 hr
    ext i j
    have := congrFun (congrArg DFunLike.coe hz) (Pi.single j 1)
    simpa [mulVecLin_apply, mulVec_single_one] using congrFun this i
  · rintro rfl
    exact rank_zero

noncomputable def unitsEquiv : GL (Fin n) K ≃ {ξ : Matrix (Fin n) (Fin n) K // IsUnit ξ.det} where
  toFun γ := ⟨γ, (isUnit_iff_isUnit_det _).1 γ.isUnit⟩
  invFun ξ := ((isUnit_iff_isUnit_det _).2 ξ.2).unit
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem tsum_eq_tsum_GL_add {f : Matrix (Fin n) (Fin n) K → E} (hf : Summable f) :
    ∑' ξ, f ξ = ∑' γ : GL (Fin n) K, f γ + ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0}, f ξ := by
  rw [← hf.tsum_subtype_add_tsum_subtype_compl {ξ | IsUnit ξ.det}]
  congr 1
  · exact ((unitsEquiv (K := K) (n := n)).tsum_eq (fun ξ => f ξ)).symm
  · have e : ({ξ | IsUnit ξ.det}ᶜ : Set (Matrix (Fin n) (Fin n) K)) = {ξ | ξ.det = 0} := by
      ext ξ
      simp [isUnit_iff_ne_zero]
    rw [e]
    rfl

theorem tsum_det_eq_zero_eq_sum_rank {f : Matrix (Fin n) (Fin n) K → E} (hf : Summable f) :
    ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0}, f ξ =
      ∑ r : Fin n, ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r}, f ξ := by
  have e : {ξ : Matrix (Fin n) (Fin n) K | ξ.det = 0} =
      ⋃ r ∈ (Finset.univ : Finset (Fin n)), {ξ | ξ.rank = (r : ℕ)} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨⟨ξ.rank, rank_lt_of_det_eq_zero h⟩, rfl⟩
    · rintro ⟨r, hr⟩
      by_contra h
      have := (rank_eq_iff_isUnit_det ξ).2 (isUnit_iff_ne_zero.2 h)
      have hr' := r.2
      omega
  have hd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Disjoint fun r : Fin n => {ξ : Matrix (Fin n) (Fin n) K | ξ.rank = (r : ℕ)}) := by
    intro r _ r' _ hrr'
    refine Set.disjoint_left.2 fun ξ h h' => hrr' (Fin.ext ?_)
    simp only [Set.mem_ofPred_eq] at h h'
    rw [← h, ← h']
  have hsum := hasSum_sum_disjoint (f := f) Finset.univ hd fun r _ => (hf.subtype _).hasSum
  show ∑' ξ : ({ξ | ξ.det = 0} : Set (Matrix (Fin n) (Fin n) K)), f ξ = _
  rw [e]
  exact hsum.tsum_eq

end GJGlobal

end GroundTheory.Automorphic
end

section
open MeasureTheory NumberField Set ComplexConjugate
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction RightCosetSpace GroundTheory.Global

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def ratElt (γ : GL (Fin n) K) : normOneGL K n :=
  ⟨AdelicGLn.diagonal K n γ, rationalGL_le_normOneGL ⟨γ, rfl⟩⟩

@[simp] theorem coe_ratElt (γ : GL (Fin n) K) :
    ((ratElt γ : normOneGL K n) : AdelicGLn.AdelicGL K n) = AdelicGLn.diagonal K n γ :=
  rfl

theorem ratElt_mem (γ : GL (Fin n) K) : ratElt γ ∈ rationalGLOne K n :=
  Subgroup.mem_subgroupOf.2 ⟨γ, rfl⟩

def ratEquiv : GL (Fin n) K ≃ rationalGLOne K n :=
  Equiv.ofBijective (fun γ => ⟨ratElt γ, ratElt_mem γ⟩)
    ⟨fun γ γ' h => AdelicGLn.diagonal_injective K n
      (congrArg (fun x : rationalGLOne K n => ((x : normOneGL K n) : AdelicGLn.AdelicGL K n)) h),
     fun x => by
       obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 x.2
       exact ⟨γ, Subtype.ext (Subtype.ext hγ)⟩⟩

@[simp] theorem coe_ratEquiv (γ : GL (Fin n) K) :
    ((ratEquiv γ : rationalGLOne K n) : normOneGL K n) = ratElt γ :=
  rfl

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem lintegral_eq_setLIntegral_tsum {h : normOneGL K n → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ y, h y ∂μ = ∫⁻ y in fundamentalDomain (rationalGLOne K n),
      ∑' γ : GL (Fin n) K, h (ratElt γ * y) ∂μ := by
  rw [lintegral_eq_lintegral_automorphize (Γ := rationalGLOne K n) μ hh.aemeasurable,
    lintegral_quotientMeasure]
  refine lintegral_congr fun y => ?_
  change ∑' γ : rationalGLOne K n, h (γ • y) = _
  rw [← (ratEquiv (K := K) (n := n)).tsum_eq]
  rfl

theorem integral_eq_setIntegral_tsum {h : normOneGL K n → ℂ} (hh : Integrable h μ) :
    ∫ y, h y ∂μ = ∫ y in fundamentalDomain (rationalGLOne K n),
      ∑' γ : GL (Fin n) K, h (ratElt γ * y) ∂μ := by
  rw [integral_eq_integral_automorphize (Γ := rationalGLOne K n) μ hh, integral_quotientMeasure]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ∑' γ : rationalGLOne K n, h (γ • y) = _
  rw [← (ratEquiv (K := K) (n := n)).tsum_eq]
  rfl

theorem measure_fundamentalDomain_rationalGLOne_lt_top :
    μ (fundamentalDomain (rationalGLOne K n)) < ⊤ := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  exact (measure_fundamentalDomain_pos_lt_top (rationalGLOne K n) μ).2

theorem lintegral_posRealMeasure (f : ℝ → ℝ≥0∞) :
    ∫⁻ t, f t ∂posRealMeasure = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * f t := by
  rw [posRealMeasure]
  have h := lintegral_subtype_comap (μ := volume.withDensity fun t : ℝ ↦ ENNReal.ofReal t⁻¹)
    (s := Ioi (0 : ℝ)) measurableSet_Ioi f
  refine h.trans ?_
  have hm : Measurable fun t : ℝ ↦ ENNReal.ofReal t⁻¹ := ENNReal.measurable_ofReal.comp measurable_inv
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ hm f measurableSet_Ioi
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rfl

section Pairing

variable {φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ}

theorem lintegral_enorm_translate_eq (hφ₁ : Continuous φ₁) (hφ₁l : AutomorphicForm.IsLeftInvariant φ₁)
    (hΞ : Continuous Ξ) (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n) :
    ∫⁻ y, ‖Ξ (centralSection K n s * x * (y : AdelicGLn.AdelicGL K n))‖ₑ *
        ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ ∂μ =
      ∫⁻ y in fundamentalDomain (rationalGLOne K n), ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ *
        ∑' γ : GL (Fin n) K, ‖Ξ (centralSection K n s * x * AdelicGLn.diagonal K n γ *
          (y : AdelicGLn.AdelicGL K n))‖ₑ ∂μ := by
  have hm : Measurable fun y : normOneGL K n =>
      ‖Ξ (centralSection K n s * x * (y : AdelicGLn.AdelicGL K n))‖ₑ *
        ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ :=
    (hΞ.comp (continuous_const.mul continuous_subtype_val)).enorm.measurable.mul
      (hφ₁.comp continuous_subtype_val).enorm.measurable
  rw [lintegral_eq_setLIntegral_tsum μ hm]
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun γ => ?_
  simp only [Subgroup.coe_mul, coe_ratElt]
  rw [hφ₁l, mul_comm]
  simp only [mul_assoc]

theorem enorm_mul_lintegral_le (hφ₁ : Continuous φ₁) (hφ₁l : AutomorphicForm.IsLeftInvariant φ₁)
    (hΞ : Continuous Ξ) {B : ℝ → ℝ}
    (hB : ∀ (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n), x ∈ normOneGL K n →
      y ∈ normOneGL K n →
      Summable (fun γ : GL (Fin n) K =>
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖) ∧
      ‖φ₂ x‖ * ‖φ₁ y‖ * ∑' γ : GL (Fin n) K,
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖ ≤ B t)
    (s : {r : ℝ // 0 < r}) (x : normOneGL K n) :
    ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ *
        ∫⁻ y, ‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          (y : AdelicGLn.AdelicGL K n))‖ₑ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ ∂μ ≤
      ENNReal.ofReal (B s) * μ (fundamentalDomain (rationalGLOne K n)) := by
  rw [lintegral_enorm_translate_eq μ hφ₁ hφ₁l hΞ, ← lintegral_const_mul' _ _ enorm_ne_top,
    ← setLIntegral_const]
  refine lintegral_mono fun y => ?_
  obtain ⟨hs, hle⟩ := hB s x y x.2 y.2
  have e1 : ∑' γ : GL (Fin n) K, ‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ₑ =
      ENNReal.ofReal (∑' γ : GL (Fin n) K, ‖Ξ (centralSection K n s *
        (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
    simp only [ofReal_norm]
  rw [e1, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_assoc]
  exact hle

theorem lintegral_lintegral_enorm_le (hφ₁ : Continuous φ₁) (hφ₁l : AutomorphicForm.IsLeftInvariant φ₁)
    (hΞ : Continuous Ξ) {B : ℝ → ℝ}
    (hB : ∀ (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n), x ∈ normOneGL K n →
      y ∈ normOneGL K n →
      Summable (fun γ : GL (Fin n) K =>
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖) ∧
      ‖φ₂ x‖ * ‖φ₁ y‖ * ∑' γ : GL (Fin n) K,
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖ ≤ B t)
    (s : {r : ℝ // 0 < r}) :
    ∫⁻ x in fundamentalDomain (rationalGLOne K n), ∫⁻ y,
        ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ ∂μ ≤
      ENNReal.ofReal (B s) * μ (fundamentalDomain (rationalGLOne K n)) *
        μ (fundamentalDomain (rationalGLOne K n)) := by
  rw [← setLIntegral_const]
  refine lintegral_mono fun x => ?_
  have h1 : ∫⁻ y, ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
        ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
        ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ =
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ *
        ∫⁻ y, ‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          (y : AdelicGLn.AdelicGL K n))‖ₑ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ ∂μ := by
    calc ∫⁻ y, ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ
        = ∫⁻ y, (fun y : normOneGL K n => ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ *
            (‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
              (y : AdelicGLn.AdelicGL K n))‖ₑ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ)) (x * y) ∂μ := by
          refine lintegral_congr fun y => ?_
          simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left]
          ring
      _ = ∫⁻ y, ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ *
            (‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
              (y : AdelicGLn.AdelicGL K n))‖ₑ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ) ∂μ :=
          lintegral_mul_left_eq_self (μ := μ) (fun y : normOneGL K n =>
            ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ * (‖Ξ (centralSection K n s *
              (x : AdelicGLn.AdelicGL K n)⁻¹ * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ)) x
      _ = _ := lintegral_const_mul' _ _ enorm_ne_top
  rw [h1]
  exact enorm_mul_lintegral_le μ hφ₁ hφ₁l hΞ hB s x

end Pairing

section Identity

variable {φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ}

theorem integral_mul_matrixCoeff_eq_thetaPairing (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂)
    (hφ₁l : AutomorphicForm.IsLeftInvariant φ₁) (hΞ : Continuous Ξ) {B : ℝ → ℝ}
    (hB : ∀ (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n), x ∈ normOneGL K n →
      y ∈ normOneGL K n →
      Summable (fun γ : GL (Fin n) K =>
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖) ∧
      ‖φ₂ x‖ * ‖φ₁ y‖ * ∑' γ : GL (Fin n) K,
        ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖ ≤ B t)
    (s : {r : ℝ // 0 < r}) :
    ∫ y, Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) *
        matrixCoeff μ φ₁ φ₂ (y : AdelicGLn.AdelicGL K n) ∂μ = thetaPairing μ φ₁ φ₂ Ξ s := by
  set F := fundamentalDomain (rationalGLOne K n) with hF
  have hFfin := measure_fundamentalDomain_rationalGLOne_lt_top μ
  set f : normOneGL K n → normOneGL K n → ℂ := fun y x =>
    Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) *
      (φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n)) *
        conj (φ₂ (x : AdelicGLn.AdelicGL K n))) with hfdef
  have hcont : Continuous (Function.uncurry f) :=
    (hΞ.comp (continuous_const.mul (continuous_subtype_val.comp continuous_fst))).mul
      ((hφ₁.comp ((continuous_subtype_val.comp continuous_snd).mul
        (continuous_subtype_val.comp continuous_fst))).mul
        (Complex.continuous_conj.comp (hφ₂.comp (continuous_subtype_val.comp continuous_snd))))
  have hint : Integrable (Function.uncurry f) (μ.prod (μ.restrict F)) := by
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hcont.enorm.measurable.aemeasurable]
    rw [lintegral_lintegral_swap (hcont.enorm.measurable.aemeasurable)]
    have h1 : ∀ x y : normOneGL K n, ‖Function.uncurry f (y, x)‖ₑ =
        ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ := by
      intro x y
      simp only [Function.uncurry_apply_pair, hfdef, enorm_mul, RCLike.enorm_conj, mul_assoc]
    simp_rw [h1]
    refine lt_of_le_of_lt (lintegral_lintegral_enorm_le μ hφ₁ hφ₁l hΞ hB s) ?_
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFfin) hFfin
  have hstep : ∀ x : normOneGL K n, ∫ y, f y x ∂μ =
      ∫ y in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        ∑' γ : GL (Fin n) K, Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n)) ∂μ := by
    intro x
    set h : normOneGL K n → ℂ := fun y => Ξ (centralSection K n s *
      (x : AdelicGLn.AdelicGL K n)⁻¹ * (y : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) with hhdef
    have e1 : ∫ y, f y x ∂μ = conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * ∫ y, h y ∂μ := by
      rw [← integral_const_mul, ← integral_mul_left_eq_self (μ := μ)
        (fun y => conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * h y) x]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hfdef, hhdef, Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left]
      ring
    rw [e1]
    by_cases hx : φ₂ (x : AdelicGLn.AdelicGL K n) = 0
    · simp [hx]
    have hhi : Integrable h μ := by
      have hhc : Continuous h := (hΞ.comp (continuous_const.mul continuous_subtype_val)).mul
        (hφ₁.comp continuous_subtype_val)
      refine ⟨hhc.aestronglyMeasurable, ?_⟩
      have hb := enorm_mul_lintegral_le μ hφ₁ hφ₁l hΞ hB s x
      have hne : ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ≠ 0 := enorm_ne_zero.2 hx
      rw [HasFiniteIntegral]
      simp only [hhdef, enorm_mul]
      have hb' : (∫⁻ y, ‖Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          (y : AdelicGLn.AdelicGL K n))‖ₑ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ₑ ∂μ) *
            ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ≤ ENNReal.ofReal (B s) * μ F := by
        rw [mul_comm]; exact hb
      have hI := (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl enorm_ne_top)).2 hb'
      exact lt_of_le_of_lt hI (ENNReal.div_lt_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFfin.ne) hne)
    rw [integral_eq_setIntegral_tsum μ hhi, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_fundamentalDomain _) fun y _ => ?_
    simp only [hhdef, Subgroup.coe_mul, coe_ratElt]
    have hl : ∀ γ : GL (Fin n) K, φ₁ (AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n)) =
        φ₁ (y : AdelicGLn.AdelicGL K n) := fun γ => hφ₁l γ _
    simp only [hl]
    rw [tsum_mul_right]
    simp only [mul_assoc]
    ring
  calc ∫ y, Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) *
        matrixCoeff μ φ₁ φ₂ (y : AdelicGLn.AdelicGL K n) ∂μ
      = ∫ y, ∫ x in F, f y x ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [matrixCoeff, hfdef]
        rw [← integral_const_mul]
    _ = ∫ x in F, ∫ y, f y x ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ x in F, ∫ y in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
          ∑' γ : GL (Fin n) K, Ξ (centralSection K n s * (x : AdelicGLn.AdelicGL K n)⁻¹ *
            AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n)) ∂μ ∂μ :=
        setIntegral_congr_fun (measurableSet_fundamentalDomain _) fun x _ => hstep x
    _ = thetaPairing μ φ₁ φ₂ Ξ s := rfl

end Identity

section Main

variable {φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ}

theorem matrixCoeff_centralSection_mul
    (hφ₁z : ∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n), φ₁ (centralSection K n s * x) = φ₁ x)
    (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n) :
    matrixCoeff μ φ₁ φ₂ (centralSection K n s * g) = matrixCoeff μ φ₁ φ₂ g := by
  unfold matrixCoeff
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← mul_assoc, ← centralSection_mul_comm s (x : AdelicGLn.AdelicGL K n), mul_assoc, hφ₁z]

theorem detPow_centralSection_mul (hn : 0 < n) (s : {r : ℝ // 0 < r}) (y : normOneGL K n) (w : ℂ) :
    detPow (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) w = ((s : ℝ) : ℂ) ^ w := by
  unfold detPow
  rw [map_mul, detModule_centralSection hn, mem_normOneGL_iff_detModule.1 y.2, mul_one]

theorem detPow_inv (g : AdelicGLn.AdelicGL K n) (w : ℂ) : detPow g⁻¹ w = detPow g (-w) := by
  unfold detPow
  rw [map_inv, Complex.cpow_neg]
  have hpos : (0 : ℝ) < (detModule K n g : ℝ) := (detModule K n g).2
  have e : (((detModule K n g)⁻¹ : {r : ℝ // 0 < r}) : ℝ) = ((detModule K n g : ℝ))⁻¹ := rfl
  rw [e, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne)]

theorem stronglyMeasurable_matrixCoeff (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) :
    StronglyMeasurable (matrixCoeff μ φ₁ φ₂) := by
  have hc : Continuous (Function.uncurry fun (g : AdelicGLn.AdelicGL K n) (x : normOneGL K n) =>
      φ₁ ((x : AdelicGLn.AdelicGL K n) * g) * conj (φ₂ (x : AdelicGLn.AdelicGL K n))) :=
    (hφ₁.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)).mul
      (Complex.continuous_conj.comp (hφ₂.comp (continuous_subtype_val.comp continuous_snd)))
  exact hc.stronglyMeasurable.integral_prod_right

theorem exists_integral_eq_mellin_thetaPairing (hn : 0 < n) (ν : Measure (AdelicGLn.AdelicGL K n))
    [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ (φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ) (w : ℂ) (B : ℝ → ℝ),
      Continuous φ₁ → Continuous φ₂ → Continuous Ξ → AutomorphicForm.IsLeftInvariant φ₁ →
      (∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
        φ₁ (centralSection K n s * x) = φ₁ x) →
      (∀ (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n), x ∈ normOneGL K n →
        y ∈ normOneGL K n →
        Summable (fun γ : GL (Fin n) K =>
          ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖) ∧
        ‖φ₂ x‖ * ‖φ₁ y‖ * ∑' γ : GL (Fin n) K,
          ‖Ξ (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)‖ ≤ B t) →
      IntegrableOn (fun t : ℝ => t ^ (w.re - 1) * B t) (Ioi 0) →
      Integrable (fun g => Ξ g * matrixCoeff μ φ₁ φ₂ g * detPow g w) ν ∧
      ∫ g, Ξ g * matrixCoeff μ φ₁ φ₂ g * detPow g w ∂ν =
        (c : ℂ) * mellin (fun t : ℝ => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ ⟨t, h⟩ else 0) w := by
  refine ⟨centralHaarConst hn μ ν, by exact_mod_cast centralHaarConst_pos hn μ ν, ?_⟩
  intro φ₁ φ₂ Ξ w B hφ₁ hφ₂ hΞ hφ₁l hφ₁z hB hBint
  set F := fundamentalDomain (rationalGLOne K n) with hF
  have hFfin := measure_fundamentalDomain_rationalGLOne_lt_top μ
  set H : AdelicGLn.AdelicGL K n → ℂ := fun g => Ξ g * matrixCoeff μ φ₁ φ₂ g * detPow g w with hH
  have hHz : ∀ (s : {r : ℝ // 0 < r}) (y : normOneGL K n),
      H (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) =
        Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) *
          matrixCoeff μ φ₁ φ₂ (y : AdelicGLn.AdelicGL K n) * ((s : ℝ) : ℂ) ^ w := by
    intro s y
    simp only [hH, matrixCoeff_centralSection_mul μ hφ₁z, detPow_centralSection_mul hn]
  have hdet : Measurable fun g : AdelicGLn.AdelicGL K n => detPow g w :=
    (Complex.measurable_ofReal.comp (measurable_subtype_coe.comp
      continuous_detModule.measurable)).pow_const w
  have hHm : StronglyMeasurable H :=
    (hΞ.stronglyMeasurable.mul (stronglyMeasurable_matrixCoeff μ hφ₁ hφ₂)).mul
      hdet.stronglyMeasurable
  have hcz : Continuous fun p : normOneGL K n × {r : ℝ // 0 < r} =>
      centralSection K n p.2 * (p.1 : AdelicGLn.AdelicGL K n) :=
    (continuous_centralSection.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst)

  have hfin : ∀ s : {r : ℝ // 0 < r},
      ∫⁻ y, ‖H (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ ∂μ ≤
        ENNReal.ofReal ((s : ℝ) ^ w.re * B s) * (μ F * μ F) := by
    intro s
    have hs0 : (0 : ℝ) < s := s.2
    have hm2 : Measurable (Function.uncurry fun (y x : normOneGL K n) =>
        ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
          ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ) :=
      (((hΞ.comp (continuous_const.mul (continuous_subtype_val.comp continuous_fst))).enorm.measurable).mul
        (hφ₁.comp ((continuous_subtype_val.comp continuous_snd).mul
          (continuous_subtype_val.comp continuous_fst))).enorm.measurable).mul
        (hφ₂.comp (continuous_subtype_val.comp continuous_snd)).enorm.measurable
    calc ∫⁻ y, ‖H (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ ∂μ
        ≤ ∫⁻ y, ENNReal.ofReal ((s : ℝ) ^ w.re) * ∫⁻ x in F,
            ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
              ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
              ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [hHz, enorm_mul, enorm_mul]
          have e1 : ‖((s : ℝ) : ℂ) ^ w‖ₑ = ENNReal.ofReal ((s : ℝ) ^ w.re) := by
            rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hs0]
          have e2 : ‖matrixCoeff μ φ₁ φ₂ (y : AdelicGLn.AdelicGL K n)‖ₑ ≤ ∫⁻ x in F,
              ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ := by
            refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
            refine lintegral_congr fun x => ?_
            rw [enorm_mul, RCLike.enorm_conj]
          rw [e1]
          calc ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                ‖matrixCoeff μ φ₁ φ₂ (y : AdelicGLn.AdelicGL K n)‖ₑ * ENNReal.ofReal ((s : ℝ) ^ w.re)
              ≤ ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                (∫⁻ x in F, ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                  ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ) * ENNReal.ofReal ((s : ℝ) ^ w.re) := by
                gcongr
            _ = ENNReal.ofReal ((s : ℝ) ^ w.re) * ∫⁻ x in F,
                ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                  ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
                  ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ := by
                rw [mul_comm _ (ENNReal.ofReal _), ← lintegral_const_mul' _ _ enorm_ne_top]
                congr 1
                refine lintegral_congr fun x => ?_
                ring
      _ = ENNReal.ofReal ((s : ℝ) ^ w.re) * ∫⁻ x in F, ∫⁻ y,
            ‖Ξ (centralSection K n s * (y : AdelicGLn.AdelicGL K n))‖ₑ *
              ‖φ₁ ((x : AdelicGLn.AdelicGL K n) * (y : AdelicGLn.AdelicGL K n))‖ₑ *
              ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ₑ ∂μ ∂μ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_lintegral_swap hm2.aemeasurable]
      _ ≤ ENNReal.ofReal ((s : ℝ) ^ w.re) * (ENNReal.ofReal (B s) * μ F * μ F) := by
          gcongr
          exact lintegral_lintegral_enorm_le μ hφ₁ hφ₁l hΞ hB s
      _ = ENNReal.ofReal ((s : ℝ) ^ w.re * B s) * (μ F * μ F) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _)]
          ring

  have hint : Integrable H ν := by
    rw [integrable_iff_prod μ ν hn H]
    refine ⟨(hHm.comp_measurable hcz.measurable).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod_symm (fun p : normOneGL K n × {r : ℝ // 0 < r} =>
      ‖H (centralSection K n p.2 * (p.1 : AdelicGLn.AdelicGL K n))‖ₑ)
      (hHm.comp_measurable hcz.measurable).enorm.aemeasurable]
    refine lt_of_le_of_lt (lintegral_mono fun s => hfin s) ?_
    rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hFfin.ne hFfin.ne)]
    refine ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top hFfin hFfin)
    rw [lintegral_posRealMeasure (fun t => ENNReal.ofReal (t ^ w.re * B t))]
    have e3 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * ENNReal.ofReal (t ^ w.re * B t) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (w.re - 1) * B t) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 ht.le), Real.rpow_sub_one ht.ne']
      congr 1
      field_simp
    rw [e3]
    refine lt_of_le_of_lt (lintegral_mono fun t => ?_) hBint.2
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  refine ⟨hint, ?_⟩
  rw [integral_eq_centralHaarConst_smul hn μ ν hint]
  have hinner : ∀ s : {r : ℝ // 0 < r},
      ∫ y, H (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) ∂μ =
        thetaPairing μ φ₁ φ₂ Ξ s * ((s : ℝ) : ℂ) ^ w := by
    intro s
    simp_rw [hHz]
    rw [integral_mul_const, integral_mul_matrixCoeff_eq_thetaPairing μ hφ₁ hφ₂ hφ₁l hΞ hB s]
  simp_rw [hinner]
  set J' : ℝ → ℂ := fun t => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ ⟨t, h⟩ * (t : ℂ) ^ w else 0
    with hJ'
  have e4 : (fun s : {r : ℝ // 0 < r} => thetaPairing μ φ₁ φ₂ Ξ s * ((s : ℝ) : ℂ) ^ w) =
      fun s : {r : ℝ // 0 < r} => J' (s : ℝ) := by
    funext s
    simp only [hJ', dif_pos s.2, Subtype.coe_eta]
  rw [e4, integral_posRealMeasure, Complex.real_smul, mellin]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [hJ', dif_pos ht]
  rw [Complex.real_smul, smul_eq_mul, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.2 ht.ne'),
    Complex.cpow_one, Complex.ofReal_inv]
  have : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  field_simp

end Main

end GJGlobal

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter NumberField ComplexConjugate
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

theorem isLeftInvariant_conj {ψ : AdelicGLn.AdelicGL K n → ℂ} (h : IsLeftInvariant ψ) :
    IsLeftInvariant (fun g => conj (ψ g)) := fun γ g => by
  simp only [h γ g]

theorem isCuspidal_conj {ψ : AdelicGLn.AdelicGL K n → ℂ} (h : IsCuspidal ψ) :
    IsCuspidal (fun g => conj (ψ g)) := by
  intro r hr hrn g
  have := h r hr hrn g
  unfold constantTerm at this ⊢
  rw [integral_conj, this, map_zero]

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem integrableOn_mul_tsum_comp {ψ : AdelicGLn.AdelicGL K n → ℂ} (hψc : Continuous ψ)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    {C : ℝ} (hC : ∀ g ∈ normOneGL K n, ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C)
    {ι : Type*} [Countable ι] (e : ι → Matrix (Fin n) (Fin n) K) (he : Function.Injective e) :
    IntegrableOn (fun g : normOneGL K n => ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' i, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (e i) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])))
      (fundamentalDomain Γ₁) μ := by
  have hF : μ (fundamentalDomain Γ₁) < ⊤ := measure_fundamentalDomain_rationalGLOne_lt_top μ
  refine Measure.integrableOn_of_bounded (M := C) hF.ne ?_ ?_
  · refine ((hψc.comp continuous_subtype_val).measurable.mul ?_).aestronglyMeasurable
    refine UnfoldGL.measurable_tsum_of_summable (fun i => ?_) fun g => ?_
    · exact (hΦ.comp (continuous_const.mul (Units.continuous_val.comp
        continuous_subtype_val))).measurable
    · exact ((hsum g).comp_injective he).of_norm
  · refine Eventually.of_forall fun g => ?_
    rw [norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hC g g.2)
    refine (norm_tsum_le_tsum_norm ((hsum g).comp_injective he)).trans ?_
    exact Summable.tsum_le_tsum_of_inj e he (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
      ((hsum g).comp_injective he) (hsum g)

set_option maxHeartbeats 800000 in

theorem setIntegral_mul_tsum_det_eq_zero (hn : 2 ≤ n) {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψc : Continuous ψ) (hψl : IsLeftInvariant ψ) (hψ : IsCuspidal ψ)
    (hψb : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ ≤ C)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    (hbd : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C) :
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ = 0 := by
  obtain ⟨C, hC⟩ := hbd
  have hsplit : ∀ g : normOneGL K n,
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) =
        ∑ r : Fin n, ψ (g : AdelicGLn.AdelicGL K n) *
          ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r},
            Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
              ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
    intro g
    rw [tsum_det_eq_zero_eq_sum_rank (hsum (g : AdelicGLn.AdelicGL K n)).of_norm, Finset.mul_sum]
  rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => hsplit g,
    integral_finsetSum _ fun r _ =>
      integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Subtype.val_injective]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : (r : ℕ) = 0
  ·
    have hmem : (0 : Matrix (Fin n) (Fin n) K).rank = r := by rw [Matrix.rank_zero, hr]
    have h0 : ∀ g : normOneGL K n,
        ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r},
          Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
            ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) = Φ 0 := by
      intro g
      have hu : ∀ ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r}, ξ = ⟨0, hmem⟩ := by
        intro ξ
        refine Subtype.ext ?_
        have h1 : (ξ : Matrix (Fin n) (Fin n) K).rank = 0 := ξ.2.trans hr
        exact (rank_eq_zero_iff (K := K) (n := n)).1 h1
      rw [tsum_eq_single (⟨0, hmem⟩ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r})
        fun ξ hξ => absurd (hu ξ) hξ]
      have hz : ratMat (0 : Matrix (Fin n) (Fin n) K) = 0 := by
        unfold ratMat
        exact Matrix.map_zero _ (map_zero _)
      rw [hz, mul_zero, zero_mul]
    have hm := setIntegral_fundamentalDomain_eq_zero μ hn hψc hψl hψ hψb
    rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => by rw [h0 g],
      integral_mul_const, hm, zero_mul]
  ·
    have hk : 0 < n - (r : ℕ) := Nat.sub_pos_of_lt r.2
    have hkn : n - (r : ℕ) < n := Nat.sub_lt (by omega) (Nat.pos_of_ne_zero hr)
    have e : n - (n - (r : ℕ)) = r := Nat.sub_sub_self r.2.le
    have := UnfoldGL.setIntegral_mul_tsum_rank_eq_zero μ hψc hψl hψ hΦ y hsum ⟨C, hC⟩ hk hkn
    rw [e] at this
    exact this

set_option maxHeartbeats 800000 in

theorem setIntegral_mul_tsum_eq_tsum_GL (hn : 2 ≤ n) {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψc : Continuous ψ) (hψl : IsLeftInvariant ψ) (hψ : IsCuspidal ψ)
    (hψb : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ ≤ C)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    (hbd : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C) :
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ =
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' γ : GL (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat (γ : Matrix (Fin n) (Fin n) K) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ := by
  obtain ⟨C, hC⟩ := hbd
  have hsing := setIntegral_mul_tsum_det_eq_zero μ hn hψc hψl hψ hψb hΦ y hsum ⟨C, hC⟩
  have hsplit : ∀ g : normOneGL K n, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' γ : GL (Fin n) K,
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) +
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
    intro g
    rw [tsum_eq_tsum_GL_add (hsum (g : AdelicGLn.AdelicGL K n)).of_norm, mul_add]
  rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => hsplit g,
    integral_add (integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Units.val_injective)
      (integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Subtype.val_injective), hsing, add_zero]

end GJGlobal

end

end GroundTheory.Automorphic
end

section
namespace GroundTheory.Automorphic.GJGlobal

open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure Matrix
  GroundTheory.Global GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.GJMatrix
  GroundTheory.Automorphic.GJGlobal.Modulus
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap Classical

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1000

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

namespace Twist

def invMod (g : GL (Fin n) 𝔸[K]) : ℝ≥0 :=
  Real.toNNReal ((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹

theorem coe_invMod (g : GL (Fin n) 𝔸[K]) :
    (invMod g : ℝ) = ((detModule K n g : ℝ))⁻¹ := by
  rw [invMod, Real.coe_toNNReal _ (inv_nonneg.2 (IdeleGroup.ideleModule K _).2.le)]
  rfl

theorem pi_const_smul {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  refine pi_eq fun s hs => ?_
  rw [Measure.smul_apply, pi_pi, ENNReal.smul_def, smul_eq_mul]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

theorem map_mul_right (b : GL (Fin n) 𝔸[K]) :
    (adelicMatrixMeasure K n).map (fun x => x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      (invMod b ^ n) • adelicMatrixMeasure K n := by
  have hf : (fun x : Matrix (Fin n) (Fin n) 𝔸[K] => x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      fun x i => (x i) ᵥ* (b : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    funext x i j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hmap : (adeleMeasurePi K (ι := Fin n)).map (fun y => y ᵥ* (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      invMod b • adeleMeasurePi K (ι := Fin n) := by
    rw [map_vecMul_adeleMeasurePi, invMod, ENNReal.smul_def]
    rfl
  have hsf : ∀ _ : Fin n, SigmaFinite ((adeleMeasurePi K (ι := Fin n)).map
      fun y => y ᵥ* (b : Matrix (Fin n) (Fin n) 𝔸[K])) := fun _ => by
    rw [hmap]; infer_instance
  rw [hf]
  change (Measure.pi fun _ : Fin n => adeleMeasurePi K (ι := Fin n)).map
    (fun x i => (x i) ᵥ* (b : Matrix (Fin n) (Fin n) 𝔸[K])) = _
  rw [pi_map_pi (hμ := hsf) (fun _ => (measurable_vecMul' b).aemeasurable)]
  simp only [hmap]
  rw [pi_const_smul, Fintype.card_fin]
  rfl

theorem measurePreserving_transpose :
    MeasurePreserving (fun x : Matrix (Fin n) (Fin n) 𝔸[K] => xᵀ) (adelicMatrixMeasure K n)
      (adelicMatrixMeasure K n) := by
  set e := (MeasurableEquiv.curry (Fin n) (Fin n) 𝔸[K]).symm
  have he : MeasurePreserving e (adelicMatrixMeasure K n)
      (Measure.pi fun _ : Fin n × Fin n => adeleMeasure K) :=
    measurePreserving_matrixCoord (n := Fin n) (adeleMeasure K)
  have hT := measurePreserving_matrixCoordT (n := Fin n) (adeleMeasure K)
  have h : (fun x : Matrix (Fin n) (Fin n) 𝔸[K] => xᵀ) = e.symm ∘ matrixCoordT := by
    funext x i j
    rfl
  rw [h]
  exact (he.symm e).comp hT

def transposeGL (a : GL (Fin n) 𝔸[K]) : GL (Fin n) 𝔸[K] :=
  ⟨(a : Matrix (Fin n) (Fin n) 𝔸[K])ᵀ, ((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])ᵀ,
    by rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one],
    by rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]⟩

theorem coe_transposeGL (a : GL (Fin n) 𝔸[K]) :
    ((transposeGL a : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      (a : Matrix (Fin n) (Fin n) 𝔸[K])ᵀ := rfl

theorem invMod_transposeGL (a : GL (Fin n) 𝔸[K]) : invMod (transposeGL a) = invMod a := by
  have h : Matrix.GeneralLinearGroup.det (transposeGL a) = Matrix.GeneralLinearGroup.det a := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      coe_transposeGL, det_transpose]
  rw [invMod, invMod, h]

theorem map_mul_left (a : GL (Fin n) 𝔸[K]) :
    (adelicMatrixMeasure K n).map (fun x => (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x) =
      (invMod a ^ n) • adelicMatrixMeasure K n := by
  have hT := measurePreserving_transpose (K := K) (n := n)
  have hR : Measurable fun x : Matrix (Fin n) (Fin n) 𝔸[K] =>
      x * ((transposeGL a : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have h : (fun x : Matrix (Fin n) (Fin n) 𝔸[K] => (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x) =
      (fun x => xᵀ) ∘ (fun x => x * ((transposeGL a : GL (Fin n) 𝔸[K]) :
        Matrix (Fin n) (Fin n) 𝔸[K])) ∘ (fun x => xᵀ) := by
    funext x
    simp only [Function.comp_apply, coe_transposeGL, ← transpose_mul, transpose_transpose]
  rw [h, ← map_map hT.measurable (hR.comp hT.measurable), ← map_map hR hT.measurable, hT.map_eq,
    map_mul_right, Measure.map_smul, hT.map_eq, invMod_transposeGL]

theorem map_mul_mul (a b : GL (Fin n) 𝔸[K]) :
    (adelicMatrixMeasure K n).map
        (fun x => (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ((invMod a * invMod b) ^ n) • adelicMatrixMeasure K n := by
  have hL : Measurable fun x : Matrix (Fin n) (Fin n) 𝔸[K] =>
      (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hR : Measurable fun x : Matrix (Fin n) (Fin n) 𝔸[K] =>
      x * (b : Matrix (Fin n) (Fin n) 𝔸[K]) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have h : (fun x : Matrix (Fin n) (Fin n) 𝔸[K] =>
      (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      (fun x => x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) ∘
        (fun x => (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x) := rfl
  rw [h, ← map_map hR hL, map_mul_left, Measure.map_smul, map_mul_right, smul_smul, mul_pow,
    mul_comm]

def mulMulHomeomorph (a b : GL (Fin n) 𝔸[K]) :
    Matrix (Fin n) (Fin n) 𝔸[K] ≃ₜ Matrix (Fin n) (Fin n) 𝔸[K] where
  toFun x := (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K])
  invFun x := ((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) * x *
    ((b⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])
  left_inv x := by
    simp only [← Matrix.mul_assoc]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv x := by
    simp only [← Matrix.mul_assoc]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem integral_comp_mul_mul (a b : GL (Fin n) 𝔸[K]) (f : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) :
    ∫ x, f ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K]))
        ∂adelicMatrixMeasure K n =
      ((((detModule K n a : ℝ) * (detModule K n b : ℝ)) ^ n)⁻¹ : ℂ) *
        ∫ x, f x ∂adelicMatrixMeasure K n := by
  have hemb : MeasurableEmbedding (mulMulHomeomorph a b) :=
    (mulMulHomeomorph a b).toMeasurableEquiv.measurableEmbedding
  have h1 := hemb.integral_map (μ := adelicMatrixMeasure K n) f
  change ∫ x, f (mulMulHomeomorph a b x) ∂adelicMatrixMeasure K n = _
  rw [← h1]
  change ∫ y, f y ∂(adelicMatrixMeasure K n).map
    (fun x => (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) = _
  rw [map_mul_mul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  congr 1
  push_cast
  rw [coe_invMod, coe_invMod]
  push_cast
  rw [← mul_inv, inv_pow]

def infHom : 𝔸[K] →+* mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

def finHom : 𝔸[K] →+* FiniteAdeleRing (𝓞 K) K :=
  RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)

theorem infPartPi_eq' (z : Fin n × Fin n → 𝔸[K]) : infPartPi z = fun p => infHom (z p) := rfl

theorem finPartPi_eq' (z : Fin n × Fin n → 𝔸[K]) : finPartPi z = fun p => finHom (z p) := rfl

def twistCoord {R : Type*} [CommRing R] (A B : Matrix (Fin n) (Fin n) R)
    (z : Fin n × Fin n → R) : Fin n × Fin n → R :=
  matrixCoord (A * Matrix.of (fun i j => z (i, j)) * B)

theorem twistCoord_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Matrix (Fin n) (Fin n) R) (z : Fin n × Fin n → R) :
    (fun p => f (twistCoord A B z p)) = twistCoord (A.map f) (B.map f) (fun p => f (z p)) := by
  have h : (A * Matrix.of (fun i j => z (i, j)) * B).map f =
      A.map f * Matrix.of (fun i j => f (z (i, j))) * B.map f := by
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  funext p
  exact congrFun (congrFun h p.1) p.2

theorem twistCoord_twistCoord {R : Type*} [CommRing R] {A B A' B' : Matrix (Fin n) (Fin n) R}
    (hA : A' * A = 1) (hB : B * B' = 1) (z : Fin n × Fin n → R) :
    twistCoord A' B' (twistCoord A B z) = z := by
  have h1 : Matrix.of (fun i j => matrixCoord (A * Matrix.of (fun i j => z (i, j)) * B) (i, j)) =
      A * Matrix.of (fun i j => z (i, j)) * B := Matrix.ext fun i j => rfl
  have h2 : A' * (A * Matrix.of (fun i j => z (i, j)) * B) * B' =
      Matrix.of (fun i j => z (i, j)) := by
    calc A' * (A * Matrix.of (fun i j => z (i, j)) * B) * B' =
        (A' * A) * Matrix.of (fun i j => z (i, j)) * (B * B') := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of (fun i j => z (i, j)) := by rw [hA, hB, Matrix.one_mul, Matrix.mul_one]
  funext p
  simp only [twistCoord]
  rw [h1, h2]
  rfl

theorem continuous_twistCoord {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (A B : Matrix (Fin n) (Fin n) R) : Continuous (twistCoord A B) :=
  (matrixCoordHomeomorph (Fin n) R).continuous.comp
    ((continuous_const.matrix_mul (matrixCoordHomeomorph (Fin n) R).symm.continuous).matrix_mul
      continuous_const)

theorem map_inv_mul_map {R : Type*} [CommRing R] (f : 𝔸[K] →+* R) (g : GL (Fin n) 𝔸[K]) :
    ((g⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map f *
      (g : Matrix (Fin n) (Fin n) 𝔸[K]).map f = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one f (map_zero f) (map_one f)]

theorem map_mul_map_inv {R : Type*} [CommRing R] (f : 𝔸[K] →+* R) (g : GL (Fin n) 𝔸[K]) :
    (g : Matrix (Fin n) (Fin n) 𝔸[K]).map f *
      ((g⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map f = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one f (map_zero f) (map_one f)]

def twistInfLin (a b : GL (Fin n) 𝔸[K]) :
    (Fin n × Fin n → mixedSpace K) ≃ₗ[ℝ] (Fin n × Fin n → mixedSpace K) where
  toFun := twistCoord ((a : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom)
    ((b : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom)
  invFun := twistCoord (((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom)
    (((b⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom)
  map_add' u v := by
    funext p
    simp only [twistCoord, matrixCoord, Pi.add_apply]
    have : Matrix.of (fun i j => u (i, j) + v (i, j)) =
        Matrix.of (fun i j => u (i, j)) + Matrix.of (fun i j => v (i, j)) :=
      Matrix.ext fun i j => rfl
    rw [this, Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' c u := by
    funext p
    simp only [twistCoord, matrixCoord, Pi.smul_apply, RingHom.id_apply]
    have : Matrix.of (fun i j => c • u (i, j)) = c • Matrix.of (fun i j => u (i, j)) :=
      Matrix.ext fun i j => rfl
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  left_inv u := twistCoord_twistCoord (map_inv_mul_map infHom a) (map_mul_map_inv infHom b) u
  right_inv u := twistCoord_twistCoord (map_mul_map_inv infHom a) (map_inv_mul_map infHom b) u

def twistInf (a b : GL (Fin n) 𝔸[K]) :
    (Fin n × Fin n → mixedSpace K) ≃L[ℝ] (Fin n × Fin n → mixedSpace K) :=
  (twistInfLin a b).toContinuousLinearEquiv

theorem coe_twistInf (a b : GL (Fin n) 𝔸[K]) :
    ⇑(twistInf a b) = twistCoord ((a : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom)
      ((b : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom) := rfl

def twistFin (a b : GL (Fin n) 𝔸[K]) :
    (Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) ≃ₜ (Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) where
  toFun := twistCoord ((a : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom)
    ((b : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom)
  invFun := twistCoord (((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom)
    (((b⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom)
  left_inv u := twistCoord_twistCoord (map_inv_mul_map finHom a) (map_mul_map_inv finHom b) u
  right_inv u := twistCoord_twistCoord (map_mul_map_inv finHom a) (map_inv_mul_map finHom b) u
  continuous_toFun := continuous_twistCoord _ _
  continuous_invFun := continuous_twistCoord _ _

theorem coe_twistFin (a b : GL (Fin n) 𝔸[K]) :
    ⇑(twistFin a b) = twistCoord ((a : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom)
      ((b : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom) := rfl

theorem tensor_comp_twistCoord (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    (g : (Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) → ℂ) (a b : GL (Fin n) 𝔸[K]) :
    schwartzBruhatTensorPi φ g ∘ twistCoord (a : Matrix (Fin n) (Fin n) 𝔸[K])
        (b : Matrix (Fin n) (Fin n) 𝔸[K]) =
      schwartzBruhatTensorPi (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twistInf a b) φ)
        (g ∘ twistFin a b) := by
  funext z
  simp only [Function.comp_apply, schwartzBruhatTensorPi,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, coe_twistInf, coe_twistFin]
  rw [infPartPi_eq', infPartPi_eq', finPartPi_eq', finPartPi_eq', twistCoord_map infHom,
    twistCoord_map finHom]

theorem comp_twistCoord_mem {F : (Fin n × Fin n → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhatPi K (Fin n × Fin n)) (a b : GL (Fin n) 𝔸[K]) :
    F ∘ twistCoord (a : Matrix (Fin n) (Fin n) 𝔸[K]) (b : Matrix (Fin n) (Fin n) 𝔸[K]) ∈
      schwartzBruhatPi K (Fin n × Fin n) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [tensor_comp_twistCoord]
    refine schwartzBruhatTensorPi_mem _ ((mem_finiteSchwartzBruhatPi K).2 ⟨?_, ?_⟩)
    · exact ((mem_finiteSchwartzBruhatPi K).1 hg).1.comp_continuous (twistFin a b).continuous
    · exact ((mem_finiteSchwartzBruhatPi K).1 hg).2.comp_homeomorph (twistFin a b)
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG

end Twist

open Twist

theorem mul_mul_mem_matrixSchwartzBruhat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) (a b : GL (Fin n) 𝔸[K]) :
    (fun x => Φ ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K]))) ∈
      matrixSchwartzBruhat K n := by
  rw [mem_matrixSchwartzBruhat] at hΦ ⊢
  have h := comp_twistCoord_mem hΦ a b
  convert h using 1
  funext z
  rfl

theorem adelicMatrixFourier_mul_mul (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (a b : GL (Fin n) 𝔸[K])
    (y : Matrix (Fin n) (Fin n) 𝔸[K]) :
    adelicMatrixFourier K
        (fun x => Φ ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K]))) y =
      ((((detModule K n a : ℝ) * (detModule K n b : ℝ)) ^ n)⁻¹ : ℂ) *
        adelicMatrixFourier K Φ (((b⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) * y *
          ((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  set A : Matrix (Fin n) (Fin n) 𝔸[K] := (a : Matrix (Fin n) (Fin n) 𝔸[K])
  set B : Matrix (Fin n) (Fin n) 𝔸[K] := (b : Matrix (Fin n) (Fin n) 𝔸[K])
  set A' : Matrix (Fin n) (Fin n) 𝔸[K] := ((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])
  set B' : Matrix (Fin n) (Fin n) 𝔸[K] := ((b⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])
  have hA : A' * A = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hB : B * B' = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have htr : ∀ x : Matrix (Fin n) (Fin n) 𝔸[K], Matrix.trace (A * x * B * (B' * y * A')) = Matrix.trace (x * y) := by
    intro x
    have e1 : A * x * B * (B' * y * A') = A * (x * (y * A')) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B B', hB, Matrix.one_mul]
    rw [e1, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [hA, Matrix.mul_one]
  rw [adelicMatrixFourier, adelicMatrixFourier, ← integral_comp_mul_mul a b]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [htr]

theorem twisted_poisson {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Φ ∈ matrixSchwartzBruhat K n)
    (a b : AdelicGLn.AdelicGL K n) :
    Summable (fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (b : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
    Summable (fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖adelicMatrixFourier K Φ (((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
    ∑' ξ : Matrix (Fin n) (Fin n) K,
        Φ ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ((((detModule K n a : ℝ) * (detModule K n b : ℝ)) ^ n)⁻¹ : ℂ) *
        ∑' ξ : Matrix (Fin n) (Fin n) K,
          adelicMatrixFourier K Φ (((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
            ratMat ξ * ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  set c : ℂ := ((((detModule K n a : ℝ) * (detModule K n b : ℝ)) ^ n)⁻¹ : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine inv_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ ?_))
    · exact_mod_cast (detModule K n a).2.ne'
    · exact_mod_cast (detModule K n b).2.ne'
  obtain ⟨h1, h2, h3⟩ := poisson_matrix (mul_mul_mem_matrixSchwartzBruhat hΦ a b)
  have hF : ∀ ξ : Matrix (Fin n) (Fin n) K,
      adelicMatrixFourier K (fun x => Φ ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * x *
        (b : Matrix (Fin n) (Fin n) 𝔸[K]))) (ξ.map (algebraMap K 𝔸[K])) =
      c * adelicMatrixFourier K Φ (((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ξ.map (algebraMap K 𝔸[K]) * ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) :=
    fun ξ => adelicMatrixFourier_mul_mul Φ a b _
  simp only [ratMat]
  simp only [hF] at h2 h3
  refine ⟨h1, ?_, ?_⟩
  · have h2' := h2.mul_left (‖c‖⁻¹)
    refine h2'.congr fun ξ => ?_
    rw [norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hc0), one_mul]
  · rw [h3, tsum_mul_left]

theorem centralSection_mul_comm_matrix (t : {r : ℝ // 0 < r}) (M : Matrix (Fin n) (Fin n) 𝔸[K]) :
    ((centralSection K n t : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * M =
      M * ((centralSection K n t : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  rw [centralSection, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) M)

theorem twisted_poisson_centralSection (hn : 0 < n) {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) (t : {r : ℝ // 0 < r}) {x y : AdelicGLn.AdelicGL K n}
    (hx : x ∈ normOneGL K n) (hy : y ∈ normOneGL K n) :
    Summable (fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ (((centralSection K n t * x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
    Summable (fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖adelicMatrixFourier K Φ (((centralSection K n t⁻¹ * y⁻¹ : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (x : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
    ∑' ξ : Matrix (Fin n) (Fin n) K,
        Φ (((centralSection K n t * x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
          ratMat ξ * (y : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ((((t : ℝ)) ^ n)⁻¹ : ℂ) *
        ∑' ξ : Matrix (Fin n) (Fin n) K,
          adelicMatrixFourier K Φ (((centralSection K n t⁻¹ * y⁻¹ : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (x : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  obtain ⟨h1, h2, h3⟩ := twisted_poisson hΦ (centralSection K n t * x⁻¹) y
  have hxm : detModule K n x = 1 := mem_normOneGL_iff_detModule.1 hx
  have hym : detModule K n y = 1 := mem_normOneGL_iff_detModule.1 hy
  have hdet : ((detModule K n (centralSection K n t * x⁻¹) : ℝ) * (detModule K n y : ℝ)) =
      (t : ℝ) := by
    rw [map_mul, map_inv, hxm, hym, detModule_centralSection hn, inv_one, mul_one, Positive.val_one,
      mul_one]
  have harg : ∀ ξ : Matrix (Fin n) (Fin n) K,
      ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        (((centralSection K n t * x⁻¹)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ((centralSection K n t⁻¹ * y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * (x : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    intro ξ
    rw [_root_.mul_inv_rev, inv_inv, ← map_inv, Units.val_mul, Units.val_mul]
    set Z : Matrix (Fin n) (Fin n) 𝔸[K] :=
      ((centralSection K n t⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
    have hz := centralSection_mul_comm_matrix (K := K) (n := n) t⁻¹
    calc ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          ((x : Matrix (Fin n) (Fin n) 𝔸[K]) * Z) =
        (((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (x : Matrix (Fin n) (Fin n) 𝔸[K])) * Z := by rw [Matrix.mul_assoc _ _ Z]
      _ = Z * (((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (x : Matrix (Fin n) (Fin n) 𝔸[K])) := (hz _).symm
      _ = Z * ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (x : Matrix (Fin n) (Fin n) 𝔸[K]) := by simp only [Matrix.mul_assoc]
  simp only [harg] at h2 h3
  refine ⟨h1, h2, ?_⟩
  rw [h3, ← Complex.ofReal_mul, hdet]

end

end GroundTheory.Automorphic.GJGlobal
end

section
open MeasureTheory Set Filter NumberField ComplexConjugate
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

section Continuity

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

local notation "Γ₁" => rationalGLOne K n

theorem continuous_thetaPairing {φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ} (hφ₁ : Continuous φ₁)
    (hφ₂ : Continuous φ₂)
    (hcont : Continuous fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ∑' γ : GL (Fin n) K, Ξ (centralSection K n p.1 * p.2.1 * AdelicGLn.diagonal K n γ * p.2.2))
    {B : {r : ℝ // 0 < r} → ℝ} (hBc : Continuous B)
    (hB : ∀ t : {r : ℝ // 0 < r}, ∀ x y : normOneGL K n,
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ‖∑' γ : GL (Fin n) K, Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ B t) :
    Continuous (thetaPairing μ φ₁ φ₂ Ξ) := by
  let T : {r : ℝ // 0 < r} → normOneGL K n → normOneGL K n → ℂ := fun t x y =>
    conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
      ∑' γ : GL (Fin n) K, Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))
  have c1 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n =>
      ((p.2.1 : normOneGL K n) : AdelicGLn.AdelicGL K n) := by fun_prop
  have c2 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n =>
      ((p.2.2 : normOneGL K n) : AdelicGLn.AdelicGL K n) := by fun_prop
  have c4 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n =>
      (p.1, ((p.2.1 : normOneGL K n) : AdelicGLn.AdelicGL K n)⁻¹,
        ((p.2.2 : normOneGL K n) : AdelicGLn.AdelicGL K n)) := by fun_prop
  have c3 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n =>
      ∑' γ : GL (Fin n) K, Ξ (centralSection K n p.1 * ((p.2.1 : normOneGL K n) :
        AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * ((p.2.2 : normOneGL K n) :
          AdelicGLn.AdelicGL K n)) := by
    have h5 := hcont.comp c4
    simpa only [Function.comp_def] using h5
  have hTc : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n =>
      T p.1 p.2.1 p.2.2 :=
    ((Complex.continuous_conj.comp (hφ₂.comp c1)).mul (hφ₁.comp c2)).mul c3
  have hTb : ∀ t x y, ‖T t x y‖ ≤ B t := by
    intro t x y
    simp only [T, norm_mul, Complex.norm_conj]
    exact hB t x y
  have hF : μ (fundamentalDomain Γ₁) < ⊤ := measure_fundamentalDomain_rationalGLOne_lt_top μ
  have : IsFiniteMeasure (μ.restrict (fundamentalDomain Γ₁)) := ⟨by rw [Measure.restrict_apply_univ]; exact hF⟩

  have hloc : ∀ t₀ : {r : ℝ // 0 < r}, ∀ᶠ t in nhds t₀, B t ≤ B t₀ + 1 := fun t₀ =>
    (hBc.continuousAt.eventually (gt_mem_nhds (lt_add_one (B t₀)))).mono fun _ h => h.le

  have hinner : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n =>
      ∫ y in fundamentalDomain Γ₁, T p.1 p.2 y ∂μ := by
    rw [continuous_iff_continuousAt]
    intro p₀
    refine continuousAt_of_dominated (bound := fun _ => B p₀.1 + 1) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun p =>
        (hTc.comp (Continuous.prodMk continuous_const (Continuous.prodMk continuous_const
          continuous_id))).aestronglyMeasurable
    · have := (hloc p₀.1).filter_mono (continuous_fst.continuousAt (x := p₀)).tendsto
      filter_upwards [this] with p hp
      exact Filter.Eventually.of_forall fun y => (hTb p.1 p.2 y).trans hp
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun y =>
        (hTc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).continuousAt
  rw [continuous_iff_continuousAt]
  intro t₀
  unfold thetaPairing
  refine continuousAt_of_dominated (bound := fun _ => (B t₀ + 1) * (μ (fundamentalDomain Γ₁)).toReal) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun t =>
      (hinner.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · filter_upwards [hloc t₀] with t ht
    refine Filter.Eventually.of_forall fun x => ?_
    calc ‖∫ y in fundamentalDomain Γ₁, T t x y ∂μ‖ ≤ (B t₀ + 1) * (μ.restrict (fundamentalDomain Γ₁) univ).toReal :=
          norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y =>
            (hTb t x y).trans ht)
      _ = (B t₀ + 1) * (μ (fundamentalDomain Γ₁)).toReal := by rw [Measure.restrict_apply_univ]
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun x =>
      (hinner.comp (continuous_id.prodMk continuous_const)).continuousAt

end Continuity

section Symmetry

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

local notation "Γ₁" => rationalGLOne K n

theorem coe_mul_diagonal_mul (t : {r : ℝ // 0 < r}) (a b : AdelicGLn.AdelicGL K n)
    (γ : GL (Fin n) K) :
    ((centralSection K n t * a * AdelicGLn.diagonal K n γ * b : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) 𝔸[K]) =
      ((centralSection K n t * a : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat (γ : Matrix (Fin n) (Fin n) K) * (b : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  rw [Units.val_mul, Units.val_mul, coe_diagonal]

theorem tsum_inv_eq (Ψ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (t : {r : ℝ // 0 < r})
    (x y : AdelicGLn.AdelicGL K n) :
    ∑' γ : GL (Fin n) K, Ψ (((centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)⁻¹ :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
    ∑' γ : GL (Fin n) K, Ψ (((centralSection K n t⁻¹ * y⁻¹ : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  rw [← (Equiv.inv (GL (Fin n) K)).tsum_eq]
  refine tsum_congr fun γ => ?_
  congr 1
  simp only [Equiv.inv_apply]
  have e : (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ⁻¹ * y)⁻¹ =
      centralSection K n t⁻¹ * y⁻¹ * AdelicGLn.diagonal K n γ * x := by
    rw [map_inv (AdelicGLn.diagonal K n)]
    have e1 : (centralSection K n t * x⁻¹ * (AdelicGLn.diagonal K n γ)⁻¹ * y)⁻¹ =
        (y⁻¹ * AdelicGLn.diagonal K n γ * x) * (centralSection K n t)⁻¹ := by group
    rw [e1, ← map_inv, ← centralSection_mul_comm t⁻¹ (y⁻¹ * AdelicGLn.diagonal K n γ * x)]
    simp only [mul_assoc]
  rw [e, Units.val_mul, Units.val_mul, coe_diagonal]

set_option maxHeartbeats 1600000 in

theorem thetaPairing_eq (hn : 2 ≤ n) {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ}
    (h₁ : φ₁ ∈ cuspForms K n) (h₂ : φ₂ ∈ cuspForms K n)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Φ ∈ matrixSchwartzBruhat K n)
    (t : {r : ℝ // 0 < r}) :
    thetaPairing μ φ₁ φ₂ (fun g => Φ (g : Matrix (Fin n) (Fin n) 𝔸[K])) t =
      ((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * thetaPairing μ φ₁ φ₂
        (fun g => adelicMatrixFourier K Φ ((g⁻¹ : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K])) t := by
  have hn0 : 0 < n := by omega
  set Φh := adelicMatrixFourier K Φ with hΦhdef
  have hΦh : Φh ∈ matrixSchwartzBruhat K n := adelicMatrixFourier_mem hΦ
  have hΦc : Continuous Φ := continuous_of_mem_matrixSchwartzBruhat hΦ
  have hΦhc : Continuous Φh := continuous_of_mem_matrixSchwartzBruhat hΦh
  have h₁c : Continuous φ₁ := h₁.1.continuous
  have h₂c : Continuous φ₂ := h₂.1.continuous
  have h₂c' : Continuous fun g => conj (φ₂ g) := Complex.continuous_conj.comp h₂c
  obtain ⟨B₁, hB₁⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms h₁
  obtain ⟨B₂, hB₂⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms h₂
  have hB₂' : ∃ C, ∀ g ∈ normOneGL K n, ‖conj (φ₂ g)‖ ≤ C :=
    ⟨B₂, fun g hg => by rw [Complex.norm_conj]; exact hB₂ g hg⟩
  set F := fundamentalDomain Γ₁
  have hF : μ F < ⊤ := measure_fundamentalDomain_rationalGLOne_lt_top μ
  have : IsFiniteMeasure (μ.restrict F) := ⟨by rw [Measure.restrict_apply_univ]; exact hF⟩

  set S : normOneGL K n → normOneGL K n → ℂ := fun x y =>
    ∑' ξ : Matrix (Fin n) (Fin n) K, Φ (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) with hS
  set Sh : normOneGL K n → normOneGL K n → ℂ := fun x y =>
    ∑' ξ : Matrix (Fin n) (Fin n) K, Φh (((centralSection K n t⁻¹ *
      (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) with hSh
  set ShG : normOneGL K n → normOneGL K n → ℂ := fun x y =>
    ∑' γ : GL (Fin n) K, Φh (((centralSection K n t⁻¹ *
      (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat (γ : Matrix (Fin n) (Fin n) K) *
          ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) with hShG

  have hP : ∀ x y : normOneGL K n, S x y = ((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y := by
    intro x y
    have := (twisted_poisson_centralSection hn0 hΦ t x.2 y.2).2.2
    rw [hS, hSh]
    simp only
    rw [this]
    push_cast
    rfl

  obtain ⟨C₁, M₁, -, hC₁⟩ := exists_bound_tsum hΦ h₁ h₂
  obtain ⟨C₂, M₂, -, hC₂⟩ := exists_bound_tsum hΦh h₂ h₁

  have hA : ∀ x : normOneGL K n,
      ∫ y in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        ∑' γ : GL (Fin n) K, Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K]) ∂μ =
      ∫ y in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        (((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y) ∂μ := by
    intro x
    obtain ⟨C, hC⟩ := exists_bound_tsum_one hΦ h₁
      (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹)
    have key := setIntegral_mul_tsum_eq_tsum_GL μ hn h₁c h₁.1.isLeftInvariant h₁.2
      ⟨B₁, hB₁⟩ hΦc (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹)
      (fun g => summable_norm_ratMat hΦ t _ g) ⟨C, fun g hg => (hC g hg).2⟩
    have e : ∀ y : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) *
        ∑' γ : GL (Fin n) K, Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K]) =
        conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * (φ₁ (y : AdelicGLn.AdelicGL K n) *
          ∑' γ : GL (Fin n) K, Φ (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ :
            AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
              ratMat (γ : Matrix (Fin n) (Fin n) K) *
                ((y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) := by
      intro y
      rw [mul_assoc]
      congr 2
    have e' : ∀ y : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) * (((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y) =
        conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * (φ₁ (y : AdelicGLn.AdelicGL K n) * S x y) := by
      intro y
      rw [hP x y, mul_assoc]
    rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun y _ => e y,
      setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun y _ => e' y,
      integral_const_mul, integral_const_mul, ← key]

  have hB : ∀ y : normOneGL K n,
      ∫ x in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        Sh x y ∂μ =
      ∫ x in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        ShG x y ∂μ := by
    intro y
    obtain ⟨C, hC⟩ := exists_bound_tsum_one hΦh h₂
      (centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹)
    have key := setIntegral_mul_tsum_eq_tsum_GL μ hn h₂c' (isLeftInvariant_conj h₂.1.isLeftInvariant)
      (isCuspidal_conj h₂.2) hB₂' hΦhc (centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹)
      (fun g => summable_norm_ratMat hΦh t⁻¹ _ g)
      ⟨C, fun g hg => by rw [Complex.norm_conj]; exact (hC g hg).2⟩
    have e1 : ∀ x : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) * Sh x y = φ₁ (y : AdelicGLn.AdelicGL K n) *
          (conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * Sh x y) := fun x => by ring
    have e2 : ∀ x : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) * ShG x y = φ₁ (y : AdelicGLn.AdelicGL K n) *
          (conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * ShG x y) := fun x => by ring
    rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => e1 x,
      setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => e2 x,
      integral_const_mul, integral_const_mul]
    congr 1

  have hmeasSh : Continuous fun p : normOneGL K n × normOneGL K n => Sh p.1 p.2 := by
    have hc := continuous_tsum_ratMat hΦh
    have h4 : Continuous fun p : normOneGL K n × normOneGL K n =>
        (t⁻¹, ((p.2 : AdelicGLn.AdelicGL K n))⁻¹, ((p.1 : AdelicGLn.AdelicGL K n))) := by fun_prop
    have h5 := hc.comp h4
    simpa only [Function.comp_def] using h5
  have hmeasShG : Continuous fun p : normOneGL K n × normOneGL K n => ShG p.1 p.2 := by
    have hc := continuous_tsum_GL hΦh
    have h4 : Continuous fun p : normOneGL K n × normOneGL K n =>
        (t⁻¹, ((p.2 : AdelicGLn.AdelicGL K n))⁻¹, ((p.1 : AdelicGLn.AdelicGL K n))) := by fun_prop
    have h5 := hc.comp h4
    simp only [Function.comp_def] at h5
    refine h5.congr fun p => tsum_congr fun γ => ?_
    rw [coe_mul_diagonal_mul]
  have hbdSh : ∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
      φ₁ (y : AdelicGLn.AdelicGL K n) * Sh x y‖ ≤ C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂ := by
    intro x y
    obtain ⟨hs, hb⟩ := hC₂ y y.2 x x.2 t⁻¹
    rw [norm_mul, norm_mul, Complex.norm_conj]
    calc ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖Sh x y‖
        ≤ ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ *
          ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φh (((centralSection K n t⁻¹ *
            (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
                ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := by
          rw [mul_comm ‖φ₂ _‖]
          exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ _ := hb
  have hbdShG : ∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
      φ₁ (y : AdelicGLn.AdelicGL K n) * ShG x y‖ ≤ C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂ := by
    intro x y
    obtain ⟨hs, hb⟩ := hC₂ y y.2 x x.2 t⁻¹
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hs' := hs.comp_injective (Units.val_injective (α := Matrix (Fin n) (Fin n) K))
    calc ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖ShG x y‖
        ≤ ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ *
          ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φh (((centralSection K n t⁻¹ *
            (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
                ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := by
          rw [mul_comm ‖φ₂ _‖]
          refine mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hs').trans ?_)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          exact Summable.tsum_le_tsum_of_inj _ Units.val_injective (fun _ _ => norm_nonneg _)
            (fun _ => le_rfl) hs' hs
      _ ≤ _ := hb
  have hint : ∀ T : normOneGL K n → normOneGL K n → ℂ,
      Continuous (fun p : normOneGL K n × normOneGL K n => T p.1 p.2) →
      (∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * T x y‖ ≤
        C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂) →
      Integrable (Function.uncurry fun x y : normOneGL K n =>
        conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * T x y)
        ((μ.restrict F).prod (μ.restrict F)) := by
    intro T hT hTb
    refine Integrable.of_bound ?_ (C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂)
      (Eventually.of_forall fun p => hTb p.1 p.2)
    refine Continuous.aestronglyMeasurable ?_
    exact ((h₂c'.comp (continuous_subtype_val.comp continuous_fst)).mul
      (h₁c.comp (continuous_subtype_val.comp continuous_snd))).mul hT

  unfold thetaPairing
  dsimp only
  rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => hA x]
  have e3 : ∀ x y : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
      φ₁ (y : AdelicGLn.AdelicGL K n) * (((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y) =
      ((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * (conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) * Sh x y) := fun x y => by ring
  simp_rw [e3, integral_const_mul]
  congr 1
  rw [integral_integral_swap (hint Sh hmeasSh hbdSh)]
  simp_rw [hB]
  rw [← integral_integral_swap (hint ShG hmeasShG hbdShG)]
  refine setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => ?_
  refine setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun y _ => ?_
  rw [tsum_inv_eq]

end Symmetry

end GJGlobal

end

end GroundTheory.Automorphic
end
