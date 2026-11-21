import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFixedBallMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOnChart
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CutOffNear
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegBallMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLelongMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionCluster
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongRegularise
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegBallMass

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_indicator_mono (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S S' : Set (Fin n → ℂ)} (hS : S ⊆ S') (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ∧
      chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ≤
        chartDens J A (S'.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  have key : ∀ x ∈ fibre J A y, ∀ h : ∃ s, IsSheetAt J A x s,
      0 ≤ ReciprocityTheory.AnForm.maDens (fun k => (vecCons (logReg u ε) fun _ => euclPot :
        Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ h.choose) y := by
    intro x hx h
    have := hN n d J A u ε x h.choose hε h.choose_spec
    rwa [hx.2] at this
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  constructor
  · refine Finset.sum_nonneg fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (key x hx h)
    · exact le_rfl
  · refine Finset.sum_le_sum fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right
        (Set.indicator_le_indicator_of_subset hS (fun _ => zero_le_one) x) (key x hx h)
    · exact le_rfl

theorem measurable_chartDens_indicator (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ)) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) :
    Measurable (chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot)) := by
  refine (SheetSumMeasurable.proof n (d + 1) J A _ _ hJ hdim hA (measurable_const.indicator hS)
    fun k => ?_).1
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
  · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_euclPot n)

end RegBallMass

open RegBallMass in

theorem RegBallMass.proof (hF : RegFixedBallMass.Statement) (hM : RegLelongMono.Statement)
    (hN : RegDensNonneg.Statement) : RegBallMass.Statement := by
  intro n d J A u K hJ hdim hA hu hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  set c : ℝ := Real.sqrt (n + 1) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  obtain ⟨M, hMb⟩ := hF n d J A u (R₀ + c) hJ hdim hA hu
  refine ⟨max M 0, le_max_right _ _, fun ε hε x hx r hr => ?_⟩
  set F : Set (Fin n → ℂ) → (Fin (d + 1) → ℂ) → ℝ := fun S =>
    chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) with hFdef
  have h1 : Metric.ball x r ⊆ euclBall x (c * r) := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hr.1] at hy
    show Real.sqrt (euclPot (y - x)) < c * r
    rw [Real.sqrt_lt' (mul_pos hc0 hr.1), mul_pow, hc2]
    calc euclPot (y - x) = ∑ j, ‖(y - x) j‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin n, r ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hy j).le 2
      _ = n * r ^ 2 := by simp
      _ < (n + 1) * r ^ 2 := by nlinarith [pow_pos hr.1 2]
  have h2 : euclBall x c ⊆ Metric.closedBall 0 (R₀ + c) := by
    intro y hy
    have hy' : euclPot (y - x) < c ^ 2 := (Real.sqrt_lt' hc0).1 hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hyx : ‖y - x‖ ≤ c := by
      refine (pi_norm_le_iff_of_nonneg hc0.le).2 fun j => ?_
      have hj : ‖(y - x) j‖ ^ 2 ≤ euclPot (y - x) :=
        Finset.single_le_sum (f := fun j => ‖(y - x) j‖ ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc0.le two_ne_zero).1 (by linarith)
    calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ R₀ + c := add_le_add (hR₀ x hx) hyx
  have h3 : euclBall x (c * r) ⊆ euclBall x c := fun y hy =>
    show Real.sqrt (euclPot (y - x)) < c from
      lt_of_lt_of_le (show Real.sqrt (euclPot (y - x)) < c * r from hy)
        (mul_le_of_le_one_right hc0.le hr.2)
  have hpos : ∀ {S S' : Set (Fin n → ℂ)}, S ⊆ S' → ∀ y, 0 ≤ F S y ∧ F S y ≤ F S' y :=
    fun hS y => chartDens_indicator_mono hN hA u hε.1 hS y
  have hEm : ∀ ρ, MeasurableSet (euclBall x ρ) := fun ρ =>
    (isOpen_lt (((contDiff_euclPot n).continuous.comp
      (continuous_id.sub continuous_const)).sqrt) continuous_const).measurableSet
  obtain ⟨hIR, hIRle⟩ := hMb ε hε
  have hint : ∀ S, MeasurableSet S → S ⊆ Metric.closedBall 0 (R₀ + c) → Integrable (F S) :=
    fun S hS hSR => hIR.mono' (measurable_chartDens_indicator hJ hdim hA u hε.1 hS).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpos hSR y).1]; exact (hpos hSR y).2)
  have hBI := hint _ Metric.isOpen_ball.measurableSet (h1.trans (h3.trans h2))
  refine ⟨hBI, ?_⟩
  have hmono := hM n d J A u ε x (c * r) c hJ hdim hA hε.1 (mul_pos hc0 hr.1)
    (mul_le_of_le_one_right hc0.le hr.2)
  have hI1 : ∫ y, F (Metric.ball x r) y ≤ ∫ y, F (euclBall x (c * r)) y :=
    integral_mono hBI (hint _ (hEm _) (h3.trans h2)) fun y => (hpos h1 y).2
  have hI2 : ∫ y, F (euclBall x c) y ≤ ∫ y, F (Metric.closedBall 0 (R₀ + c)) y :=
    integral_mono (hint _ (hEm _) h2) hIR fun y => (hpos h2 y).2
  have hI3 : ∫ y, F (euclBall x (c * r)) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := by
    have : c ^ (2 * d) * ∫ y, F (euclBall x (c * r)) y ≤
        c ^ (2 * d) * (r ^ (2 * d) * ∫ y, F (euclBall x c) y) := by
      rw [← mul_assoc, ← mul_pow]; exact hmono
    exact le_of_mul_le_mul_left this (pow_pos hc0 _)
  calc ∫ y, F (Metric.ball x r) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := hI1.trans hI3
    _ ≤ r ^ (2 * d) * max M 0 :=
      mul_le_mul_of_nonneg_left (hI2.trans (hIRle.trans (le_max_left _ _))) (pow_nonneg hr.1.le _)
    _ = max M 0 * r ^ (2 * d) := mul_comm _ _

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegFixedBallMass

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_weight_mono (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {w w' : (Fin n → ℂ) → ℝ} (hw : ∀ x, w x ≤ w' x)
    (y : Fin (d + 1) → ℂ) :
    chartDens J A w (vecCons (logReg u ε) fun _ => euclPot) y ≤
      chartDens J A w' (vecCons (logReg u ε) fun _ => euclPot) y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with h
  · have h0 := hN n d J A u ε x h.choose hε h.choose_spec
    rw [hx.2] at h0
    exact mul_le_mul_of_nonneg_right (hw x) h0
  · exact le_rfl

end RegFixedBallMass

open RegFixedBallMass in

theorem RegFixedBallMass.proof (hN : RegDensNonneg.Statement) (hS : StokesOnChart.Statement)
    (hL : LogIntegrable.Statement) (hC : ChartMassCompact.Statement) : RegFixedBallMass.Statement := by
  intro n d J A u R hJ hdim hA hu
  obtain ⟨θ, hθs, hθ01, hθU, V, -, hBV, hθV⟩ :=
    exists_cutoff_near (S := Metric.closedBall (0 : Fin n → ℂ) R) Metric.isClosed_closedBall
      Metric.isOpen_ball (Metric.closedBall_subset_ball (lt_add_one R))
  have hθR : tsupport θ ⊆ Metric.closedBall 0 (R + 1) := hθU.trans Metric.ball_subset_closedBall
  have hθc : HasCompactSupport θ :=
    (isCompact_closedBall (0 : Fin n → ℂ) (R + 1)).of_isClosed_subset (isClosed_tsupport θ) hθR
  have hθw : ∀ x, (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x ≤ θ x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
    · rw [Set.indicator_of_mem hx, hθV x (hBV hx)]
    · rw [Set.indicator_of_notMem hx]
      exact (hθ01 x).1
  have hηs : ∀ i : Fin d, SmoothNear (zeroSet J) ((fun _ => euclPot) i) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
  have hθη : ∀ i : Fin (d + 1), SmoothNear (zeroSet J) (vecCons θ (fun _ => euclPot) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) hθs
    · simpa using hηs i
  have hu2 : linForm ((2 : ℂ) • u) ∉ J := by
    have he : linForm ((2 : ℂ) • u) = C 2 * linForm u := by
      simp [linForm, Finset.mul_sum, ← mul_assoc, C_mul]
    intro hm
    apply hu
    have := J.mul_mem_left (C (1 / 2 : ℂ)) (he ▸ hm)
    rwa [← mul_assoc, ← C_mul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, C_1, one_mul] at this
  obtain ⟨P, hP, hPy⟩ := LelongRegularise.exists_poly_of_linEval_eq_zero hJ hA hu
  have hgood : ∀ᵐ y : Fin (d + 1) → ℂ, ∀ x ∈ fibre J A y, linEval u x ≠ 0 := by
    filter_upwards [LelongRegularise.ae_eval_ne_zero P hP] with y hy x hx h0
    exact hy (hPy y x hx h0)
  have hTi := (hL n (d + 1) J A u _ (R + 1) hJ hdim hA hu hθη).add
    (hL n (d + 1) J A ((2 : ℂ) • u) _ (R + 1) hJ hdim hA hu2 hθη)
  refine ⟨∫ y, (chartAbsDens J A ((Metric.closedBall 0 (R + 1)).indicator fun x => Real.log ‖linEval u x‖)
      (vecCons θ fun _ => euclPot) + chartAbsDens J A ((Metric.closedBall 0 (R + 1)).indicator
        fun x => Real.log ‖linEval ((2 : ℂ) • u) x‖) (vecCons θ fun _ => euclPot)) y, fun ε hε => ?_⟩
  have hgs : ∀ i : Fin (d + 1), SmoothNear (zeroSet J) (vecCons (logReg u ε) (fun _ => euclPot) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε.1)
    · simpa using hηs i
  have hGi : Integrable (chartDens J A θ (vecCons (logReg u ε) fun _ => euclPot)) :=
    (hC n (d + 1) J A θ _ hJ hdim hA hθs.continuous.continuousOn hgs (Or.inl hθc)).mono'
      (SheetSumMeasurable.proof n (d + 1) J A θ _ hJ hdim hA hθs.continuous.measurable
        hgs).1.aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using abs_chartDens_le J A θ _ y)
  have hFi : Integrable (chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => euclPot)) :=
    hGi.mono' (RegBallMass.measurable_chartDens_indicator hJ hdim hA u hε.1
        Metric.isClosed_closedBall.measurableSet).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        have h0 := (RegBallMass.chartDens_indicator_mono hN hA u hε.1
          (subset_refl (Metric.closedBall (0 : Fin n → ℂ) R)) y).1
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact chartDens_weight_mono hN hA u hε.1 hθw y)
  refine ⟨hFi, ?_⟩
  calc ∫ y, chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (logReg u ε) fun _ => euclPot) y
      ≤ ∫ y, chartDens J A θ (vecCons (logReg u ε) fun _ => euclPot) y :=
        integral_mono hFi hGi fun y => chartDens_weight_mono hN hA u hε.1 hθw y
    _ = ∫ y, chartDens J A (logReg u ε) (vecCons θ fun _ => euclPot) y :=
        hS n d J A θ (logReg u ε) (fun _ => euclPot) hJ hdim hA (smoothNear_of_contDiff hθs)
          (smoothNear_of_contDiff (contDiff_logReg u hε.1)) hηs (Or.inl hθc)
    _ ≤ ‖∫ y, chartDens J A (logReg u ε) (vecCons θ fun _ => euclPot) y‖ := Real.le_norm_self _
    _ ≤ _ := norm_integral_le_of_norm_le hTi (by
        filter_upwards [hgood] with y hy
        exact LelongRegularise.norm_chartDens_le hA _ hθR hε.1 hε.2 hy)

end

end GroundTheory.Heights₂.Heights
end
