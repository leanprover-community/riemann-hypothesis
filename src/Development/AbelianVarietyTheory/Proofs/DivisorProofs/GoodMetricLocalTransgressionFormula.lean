import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeCoordHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormPoincareGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnChernTransgressionTermPoincareGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundFamilyOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOffCoordinateHyperplanes
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetLeOfWeightedEntryBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnOffCoordinateHyperplanesOfPoincareBo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPos

section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_mixTop_position_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) :
    ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = mixTop (fun _ => K₁) - mixTop fun _ => K₀ := by
  classical
  set T : ℕ → ℂ := fun k => mixTop (fun i : Fin n => if (i : ℕ) < k then K₁ else K₀) with hT
  have hterm : ∀ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = T ((j : ℕ) + 1) - T j := by
    intro j
    have hK : K₁ - K₀ = (1 : ℂ) • K₁ + (-1 : ℂ) • K₀ := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [hK, GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ K₁ K₀ 1 (-1) j, one_mul, neg_one_mul, ← sub_eq_add_neg]
    congr 1
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j + 1 := by have := Fin.lt_def.mp h1; omega
        simp [h1, this]
      · by_cases h2 : i = j
        · subst h2; simp
        · have h3 : ¬ ((i : ℕ) < j + 1) := by
            have : j < i := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
            have := Fin.lt_def.mp this; omega
          simp [h1, h2, h3]
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j := Fin.lt_def.mp h1
        simp [h1, this]
      · have : ¬ ((i : ℕ) < j) := fun h => h1 (Fin.lt_def.mpr h)
        by_cases h2 : i = j
        · simp [h1, h2, this]
        · simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Fin.sum_univ_eq_sum_range (fun k => T (k + 1) - T k) n, Finset.sum_range_sub]
  have e1 : (fun i : Fin n => if (i : ℕ) < n then K₁ else K₀) = fun _ => K₁ := by
    funext i; simp [i.isLt]
  have e0 : (fun i : Fin n => if (i : ℕ) < 0 then K₁ else K₀) = fun _ => K₀ := by
    funext i; simp
  show mixTop _ - mixTop _ = _
  rw [e1, e0]

end GlobalTheory.GoodTop
end

section
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem mdbar_neg_cut_conn_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    {G₀ G₁ : V n → Matrix r r ℂ} {v : V n} (hρ : DifferentiableAt ℝ ρ v) (h₀ : MContDiffAt 2 G₀ v)
    (u₀ : IsUnit (G₀ v).det) (h₁ : MContDiffAt 2 G₁ v) (u₁ : IsUnit (G₁ v).det) :
    (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b))
      = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  funext a b
  have c₀ : MContDiffAt 1 (fun x => conn G₀ x (coordVec a)) v := h₀.conn u₀ (by norm_num) _
  have c₁ : MContDiffAt 1 (fun x => conn G₁ x (coordVec a)) v := h₁.conn u₁ (by norm_num) _
  have hρ' : DifferentiableAt ℝ (fun x => (ρ x : ℂ)) v := Complex.ofRealCLM.differentiableAt.comp v hρ
  have hs : mdbar (fun x => conn G₁ x (coordVec a) - conn G₀ x (coordVec a)) v (coordVec b) =
      mdbar (fun x => conn G₁ x (coordVec a)) v (coordVec b) -
        mdbar (fun x => conn G₀ x (coordVec a)) v (coordVec b) := by
    simp only [sub_eq_add_neg]
    rw [mdbar_add c₁ c₀.neg, mdbar_neg]
  rw [mdbar_neg (fun x => (ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a))),
    mdbar_smul hρ' (c₁.sub c₀), hs]
  simp only [Pi.sub_apply, Pi.smul_apply, curvAt, cutForm, curv, smul_sub, smul_neg]
  abel

end GlobalTheory.GoodTop
end
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {v : V n}, DifferentiableAt ℝ ρ v → MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b)) = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  atlas_forward_decl GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub
end

section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

noncomputable def logCutoff (k : ℕ) (z : ℂ) : ℝ :=
  if z = 0 then 0 else Real.smoothTransition (2 + Real.log ‖z‖ / ((k : ℝ) + 1))

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma logCutoff_eq_zero_of_norm_le (k : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ Real.exp (-2 * ((k : ℝ) + 1))) : _root_.GlobalTheory.GoodTop.logCutoff k z = 0 := by
  unfold _root_.GlobalTheory.GoodTop.logCutoff
  split_ifs with h0
  · rfl
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog : Real.log ‖z‖ ≤ -2 * ((k : ℝ) + 1) := by
    rw [← Real.log_exp (-2 * ((k : ℝ) + 1))]
    exact Real.log_le_log (norm_pos_iff.mpr h0) hz
  rw [← sub_nonneg, show 0 - (2 + Real.log ‖z‖ / ((k : ℝ) + 1)) =
    (-2 * ((k : ℝ) + 1) - Real.log ‖z‖) / ((k : ℝ) + 1) by field_simp; ring]
  exact div_nonneg (by linarith) hk.le

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
lemma _root_.GlobalTheory.GoodTop.contDiff_logCutoff (k : ℕ) : ContDiff ℝ ∞ (_root_.GlobalTheory.GoodTop.logCutoff k) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases h0 : z = 0
  · subst h0
    have hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-2 * ((k : ℝ) + 1)))] with w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact logCutoff_eq_zero_of_norm_le k hw.le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 z]
        fun w => Real.smoothTransition (2 + Real.log ‖w‖ / ((k : ℝ) + 1)) := by
      filter_upwards [isOpen_ne.mem_nhds h0] with w hw
      simp only [_root_.GlobalTheory.GoodTop.logCutoff, if_neg (show w ≠ 0 from hw)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine Real.smoothTransition.contDiff.contDiffAt.comp z ?_
    refine contDiffAt_const.add (ContDiffAt.div_const ?_ _)
    exact (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr h0)).comp z (contDiffAt_norm ℝ h0)

end GlobalTheory.GoodTop
end

section
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma exists_bound_abs_deriv_smoothTransition_mul_sub_two :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| * |x - 2| ≤ M := by
  have hc : Continuous fun x : ℝ => |deriv Real.smoothTransition x| * |x - 2| :=
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).abs.mul
      (continuous_id.sub continuous_const).abs
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have := hM x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    exact this.trans (le_max_left _ _)
  · have hd : deriv Real.smoothTransition x = 0 := by
      rcases not_and_or.mp hx with h | h
      · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds (not_le.mp h)] with y hy
          exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
        rw [hev.deriv_eq, deriv_const]
      · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
          filter_upwards [Ioi_mem_nhds (not_le.mp h)] with y hy
          exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
        rw [hev.deriv_eq, deriv_const]
    rw [hd, abs_zero, zero_mul]
    exact le_max_right _ _

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma exists_bound_fderiv_logCutoff_mul_norm_mul_log :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (k : ℕ) (z c : ℂ),
      ‖fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) z c‖ * (‖z‖ * |Real.log ‖z‖|) ≤ M * ‖c‖ := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_abs_deriv_smoothTransition_mul_sub_two
  refine ⟨M, hM0, fun k z c => ?_⟩
  by_cases h0 : z = 0
  · subst h0
    simp only [norm_zero, zero_mul, mul_zero]
    positivity
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr h0
  have hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 z]
      fun w => Real.smoothTransition (2 + Real.log ‖w‖ / ((k : ℝ) + 1)) := by
    filter_upwards [isOpen_ne.mem_nhds h0] with w hw
    simp only [_root_.GlobalTheory.GoodTop.logCutoff, if_neg (show w ≠ 0 from hw)]
  set N := fderiv ℝ (fun w : ℂ => ‖w‖) z
  have hn : HasFDerivAt (fun w : ℂ => ‖w‖) N z :=
    ((contDiffAt_norm ℝ (n := 1) h0).differentiableAt one_ne_zero).hasFDerivAt
  have hN : ‖N‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (f := fun w : ℂ => ‖w‖) (x₀ := z)
      (lipschitzWith_one_norm (E := ℂ))
  have hl := (((Real.hasDerivAt_log hz.ne').div_const ((k : ℝ) + 1)).const_add 2)
  have hg := (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    (2 + Real.log ‖z‖ / ((k : ℝ) + 1))
  have hs := (hg.hasDerivAt.comp ‖z‖ hl).comp_hasFDerivAt z hn
  have hs' : HasFDerivAt (fun w : ℂ => Real.smoothTransition (2 + Real.log ‖w‖ / ((k : ℝ) + 1)))
      ((deriv Real.smoothTransition (2 + Real.log ‖z‖ / ((k : ℝ) + 1)) *
        (‖z‖⁻¹ / ((k : ℝ) + 1))) • N) z := hs
  rw [hev.fderiv_eq, hs'.fderiv]
  set x := 2 + Real.log ‖z‖ / ((k : ℝ) + 1)
  have hlog : Real.log ‖z‖ = (x - 2) * ((k : ℝ) + 1) := by
    simp only [x]; field_simp; ring
  have hNc : ‖N c‖ ≤ ‖c‖ := (N.le_opNorm c).trans (by simpa using mul_le_mul_of_nonneg_right hN (norm_nonneg c))
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Real.norm_eq_abs]
  rw [hlog]
  have e : |deriv Real.smoothTransition x * (‖z‖⁻¹ / ((k : ℝ) + 1)) * N c| *
      (‖z‖ * |(x - 2) * ((k : ℝ) + 1)|) = |deriv Real.smoothTransition x| * |x - 2| * |N c| := by
    rw [abs_mul, abs_mul, abs_mul, abs_div, abs_inv, abs_of_pos hz, abs_of_pos hk]
    field_simp
  rw [e]
  exact mul_le_mul (hM x) (by rw [← Real.norm_eq_abs]; exact hNc) (abs_nonneg _) hM0

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma logCutoff_mem_Icc (k : ℕ) (z : ℂ) :
    0 ≤ _root_.GlobalTheory.GoodTop.logCutoff k z ∧ _root_.GlobalTheory.GoodTop.logCutoff k z ≤ 1 := by
  unfold _root_.GlobalTheory.GoodTop.logCutoff
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma logCutoff_eq_zero_of_norm_le_exp_neg_two_mul (k : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ Real.exp (-2 * ((k : ℝ) + 1))) : _root_.GlobalTheory.GoodTop.logCutoff k z = 0 := by
  unfold _root_.GlobalTheory.GoodTop.logCutoff
  split_ifs with h0
  · rfl
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog : Real.log ‖z‖ ≤ -2 * ((k : ℝ) + 1) := by
    rw [← Real.log_exp (-2 * ((k : ℝ) + 1))]
    exact Real.log_le_log (norm_pos_iff.mpr h0) hz
  rw [← sub_nonneg, show 0 - (2 + Real.log ‖z‖ / ((k : ℝ) + 1)) =
    (-2 * ((k : ℝ) + 1) - Real.log ‖z‖) / ((k : ℝ) + 1) by field_simp; ring]
  exact div_nonneg (by linarith) hk.le

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma logCutoff_eq_one_of_exp_le_norm (k : ℕ) {z : ℂ}
    (hz : Real.exp (-((k : ℝ) + 1)) ≤ ‖z‖) : _root_.GlobalTheory.GoodTop.logCutoff k z = 1 := by
  have h0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact absurd hz (not_le.mpr (Real.exp_pos _))
  unfold _root_.GlobalTheory.GoodTop.logCutoff
  rw [if_neg h0]
  apply Real.smoothTransition.one_of_one_le
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog : -((k : ℝ) + 1) ≤ Real.log ‖z‖ := by
    rw [← Real.log_exp (-((k : ℝ) + 1))]
    exact Real.log_le_log (Real.exp_pos _) hz
  rw [← sub_nonneg, show 2 + Real.log ‖z‖ / ((k : ℝ) + 1) - 1 =
    (Real.log ‖z‖ + ((k : ℝ) + 1)) / ((k : ℝ) + 1) by field_simp; ring]
  exact div_nonneg (by linarith) hk.le

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma fderiv_prod_logCutoff_coordVec {n : ℕ} (k : ℕ) (S : Finset (Fin n))
    (v : _root_.ReciprocityTheory.L2DbarEstimates.V n) (b : Fin n) (c : ℂ) :
    fderiv ℝ (fun w : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k (w a)) v
        (c • _root_.GlobalTheory.GoodMetric.coordVec b) =
      if b ∈ S then (∏ a ∈ S.erase b, _root_.GlobalTheory.GoodTop.logCutoff k (v a)) *
        fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) c else 0 := by
  have hψ : ∀ z, HasFDerivAt (_root_.GlobalTheory.GoodTop.logCutoff k) (fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) z) z :=
    fun z => ((_root_.GlobalTheory.GoodTop.contDiff_logCutoff k).differentiable (by simp) z).hasFDerivAt
  have hχ : ContDiff ℝ 1 (fun w : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k (w a)) :=
    contDiff_prod fun a _ =>
      ((_root_.GlobalTheory.GoodTop.contDiff_logCutoff k).of_le (by simp)).comp
        ((EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) a).contDiff.restrict_scalars ℝ)
  have hline : HasDerivAt (fun t : ℝ => v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b))
      (c • _root_.GlobalTheory.GoodMetric.coordVec b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (c • _root_.GlobalTheory.GoodMetric.coordVec b)).const_add v
  have h1 := ((hχ.differentiable one_ne_zero) v).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline
    (by simp)
  have hcoord : ∀ (t : ℝ) (a : Fin n), (v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b)) a =
      if a = b then v b + (t : ℂ) * c else v a := by
    intro t a
    simp only [_root_.GlobalTheory.GoodMetric.coordVec, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply]
    split_ifs with h
    · subst h; simp [Complex.real_smul]
    · simp
  have hψline : HasDerivAt (fun t : ℝ => _root_.GlobalTheory.GoodTop.logCutoff k (v b + (t : ℂ) * c))
      (fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) c) 0 := by
    have hl : HasDerivAt (fun t : ℝ => v b + (t : ℂ) * c) c 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const c).const_add (v b)
    exact (hψ (v b)).comp_hasDerivAt_of_eq 0 hl (by simp)
  split_ifs with hb
  · have h2 : HasDerivAt (fun t : ℝ => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k
        ((v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b)) a))
        ((∏ a ∈ S.erase b, _root_.GlobalTheory.GoodTop.logCutoff k (v a)) *
          fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) c) 0 := by
      have e : (fun t : ℝ => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k
          ((v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b)) a)) =
          fun t : ℝ => (∏ a ∈ S.erase b, _root_.GlobalTheory.GoodTop.logCutoff k (v a)) *
            _root_.GlobalTheory.GoodTop.logCutoff k (v b + (t : ℂ) * c) := by
        funext t
        rw [← Finset.mul_prod_erase S _ hb, mul_comm, hcoord, if_pos rfl]
        congr 1
        refine Finset.prod_congr rfl fun a ha => ?_
        rw [hcoord, if_neg (Finset.ne_of_mem_erase ha)]
      rw [e]
      exact hψline.const_mul _
    exact h1.unique h2
  · have h2 : HasDerivAt (fun t : ℝ => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k
        ((v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b)) a)) 0 0 := by
      have e : (fun t : ℝ => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k
          ((v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b)) a)) =
          fun _ => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k (v a) := by
        funext t
        refine Finset.prod_congr rfl fun a ha => ?_
        rw [hcoord, if_neg (fun h : a = b => hb (h ▸ ha))]
      rw [e]
      exact hasDerivAt_const _ _
    exact h1.unique h2

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in

theorem _root_.GlobalTheory.GoodTop.exists_logCutoff_hyperplanes {n : ℕ} (S : Finset (Fin n)) :
    ∃ (C : ℝ) (χ : ℕ → _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ),
    (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k v, 0 ≤ χ k v ∧ χ k v ≤ 1) ∧
    (∀ k v, (∃ a ∈ S, v a = 0) → χ k =ᶠ[𝓝 v] fun _ => 0) ∧
    (∀ v : _root_.ReciprocityTheory.L2DbarEstimates.V n, (∀ a ∈ S, v a ≠ 0) → ∀ᶠ k in atTop, χ k =ᶠ[𝓝 v] fun _ => 1) ∧
    ∀ k v b, ‖_root_.GlobalTheory.dbar (fun x => (χ k x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖ *
      _root_.GlobalTheory.GoodMetric.poinWt S v b ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_logCutoff_mul_norm_mul_log
  have hproj : ∀ a : Fin n, ContDiff ℝ ∞ fun w : _root_.ReciprocityTheory.L2DbarEstimates.V n => w a := fun a =>
    (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) a).contDiff.restrict_scalars ℝ
  have hcont : ∀ a : Fin n, Continuous fun w : _root_.ReciprocityTheory.L2DbarEstimates.V n => w a := fun a => (hproj a).continuous
  refine ⟨M, fun k v => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k (v a), fun k => ?_, fun k v => ?_,
    fun k v hv => ?_, fun v hv => ?_, fun k v b => ?_⟩
  · exact contDiff_prod fun a _ => (_root_.GlobalTheory.GoodTop.contDiff_logCutoff k).comp (hproj a)
  · exact ⟨Finset.prod_nonneg fun a _ => (logCutoff_mem_Icc k _).1,
      Finset.prod_le_one (fun a _ => (logCutoff_mem_Icc k _).1)
        (fun a _ => (logCutoff_mem_Icc k _).2)⟩
  · obtain ⟨a, ha, h0⟩ := hv
    have hopen : IsOpen {w : _root_.ReciprocityTheory.L2DbarEstimates.V n | ‖w a‖ < Real.exp (-2 * ((k : ℝ) + 1))} :=
      isOpen_lt (hcont a).norm continuous_const
    filter_upwards [hopen.mem_nhds (by simp [h0, Real.exp_pos])] with w hw
    exact Finset.prod_eq_zero ha (logCutoff_eq_zero_of_norm_le_exp_neg_two_mul k (le_of_lt hw))
  · have hone : ∀ a ∈ S, ∀ᶠ k : ℕ in atTop, ∀ᶠ w in 𝓝 v, _root_.GlobalTheory.GoodTop.logCutoff k (w a) = 1 := by
      intro a ha
      have hr : 0 < ‖v a‖ / 2 := by have := norm_pos_iff.mpr (hv a ha); positivity
      obtain ⟨N, hN⟩ := exists_nat_gt (-Real.log (‖v a‖ / 2))
      have hopen : IsOpen {w : _root_.ReciprocityTheory.L2DbarEstimates.V n | ‖v a‖ / 2 < ‖w a‖} :=
        isOpen_lt continuous_const (hcont a).norm
      have hvm : v ∈ {w : _root_.ReciprocityTheory.L2DbarEstimates.V n | ‖v a‖ / 2 < ‖w a‖} := by
        have := norm_pos_iff.mpr (hv a ha)
        show ‖v a‖ / 2 < ‖v a‖
        linarith
      filter_upwards [Filter.eventually_ge_atTop N] with k hk
      filter_upwards [hopen.mem_nhds hvm] with w hw
      apply logCutoff_eq_one_of_exp_le_norm
      refine le_trans ?_ hw.le
      rw [← Real.exp_log hr]
      apply Real.exp_le_exp.mpr
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    filter_upwards [(Filter.eventually_all_finset S).2 hone] with k hk
    filter_upwards [(Filter.eventually_all_finset S).2 hk] with w hw
    exact Finset.prod_eq_one hw
  · set χk := fun w : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k (w a) with hχk
    have hd : DifferentiableAt ℝ χk v :=
      ((contDiff_prod fun a _ => (_root_.GlobalTheory.GoodTop.contDiff_logCutoff k).comp (hproj a)).differentiable
        (by simp)) v
    have hF : ∀ w, fderiv ℝ (fun x => (χk x : ℂ)) v w = ((fderiv ℝ χk v w : ℝ) : ℂ) := by
      intro w
      have hc := Complex.ofRealCLM.hasFDerivAt.comp v hd.hasFDerivAt
      rw [show (fun x => (χk x : ℂ)) = Complex.ofRealCLM ∘ χk from rfl, hc.fderiv]
      rfl
    rw [_root_.GlobalTheory.dbar_apply, hF, hF]
    have h1 := fderiv_prod_logCutoff_coordVec k S v b 1
    have hI := fderiv_prod_logCutoff_coordVec k S v b Complex.I
    rw [one_smul] at h1
    rw [h1, hI]
    unfold _root_.GlobalTheory.GoodMetric.poinWt
    split_ifs with hb
    · set P := ∏ a ∈ S.erase b, _root_.GlobalTheory.GoodTop.logCutoff k (v a)
      have hP : |P| ≤ 1 := by
        rw [abs_of_nonneg (Finset.prod_nonneg fun a _ => (logCutoff_mem_Icc k _).1)]
        exact Finset.prod_le_one (fun a _ => (logCutoff_mem_Icc k _).1)
          (fun a _ => (logCutoff_mem_Icc k _).2)
      have hw : 0 ≤ ‖v b‖ * |Real.log ‖v b‖| := by positivity
      have b1 := hM k (v b) 1
      have bI := hM k (v b) Complex.I
      rw [norm_one, mul_one] at b1
      rw [Complex.norm_I, mul_one] at bI
      rw [Real.norm_eq_abs] at b1 bI
      calc ‖(1 / 2 : ℂ) • (((P * fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) 1 : ℝ) : ℂ) +
            Complex.I • ((P * fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) Complex.I : ℝ) : ℂ))‖ *
            (‖v b‖ * |Real.log ‖v b‖|)
          ≤ (1 / 2) * (|fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) 1| +
              |fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) Complex.I|) * (‖v b‖ * |Real.log ‖v b‖|) := by
            refine mul_le_mul_of_nonneg_right ?_ hw
            rw [norm_smul, norm_div, norm_one, Complex.norm_two]
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (by norm_num)
            rw [norm_smul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
            exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) hP)
              (mul_le_of_le_one_left (abs_nonneg _) hP)
        _ ≤ M := by nlinarith
    · simpa using hM0

end GlobalTheory.GoodTop
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logCutoff_coordinateHyperplanes_poincareBound : ∀ {n : ℕ} (S : Finset (Fin n)), ∃ (C : ℝ) (χ : ℕ → V n → ℝ), (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k v, 0 ≤ χ k v ∧ χ k v ≤ 1) ∧ (∀ k v, (∃ a ∈ S, v a = 0) → χ k =ᶠ[𝓝 v] fun _ => 0) ∧ (∀ v : V n, (∀ a ∈ S, v a ≠ 0) → ∀ᶠ k in atTop, χ k =ᶠ[𝓝 v] fun _ => 1) ∧ ∀ k v b, ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b ≤ C := by
  atlas_forward_decl GlobalTheory.GoodTop.exists_logCutoff_hyperplanes
end

section
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

noncomputable section

namespace GlobalTheory.GoodTop.Piola

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem hasFDerivAt_dbar_apply {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z) (u : E) :
    HasFDerivAt (fun x => dbar f x u)
      ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) z) +
        Complex.I • (ContinuousLinearMap.apply ℝ ℂ (Complex.I • u)).comp (fderiv ℝ (fderiv ℝ f) z))) z := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h : ∀ a : E, HasFDerivAt (fun x => fderiv ℝ f x a)
      ((ContinuousLinearMap.apply ℝ ℂ a).comp (fderiv ℝ (fderiv ℝ f) z)) z :=
    fun a => (ContinuousLinearMap.apply ℝ ℂ a).hasFDerivAt.comp z hD.hasFDerivAt
  exact ((h u).add ((h (Complex.I • u)).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem dbar_dbar_symm {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    dbar (fun x => dbar f x w) z v = dbar (fun x => dbar f x v) z w := by
  have hs : IsSymmSndFDerivAt ℝ f z := hf.isSymmSndFDerivAt (by simp)
  rw [dbar_eq_of_hasFDerivAt (hasFDerivAt_dbar_apply hf w),
    dbar_eq_of_hasFDerivAt (hasFDerivAt_dbar_apply hf v)]
  simp only [antilinPart_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hs v w, hs v (Complex.I • w), hs (Complex.I • v) w, hs (Complex.I • v) (Complex.I • w)]
  ring_nf

theorem dbar_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {g : ι → E → ℂ} {z : E}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) z) (u : E) :
    dbar (fun x => ∏ i ∈ s, g i x) z u = ∑ k ∈ s, dbar (g k) z u * ∏ i ∈ s.erase k, g i z := by
  have h := HasFDerivAt.finset_prod (fun i hi => (hg i hi).hasFDerivAt)
  rw [dbar_eq_of_hasFDerivAt h]
  simp only [antilinPart_apply, dbar_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.GoodTop.Piola

namespace GlobalTheory.GoodTop

theorem piola_dbar {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n)
    (hf : ∀ i, i ≠ j → ContDiffAt ℝ 2 (f i) v) :
    ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
      dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) = 0 := by
  have e : ∀ w : Equiv.Perm (Fin n),
      dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) =
      ∑ k ∈ Finset.univ.erase j, dbar (fun x => dbar (f k) x (coordVec (w k))) v (coordVec (w j)) *
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i)) := fun w =>
    Piola.dbar_finset_prod (g := fun i x => dbar (f i) x (coordVec (w i))) _
      (fun i hi => (Piola.hasFDerivAt_dbar_apply (hf i (Finset.ne_of_mem_erase hi)) _).differentiableAt) _
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
  set T : Equiv.Perm (Fin n) → ℂ := fun w => ((Equiv.Perm.sign w : ℤ) : ℂ) *
    (dbar (fun x => dbar (f k) x (coordVec (w k))) v (coordVec (w j)) *
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i))) with hT
  have h1 : ∀ w, T (w * Equiv.swap j k) = -T w := by
    intro w
    have hp : ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec ((w * Equiv.swap j k) i)) =
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i)) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)) (Finset.ne_of_mem_erase hi)]
    simp only [hT]
    rw [hp, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Piola.dbar_dbar_symm (hf k hkj) (coordVec (w k)) (coordVec (w j)), Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hkj.symm]
    simp
  have h2 : ∑ w, T w = -∑ w, T w := by
    rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp (Equiv.mulRight (Equiv.swap j k)) T]
    exact Finset.sum_congr rfl fun w _ => h1 w
  show ∑ w, T w = 0
  linear_combination (1 / 2 : ℂ) * h2

end GlobalTheory.GoodTop
end
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piola_identity_wirtingerAntiholomorphic : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, i ≠ j → ContDiffAt ℝ 2 (f i) v) → ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) = 0 := by
  atlas_forward_decl GlobalTheory.GoodTop.piola_dbar
end

section
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem det_dbar_eq_sum_dbar : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, ContDiffAt ℝ 2 (f i) v) → (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) := by
  intro n f j v hf
  have hP := GlobalTheory.T.piola_identity_wirtingerAntiholomorphic f j v (fun i _ => hf i)
  have hd : ∀ w : Equiv.Perm (Fin n), DifferentiableAt ℝ
      (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v := fun w =>
    (HasFDerivAt.finset_prod (u := Finset.univ.erase j) (g := fun i x => dbar (f i) x (coordVec (w i)))
      (fun i _ => (differentiableAt_dbar_apply (hf i) _).hasFDerivAt)).differentiableAt
  have hj : DifferentiableAt ℝ (f j) v := (hf j).differentiableAt (by norm_num)
  have key : ∀ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
      dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) =
      ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, dbar (f i) v (coordVec (w i)) +
      f j v * (((Equiv.Perm.sign w : ℤ) : ℂ) *
        dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j))) := by
    intro w
    rw [dbar_mul hj (hd w), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    ring
  rw [Finset.sum_congr rfl (fun w _ => key w), Finset.sum_add_distrib, ← Finset.mul_sum, hP, mul_zero, add_zero,
    ← Matrix.det_transpose, Matrix.det_apply']
  rfl

end GlobalTheory.GoodTop
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_wirtingerAntiholomorphicDeriv_eq_sum : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, ContDiffAt ℝ 2 (f i) v) → (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) := by
  atlas_forward_decl GlobalTheory.GoodTop.det_dbar_eq_sum_dbar
end

section
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

noncomputable section

namespace GlobalTheory.GoodTop

theorem integral_dbar_eq_zero_of_hasCompactSupport {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ G y w) := fun w =>
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  refine ⟨?_, ?_⟩
  · simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  · simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc]
    simp

theorem setIntegral_dbar_eq_zero {n : ℕ} (U K : Set (V n)) (g : V n → ℂ) (ξ : V n)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hg : ContDiffOn ℝ 1 g U)
    (h0 : ∀ v ∈ U, v ∉ K → g v = 0) :
    IntegrableOn (fun v => dbar g v ξ) U ∧ ∫ v in U, dbar g v ξ = 0 := by
  classical
  set G : V n → ℂ := U.indicator g with hGdef
  have hin : ∀ v ∈ U, G =ᶠ[𝓝 v] g := fun v hv => by
    filter_upwards [hU.mem_nhds hv] with x hx
    exact Set.indicator_of_mem hx g
  have hz : ∀ x, x ∉ K → G x = 0 := fun x hx => by
    by_cases hxU : x ∈ U
    · rw [hGdef, Set.indicator_of_mem hxU, h0 x hxU hx]
    · rw [hGdef, Set.indicator_of_notMem hxU]
  have hout : ∀ v, v ∉ K → G =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hv] with x hx
    exact hz x hx
  have hG : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ U
    · exact (hg.contDiffAt (hU.mem_nhds hv)).congr_of_eventuallyEq (hin v hv)
    · exact contDiffAt_const.congr_of_eventuallyEq (hout v fun h => hv (hKU h))
  have hc : HasCompactSupport G := HasCompactSupport.intro hK hz
  obtain ⟨hI, hE⟩ := integral_dbar_eq_zero_of_hasCompactSupport hG hc ξ
  have heq : Set.EqOn (fun v => dbar G v ξ) (fun v => dbar g v ξ) U := fun v hv => by
    simp only [dbar_congr (hin v hv)]
  refine ⟨hI.integrableOn.congr_fun heq hU.measurableSet, ?_⟩
  rw [← setIntegral_congr_fun hU.measurableSet heq,
    setIntegral_eq_integral_of_forall_compl_eq_zero, hE]
  intro v hv
  rw [dbar_congr (hout v fun h => hv (hKU h))]
  simp [dbar_apply]

end GlobalTheory.GoodTop
end
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_antiholomorphicDeriv_compactSupport_eq_zero : ∀ {n : ℕ} (U K : Set (V n)) (g : V n → ℂ) (ξ : V n), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → (∀ v ∈ U, v ∉ K → g v = 0) → IntegrableOn (fun v => dbar g v ξ) U ∧ ∫ v in U, dbar g v ξ = 0 := by
  atlas_forward_decl GlobalTheory.GoodTop.setIntegral_dbar_eq_zero
end

section
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem contDiffOn_dbar_apply {n : ℕ} {U : Set (V n)} {f : V n → ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (ξ : V n) : ContDiffOn ℝ 1 (fun x => dbar f x ξ) U := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y) U := hf.fderiv_of_isOpen hU (by norm_num)
  have ha : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y ξ) U := h1.clm_apply contDiffOn_const
  have hb : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y (Complex.I • ξ)) U :=
    h1.clm_apply contDiffOn_const
  have : (fun x => dbar f x ξ) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ f x ξ + Complex.I • fderiv ℝ f x (Complex.I • ξ)) := by
    funext x; exact dbar_apply f x ξ
  rw [this]
  exact (ha.add (hb.const_smul Complex.I)).const_smul _

theorem integral_dbarJacobian_eq_zero : ∀ {n : ℕ} (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n),
    IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (f i) U) →
    (∀ v ∈ U, v ∉ K → f j v = 0) →
    ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  intro n U K f j hU hK hKU hf hz
  have hgC : ∀ w : Equiv.Perm (Fin n), ContDiffOn ℝ 1
      (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) U := fun w =>
    ((hf j).of_le (by norm_num)).mul
      (contDiffOn_prod fun i _ => contDiffOn_dbar_apply hU (hf i) _)
  have hg0 : ∀ w : Equiv.Perm (Fin n), ∀ v ∈ U, v ∉ K →
      (f j v * ∏ i ∈ Finset.univ.erase j, dbar (f i) v (coordVec (w i))) = 0 :=
    fun w v hv hvK => by rw [hz v hv hvK, zero_mul]
  have hT := fun w : Equiv.Perm (Fin n) =>
    GlobalTheory.T.integral_antiholomorphicDeriv_compactSupport_eq_zero U K _ (coordVec (w j)) hU hK hKU (hgC w) (hg0 w)
  have hcongr : ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det =
      ∫ v in U, ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
        dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v
          (coordVec (w j)) :=
    setIntegral_congr_fun hU.measurableSet fun v hv =>
      GlobalTheory.T.det_wirtingerAntiholomorphicDeriv_eq_sum f j v fun i => (hf i).contDiffAt (hU.mem_nhds hv)
  rw [hcongr, integral_finsetSum _ fun w _ => (hT w).1.const_mul _]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [integral_const_mul, (hT w).2, mul_zero]

end GlobalTheory.GoodTop
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_dbarJacobian_det_eq_zero_of_compactSupport : ∀ {n : ℕ} (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n), IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (f i) U) → (∀ v ∈ U, v ∉ K → f j v = 0) → ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  atlas_forward_decl GlobalTheory.GoodTop.integral_dbarJacobian_eq_zero
end

section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_offCoordinateHyperplanes : ∀ {n : ℕ} (S : Finset (Fin n)) (U : Set (V n)), IsOpen U → IsOpen (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen | exact GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen | (intros; apply GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem continuousOn_det_dbar {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {g : Fin n → V n → ℂ}
    (hg : ∀ i, ContDiffOn ℝ 2 (g i) Ω) :
    ContinuousOn (fun v => (Matrix.of fun i b => dbar (g i) v (coordVec b)).det) Ω := by
  have he : ∀ i (w : V n), ContinuousOn (fun v => dbar (g i) v w) Ω := by
    intro i w
    have hd := (hg i).continuousOn_fderiv_of_isOpen hΩ one_le_two
    simp only [dbar_apply]
    exact ((hd.clm_apply continuousOn_const).add
      ((hd.clm_apply continuousOn_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)
  have hM : ContinuousOn (fun v => Matrix.of fun i b => dbar (g i) v (coordVec b)) Ω :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun b => he i _
  exact (continuous_id.matrix_det).comp_continuousOn hM

theorem det_dbar_eq_zero_of_row {n : ℕ} {g : Fin n → V n → ℂ} {v : V n} (j : Fin n)
    (h : g j =ᶠ[𝓝 v] fun _ => 0) :
    (Matrix.of fun i b => dbar (g i) v (coordVec b)).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero j
  intro b
  simp [dbar_congr h]

theorem integral_det_dbar_eq_zero_of_poincare : ∀ {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (f : Fin n → V n → ℂ)
    (j : Fin n) (u : Equiv.Perm (Fin n)) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U →
    (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i, ContDiffOn ℝ 2 (f i) (offHyp S U)) →
    (∀ v ∈ offHyp S U, v ∉ K → f j v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ‖f j v‖ * poinWt S v (u j) ≤ c) →
    (∀ v ∈ offHyp S U, v ∈ K → ∀ i b, ‖dbar (f i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c) →
    IntegrableOn (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) (offHyp S U) ∧
      ∫ v in offHyp S U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  intro n S U K f j u c hU hK hKU hsmall hf hf0 hfb hdb
  have hΩ : IsOpen (offHyp S U) := GlobalTheory.T.isOpen_offCoordinateHyperplanes S U hU
  have hΩm : MeasurableSet (offHyp S U) := hΩ.measurableSet
  have hKc : IsClosed K := hK.isClosed
  have hwt : ∀ v ∈ offHyp S U, ∀ a, 0 < poinWt S v a := fun v hv =>
    (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv.1)).2 hv.2
  have hoff : ∀ g : Fin n → V n → ℂ, (∀ v ∈ offHyp S U, v ∉ K → g j v = 0) → ∀ v ∈ offHyp S U, v ∉ K →
      (Matrix.of fun i b => dbar (g i) v (coordVec b)).det = 0 := fun g hg v hv hvK =>
    det_dbar_eq_zero_of_row j (Filter.eventually_of_mem ((hΩ.sdiff hKc).mem_nhds ⟨hv, hvK⟩)
      fun x hx => hg x hx.1 hx.2)
  have hbd : ∀ (g : Fin n → V n → ℂ) (c' : ℝ), (∀ v ∈ offHyp S U, v ∈ K → ∀ i b,
      ‖dbar (g i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c') → ∀ v ∈ offHyp S U, v ∈ K →
      ‖(Matrix.of fun i b => dbar (g i) v (coordVec b)).det‖ ≤
        (n.factorial : ℝ) * |c'| ^ n * ∏ a, (poinWt S v a)⁻¹ ^ 2 :=
    fun g c' h v hv hvK => GlobalTheory.T.norm_det_le_of_weighted_entry_bound _ u _ c' (hwt v hv) (h v hv hvK)
  have hint := GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound S U K (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) _ hU hK hKU hsmall
    (continuousOn_det_dbar hΩ hf) (hoff f hf0) (hbd f c hdb)
  refine ⟨hint, ?_⟩
  obtain ⟨C, χ, hχs, hχ01, hχ0, hχ1, hχd⟩ := GlobalTheory.T.exists_logCutoff_coordinateHyperplanes_poincareBound S
  let F : ℕ → Fin n → V n → ℂ := fun k => Function.update f j (fun x => (χ k x : ℂ) * f j x)
  have hFj : ∀ k, F k j = fun x => (χ k x : ℂ) * f j x := fun k => by simp [F]
  have hFi : ∀ k i, i ≠ j → F k i = f i := fun k i hi => by simp [F, Function.update_of_ne hi]
  have hχC : ∀ k, ContDiffOn ℝ 2 (fun x => (χ k x : ℂ)) (offHyp S U) := fun k =>
    (Complex.ofRealCLM.contDiff.comp (by exact_mod_cast contDiff_infty.1 (hχs k) 2)).contDiffOn
  have hFs : ∀ k i, ContDiffOn ℝ 2 (F k i) (offHyp S U) := by
    intro k i
    by_cases hi : i = j
    · rw [hi, hFj]; exact (hχC k).mul (hf j)
    · rw [hFi k i hi]; exact hf i
  have hF0 : ∀ k, ∀ v ∈ offHyp S U, v ∉ K → F k j v = 0 := fun k v hv hvK => by
    rw [hFj]; simp [hf0 v hv hvK]
  have hzero : ∀ k, ∫ v in offHyp S U, (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det = 0 := by
    intro k
    have hsub : K ∩ tsupport (χ k) ⊆ offHyp S U := by
      rintro v ⟨hvK, hvt⟩
      refine ⟨hKU hvK, fun a ha h0 => ?_⟩
      exact (notMem_tsupport_iff_eventuallyEq.2 (hχ0 k v ⟨a, ha, h0⟩)) hvt
    refine GlobalTheory.T.integral_dbarJacobian_det_eq_zero_of_compactSupport (offHyp S U) (K ∩ tsupport (χ k)) (F k) j hΩ (hK.inter_right (isClosed_tsupport _))
      hsub (hFs k) ?_
    intro v hv hvn
    by_cases hvK : v ∈ K
    · have : v ∉ tsupport (χ k) := fun h => hvn ⟨hvK, h⟩
      rw [hFj]; simp [image_eq_zero_of_notMem_tsupport this]
    · exact hF0 k v hv hvK
  have hFb : ∀ k, ∀ v ∈ offHyp S U, v ∈ K → ∀ i b,
      ‖dbar (F k i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ |c| + |C| * |c| := by
    intro k v hv hvK i b
    have hw := hwt v hv
    have hCc : 0 ≤ |C| * |c| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    by_cases hi : i = j
    · rw [hi, hFj]
      have hvn := hΩ.mem_nhds hv
      rw [dbar_mul (a := fun x => (χ k x : ℂ)) (b := f j)
        (((hχC k).differentiableOn two_ne_zero).differentiableAt hvn)
        (((hf j).differentiableOn two_ne_zero).differentiableAt hvn) (coordVec b)]
      have h1 := hdb v hv hvK j b
      have h2 := hχd k v b
      have h3 := hfb v hv hvK
      have hχv := hχ01 k v
      have hp : 0 ≤ poinWt S v (u j) * poinWt S v b := mul_nonneg (hw _).le (hw _).le
      have hA : 0 ≤ ‖dbar (f j) v (coordVec b)‖ * (poinWt S v (u j) * poinWt S v b) :=
        mul_nonneg (norm_nonneg _) hp
      have hB : 0 ≤ ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b :=
        mul_nonneg (norm_nonneg _) (hw _).le
      have hE : 0 ≤ ‖f j v‖ * poinWt S v (u j) := mul_nonneg (norm_nonneg _) (hw _).le
      calc ‖(χ k v : ℂ) * dbar (f j) v (coordVec b) + dbar (fun x => (χ k x : ℂ)) v (coordVec b) * f j v‖ *
            (poinWt S v (u j) * poinWt S v b)
          ≤ (‖(χ k v : ℂ) * dbar (f j) v (coordVec b)‖ + ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b) * f j v‖) *
            (poinWt S v (u j) * poinWt S v b) := mul_le_mul_of_nonneg_right (norm_add_le _ _) hp
        _ = χ k v * (‖dbar (f j) v (coordVec b)‖ * (poinWt S v (u j) * poinWt S v b)) +
            (‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b) * (‖f j v‖ * poinWt S v (u j)) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hχv.1]; ring
        _ ≤ |c| + |C| * |c| := by
          refine add_le_add ?_ ?_
          · exact (mul_le_of_le_one_left hA hχv.2).trans (h1.trans (le_abs_self c))
          · exact mul_le_mul (h2.trans (le_abs_self C)) (h3.trans (le_abs_self c)) hE (abs_nonneg _)
    · rw [hFi k i hi]
      exact (hdb v hv hvK i b).trans ((le_abs_self c).trans (le_add_of_nonneg_right hCc))
  let bound : V n → ℝ := K.indicator fun v =>
    (n.factorial : ℝ) * |(|c| + |C| * |c|)| ^ n * ∏ a, (poinWt S v a)⁻¹ ^ 2
  have hbint : Integrable bound (volume.restrict (offHyp S U)) := by
    rw [integrable_indicator_iff hKc.measurableSet, IntegrableOn,
      Measure.restrict_restrict hKc.measurableSet]
    exact IntegrableOn.mono_set ((GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc S K hK fun v hv => hsmall v (hKU hv)).const_mul
      ((n.factorial : ℝ) * |(|c| + |C| * |c|)| ^ n)) Set.inter_subset_left
  have hmeas : ∀ k, AEStronglyMeasurable (fun v => (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det)
      (volume.restrict (offHyp S U)) := fun k =>
    (continuousOn_det_dbar hΩ (hFs k)).aestronglyMeasurable hΩm
  have hle : ∀ k, ∀ᵐ v ∂(volume.restrict (offHyp S U)),
      ‖(Matrix.of fun i b => dbar (F k i) v (coordVec b)).det‖ ≤ bound v := by
    intro k
    refine (ae_restrict_iff' hΩm).2 (Filter.Eventually.of_forall fun v hv => ?_)
    by_cases hvK : v ∈ K
    · simp only [bound, Set.indicator_of_mem hvK]
      exact hbd (F k) _ (hFb k) v hv hvK
    · simp only [bound, Set.indicator_of_notMem hvK]
      rw [hoff (F k) (hF0 k) v hv hvK, norm_zero]
  have hlim : ∀ᵐ v ∂(volume.restrict (offHyp S U)),
      Tendsto (fun k => (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det) atTop
        (𝓝 ((Matrix.of fun i b => dbar (f i) v (coordVec b)).det)) := by
    refine (ae_restrict_iff' hΩm).2 (Filter.Eventually.of_forall fun v hv => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχ1 v hv.2] with k hk
    congr 1
    ext i b
    by_cases hi : i = j
    · simp only [Matrix.of_apply, hi, hFj]
      rw [dbar_congr (f := f j) (g := fun x => (χ k x : ℂ) * f j x) (hk.mono fun x hx => by simp [hx])]
    · simp only [Matrix.of_apply, hFi k i hi]
  have hT := tendsto_integral_of_dominated_convergence bound hmeas hbint hle hlim
  have h0 : (fun k => ∫ v in offHyp S U, (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det) = fun _ => 0 :=
    funext hzero
  rw [h0] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

end GlobalTheory.GoodTop
end
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_antiholomorphicJacobian_eq_zero_poincareGrowth : ∀ {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n) (u : Equiv.Perm (Fin n)) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i, ContDiffOn ℝ 2 (f i) (offHyp S U)) → (∀ v ∈ offHyp S U, v ∉ K → f j v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ‖f j v‖ * poinWt S v (u j) ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i b, ‖dbar (f i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c) → IntegrableOn (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) (offHyp S U) ∧ ∫ v in offHyp S U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  atlas_forward_decl GlobalTheory.GoodTop.integral_det_dbar_eq_zero_of_poincare
end

section
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integral_mixTop_mdbar_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (θ : Fin n → Fin n → V n → Matrix r r ℂ) (j : Fin n) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v) → (∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ∀ a p q, ‖θ j a v p q‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q, ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ c) → IntegrableOn (fun v => mixTop fun i a b => mdbar (θ i a) v (coordVec b)) (offHyp S U) ∧ ∫ v in offHyp S U, (mixTop fun i a b => mdbar (θ i a) v (coordVec b)) = 0 := by
  intro n r _ _ S U K θ j c hU hK hKU hS hθ h0 hb hd
  have key : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      IntegrableOn (fun v => (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (offHyp S U) ∧
      ∫ v in offHyp S U, (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det = 0 := by
    intro p π u
    exact GlobalTheory.T.integral_antiholomorphicJacobian_eq_zero_poincareGrowth S U K (fun i x => θ i (u i) x (p i) (p (π i))) j u c hU hK hKU hS
      (fun i v hv => (hθ i (u i) v hv (p i) (p (π i))).contDiffWithinAt)
      (fun v hv hvK => by simp [h0 (u j) v hv hvK])
      (fun v hv hvK => hb v hv hvK (u j) _ _)
      (fun v hv hvK i b => hd v hv hvK i (u i) b (p i) (p (π i)))
  have hI : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      Integrable (fun v => ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p π u => Integrable.const_mul (key p π u).1 _
  have hI2 : ∀ (p : Fin n → r) (π : Equiv.Perm (Fin n)),
      Integrable (fun v => ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p π => integrable_finset_sum _ fun u _ => hI p π u
  have hI3 : ∀ (p : Fin n → r),
      Integrable (fun v => ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p => integrable_finset_sum _ fun π _ => hI2 p π
  unfold mixTop
  refine ⟨Integrable.const_mul (integrable_finset_sum _ fun p _ => hI3 p) _, ?_⟩
  rw [integral_const_mul, integral_finset_sum _ fun p _ => hI3 p]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun p _ => ?_)
  rw [integral_finset_sum _ fun π _ => hI2 p π]
  refine Finset.sum_eq_zero fun π _ => ?_
  rw [integral_finset_sum _ fun u _ => hI p π u]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [integral_const_mul, (key p π u).2, mul_zero]

end GlobalTheory.GoodTop
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_polarisedTopForm_dbarExact_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (θ : Fin n → Fin n → V n → Matrix r r ℂ) (j : Fin n) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v) → (∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ∀ a p q, ‖θ j a v p q‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q, ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ c) → IntegrableOn (fun v => mixTop fun i a b => mdbar (θ i a) v (coordVec b)) (offHyp S U) ∧ ∫ v in offHyp S U, (mixTop fun i a b => mdbar (θ i a) v (coordVec b)) = 0 := by
  atlas_forward_decl GlobalTheory.GoodTop.integral_mixTop_mdbar_eq_zero
end

section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

set_option autoImplicit false

noncomputable def transConn {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ)
    (G₀ G₁ : V n → Matrix r r ℂ) (j : Fin n) (i a : Fin n) : V n → Matrix r r ℂ :=
  if i < j then fun x => -conn G₁ x (coordVec a)
  else if i = j then fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))
  else fun x => -conn G₀ x (coordVec a)

theorem weighted_bound_cut_sum (x A B w C c : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ C) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hA : A * w ≤ c) (hB : B ≤ C) : x * (A + B) * w ≤ C * (|c| + C) := by
  have h1 : (A + B) * w ≤ |c| + C := by nlinarith [le_abs_self c]
  have hC : 0 ≤ C := hx0.trans hx
  rw [mul_assoc]
  exact mul_le_mul hx h1 (by positivity) hC

theorem weighted_bound_cut_entry (x X₁ X₀ d Y₁ Y₀ : ℂ) (wa wb C c : ℝ) (hx : ‖x‖ ≤ C) (hd : ‖d‖ ≤ C)
    (hX₁ : ‖X₁‖ * (wa * wb) ≤ c) (hX₀ : ‖X₀‖ ≤ C) (hY₁ : ‖Y₁‖ * wa ≤ c) (hY₀ : ‖Y₀‖ ≤ C)
    (hwa0 : 0 ≤ wa) (hwa1 : wa ≤ 1) (hwb0 : 0 ≤ wb) (hwb1 : wb ≤ 1) :
    ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ * (wa * wb) ≤ 2 * C * (|c| + C) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hx
  have e1 := weighted_bound_cut_sum ‖x‖ ‖X₁‖ ‖X₀‖ (wa * wb) C c (norm_nonneg _) hx (norm_nonneg _) (norm_nonneg _)
    (by positivity) (by nlinarith) hX₁ hX₀
  have e2 := weighted_bound_cut_sum ‖d‖ ‖Y₁‖ ‖Y₀‖ wa C c (norm_nonneg _) hd (norm_nonneg _) (norm_nonneg _)
    hwa0 hwa1 hY₁ hY₀
  have n1 : ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ ≤ ‖x‖ * (‖X₁‖ + ‖X₀‖) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;>
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
  have hww : 0 ≤ wa * wb := by positivity
  have e2' : ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) ≤ C * (|c| + C) := by
    have h0 : 0 ≤ ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa := by positivity
    calc ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) = (‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa) * wb := by ring
      _ ≤ (‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa) * 1 := mul_le_mul_of_nonneg_left hwb1 h0
      _ ≤ C * (|c| + C) := by rw [mul_one]; exact e2
  calc ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ * (wa * wb)
      ≤ (‖x‖ * (‖X₁‖ + ‖X₀‖) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖)) * (wa * wb) := mul_le_mul_of_nonneg_right n1 hww
    _ = ‖x‖ * (‖X₁‖ + ‖X₀‖) * (wa * wb) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) := by ring
    _ ≤ C * (|c| + C) + C * (|c| + C) := add_le_add e1 e2'
    _ = 2 * C * (|c| + C) := by ring

theorem integral_mixTop_position_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → ∀ j : Fin n, IntegrableOn (fun v => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)) (offHyp S U) ∧ ∫ v in offHyp S U, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j) = 0 := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hsmall hG₀ hG₁ hconn hcurv hρ hρK j
  obtain ⟨C, hC0, hC⟩ := exists_bound_smooth_data U K G₀ ρ hU hK hKU hG₀ hρ
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have h3 : (2 : WithTop ℕ∞) + 1 ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have hw : ∀ v ∈ U, ∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1 :=
    fun v hv a => (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv)).1 a
  have hρd : ∀ v ∈ U, ContDiffAt ℝ ∞ ρ v := fun v hv => hρ.contDiffAt (hU.mem_nhds hv)
  have hρc : ∀ v ∈ U, ContDiffAt ℝ 2 (fun x => (ρ x : ℂ)) v := fun v hv =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp v ((hρd v hv).of_le h2)
  set θ := transConn ρ G₀ G₁ j with hθ
  have hsm : ∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v := by
    intro i a v hv
    have h1 := (hG₁ v hv).1.conn (j := 2) (hG₁ v hv).2 h3 (coordVec a)
    have h0 := (hG₀ v hv.1).1.conn (j := 2) (hG₀ v hv.1).2 h3 (coordVec a)
    simp only [hθ, transConn]
    split_ifs
    · exact h1.neg
    · exact (MContDiffAt.smul (hρc v hv.1) (h1.sub h0)).neg
    · exact h0.neg
  have heq : ∀ v ∈ offHyp S U, (fun i a b => mdbar (θ i a) v (coordVec b)) =
      intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j := by
    intro v hv
    funext i a b
    simp only [hθ, transConn, intersection_update_fsHerm_neg_one]
    split_ifs with h h'
    · rw [mdbar_neg]; rfl
    · exact congrFun (congrFun (GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq ((hρd v hv.1).differentiableAt (by simp))
        ((hG₀ v hv.1).1.of_le h2) (hG₀ v hv.1).2 ((hG₁ v hv).1.of_le h2) (hG₁ v hv).2) a) b
    · rw [mdbar_neg]; rfl
  have hzero : ∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0 := by
    intro a v hv hvK
    simp [hθ, transConn, hρK v hv.1 hvK]
  have hcC : 0 ≤ C * (|c| + C) := by positivity
  have hbd1 : ∀ v ∈ offHyp S U, v ∈ K → ∀ a p q,
      ‖θ j a v p q‖ * poinWt S v a ≤ |c| + C + 2 * C * (|c| + C) := by
    intro v hv hvK a p q
    obtain ⟨hρv, -, hc0, -⟩ := hC v hvK
    simp only [hθ, transConn, lt_irrefl, if_false, if_true, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e := weighted_bound_cut_sum |ρ v| ‖conn G₁ v (coordVec a) p q‖ ‖conn G₀ v (coordVec a) p q‖ (poinWt S v a) C c
      (abs_nonneg _) hρv (norm_nonneg _) (norm_nonneg _) (hw v hv.1 a).1 (hw v hv.1 a).2
      (hconn v hv a p q) (hc0 a p q)
    have n1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (norm_sub_le (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)) (abs_nonneg (ρ v)))
      (hw v hv.1 a).1
    have : 0 ≤ |c| := abs_nonneg c
    nlinarith
  have hbd2 : ∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q,
      ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤
        |c| + C + 2 * C * (|c| + C) := by
    intro v hv hvK i a b p q
    obtain ⟨hρv, hdv, hc0, hk0⟩ := hC v hvK
    obtain ⟨hwa0, hwa1⟩ := hw v hv.1 a
    obtain ⟨hwb0, hwb1⟩ := hw v hv.1 b
    have hww : 0 ≤ poinWt S v a * poinWt S v b := by positivity
    have hww1 : poinWt S v a * poinWt S v b ≤ 1 := by nlinarith
    have hca : 0 ≤ |c| := abs_nonneg c
    rw [show mdbar (θ i a) v (coordVec b) = _ from congrFun (congrFun (congrFun (heq v hv) i) a) b]
    simp only [intersection_update_fsHerm_neg_one]
    split_ifs with h h'
    · have := hcurv v hv a b p q
      simp only [curvAt]
      nlinarith [le_abs_self c]
    · simp only [curvAt, cutForm, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul]
      have e := weighted_bound_cut_entry (ρ v : ℂ) (curv G₁ v (coordVec a) (coordVec b) p q) (curv G₀ v (coordVec a) (coordVec b) p q)
        (dbar (fun x => (ρ x : ℂ)) v (coordVec b)) (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)
        (poinWt S v a) (poinWt S v b) C c (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hρv) (hdv b)
        (hcurv v hv a b p q) (hk0 a b p q) (hconn v hv a p q) (hc0 a p q) hwa0 hwa1 hwb0 hwb1
      nlinarith
    · simp only [curvAt]
      have := hk0 a b p q
      have := mul_le_mul_of_nonneg_left hww1 (norm_nonneg (curv G₀ v (coordVec a) (coordVec b) p q))
      nlinarith
  obtain ⟨hi, hint⟩ := GlobalTheory.T.integral_polarisedTopForm_dbarExact_eq_zero S U K θ j (|c| + C + 2 * C * (|c| + C)) hU hK hKU hsmall hsm hzero
    hbd1 hbd2
  have hO : MeasurableSet (offHyp S U) := (isOpen_offHyp_of_isOpen S U hU).measurableSet
  refine ⟨hi.congr_fun (fun v hv => congrArg mixTop (heq v hv)) hO, ?_⟩
  rw [← hint]
  exact setIntegral_congr_fun hO fun v hv => congrArg mixTop (heq v hv).symm

end GlobalTheory.GoodTop
end

section
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mixTop_slot_smul_sub_sub {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] (A B D : _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r) (s : ℂ) (j : Fin n) :
    _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (s • (A - B) - D) B j) =
      s * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (A - B) B j) +
        (-1) * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A D B j) := by
  rw [← _root_.GlobalTheory.GoodTop.mixTop_position_linear, neg_one_smul, ← sub_eq_add_neg]

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in

theorem _root_.GlobalTheory.GoodTop.integral_cutTop_sub : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ * _root_.GlobalTheory.GoodMetric.poinWt S v a ≤ c) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ * (_root_.GlobalTheory.GoodMetric.poinWt S v a * _root_.GlobalTheory.GoodMetric.poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) - (∫ v in U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) = ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hS hG₀ hG₁ hconn hcurv hρ hρK
  have hstokes := _root_.GlobalTheory.GoodTop.integral_mixTop_position_eq_zero S U K G₀ G₁ ρ c hU hK hKU
    hS hG₀ hG₁ hconn hcurv hρ hρK
  have hF₁ := _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hF₀ := (_root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth U K G₀ ρ hU hK hKU hG₀ hρ
    hρK).mono_set (fun v hv => ((mem_offHyp_iff (S := S)).1 hv).1)
  have hT := _root_.GlobalTheory.GoodTop.integrableOn_corrC S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hpt : ∀ v, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v =
      ∑ j, _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ v)
        ((ρ v : ℂ) • (_root_.GlobalTheory.GoodTop.curvAt G₁ v - _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
          _root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ v) (_root_.GlobalTheory.GoodTop.curvAt G₀ v) j) := by
    intro v
    simp_rw [mixTop_slot_smul_sub_sub]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      _root_.GlobalTheory.GoodTop.sum_mixTop_position_sub]
    unfold _root_.GlobalTheory.GoodTop.corrC
    ring
  have hzero : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finset_sum _ fun j _ => (hstokes j).1]
    exact Finset.sum_eq_zero fun j _ => (hstokes j).2
  have hsplit : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) =
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
    have hsub : IntegrableOn (fun v =>
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v))
        (_root_.GlobalTheory.GoodTop.offHyp S U) := hF₁.sub hF₀
    exact (integral_sub hsub hT).trans (congrArg (· - _) (integral_sub hF₁ hF₀))
  rw [← setIntegral_congr_set (_root_.GlobalTheory.GoodTop.offHyp_ae_eq S U)]
  linear_combination hzero - hsplit

end GlobalTheory.GoodTop
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodMetric_local_transgression_formula : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → (∫ v in offHyp S U, (ρ v : ℂ) * mixTop fun _ => curvAt G₁ v) - (∫ v in U, (ρ v : ℂ) * mixTop fun _ => curvAt G₀ v) = ∫ v in offHyp S U, corrC ρ G₀ G₁ v := by
  atlas_forward_decl GlobalTheory.GoodTop.integral_cutTop_sub
end
