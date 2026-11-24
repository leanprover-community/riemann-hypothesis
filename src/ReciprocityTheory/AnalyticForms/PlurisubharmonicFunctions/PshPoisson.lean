module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Metric Real Filter Topology InnerProductSpace

namespace ReciprocityTheory.AnForm.A

noncomputable def poissonInt (g : ℂ → ℝ) (r : ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel 0 w • g) 0 r

private lemma notMem_sphere_abs_of_mem_ball {r : ℝ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    w ∉ sphere (0 : ℂ) |r| := by
  have h := mem_ball_zero_iff.mp hw
  rw [mem_sphere_zero_iff_norm, abs_of_pos ((norm_nonneg w).trans_lt h)]
  exact h.ne

lemma poissonKernel_zero_continuousOn {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    ContinuousOn (poissonKernel 0 w) (sphere 0 r) := by
  simpa only [abs_of_pos hr] using
    continuousOn_poissonKernel_sphere (notMem_sphere_abs_of_mem_ball hw)

lemma poissonKernel_zero_nonneg {r : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) : 0 ≤ poissonKernel 0 w z := by
  rw [poissonKernel_def]
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  refine div_nonneg ?_ (sq_nonneg _)
  simp only [sub_zero]
  rw [hz]
  nlinarith [norm_nonneg w]

lemma poissonKernel_zero_le {r δ : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) (hδ : 0 < δ) (hzw : δ ≤ ‖z - w‖) :
    poissonKernel 0 w z ≤ (r ^ 2 - ‖w‖ ^ 2) / δ ^ 2 := by
  rw [poissonKernel_def]
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  simp only [sub_zero]
  rw [hz]
  have hnum : 0 ≤ r ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hden : δ ^ 2 ≤ ‖z - w‖ ^ 2 := by nlinarith [hzw, hδ]
  first
  | exact div_le_div_of_nonneg_left hnum (pow_pos hδ 2) hden

lemma circleAverage_poissonKernel_zero {r : ℝ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    Real.circleAverage (poissonKernel 0 w) 0 r = 1 := by
  have hc : HarmonicOnNhd (fun _ : ℂ => (1 : ℝ)) (closedBall 0 r) := harmonicOnNhd_const 1
  simpa [Pi.mul_def] using hc.circleAverage_poissonKernel_smul hw

lemma poissonInt_eq_re {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    poissonInt g r w =
      (Real.circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 r).re := by
  simp only [poissonInt, poissonKernel_eq_re_herglotzRieszKernel]
  exact (re_circleAverage_herglotzRieszKernel_smul (hg.circleIntegrable hr.le)
    (notMem_sphere_abs_of_mem_ball hw)).symm

lemma poissonInt_harmonicAt {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) : HarmonicAt (poissonInt g r) w := by
  have hi : CircleIntegrable (fun z => (g z : ℂ)) 0 r :=
    (Complex.continuous_ofReal.comp_continuousOn hg).circleIntegrable hr.le
  have hd : DifferentiableOn ℂ
      (fun z => Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • (g ζ : ℂ)) 0 r)
      (ball 0 r) := fun z hz =>
    (hasDerivAt_circleAverage_herglotzRieszKernel_smul hi
      (notMem_sphere_abs_of_mem_ball hz)).differentiableAt.differentiableWithinAt
  apply (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr
    (hd.analyticAt (isOpen_ball.mem_nhds hw)).harmonicAt_re
  filter_upwards [isOpen_ball.mem_nhds hw] with z hz
  exact poissonInt_eq_re hr hg hz

lemma poissonInt_zero {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) :
    poissonInt g r 0 = Real.circleAverage g 0 r := by
  unfold poissonInt
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hz
  have hz0 : ‖z‖ ≠ 0 := by rw [hz]; exact hr.ne'
  simp only [Pi.mul_apply, smul_eq_mul, poissonKernel_def, sub_zero, norm_zero]
  rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hz0)]
  ring

lemma poissonInt_sub {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) (c : ℝ) :
    poissonInt g r w - c =
      Real.circleAverage (fun z ↦ poissonKernel 0 w z * (g z - c)) 0 r := by
  have hP := poissonKernel_zero_continuousOn hr hw
  have hPg : CircleIntegrable (fun z => poissonKernel 0 w z * g z) 0 r :=
    (hP.mul hg).circleIntegrable hr.le
  have hPc : CircleIntegrable (c • poissonKernel 0 w) 0 r :=
    (continuousOn_const.mul hP).circleIntegrable hr.le
  rw [show (fun z => poissonKernel 0 w z * (g z - c)) =
      (fun z => poissonKernel 0 w z * g z) - c • poissonKernel 0 w from by
        ext z
        change poissonKernel 0 w z * (g z - c) = _ - c * poissonKernel 0 w z
        ring,
    Real.circleAverage_sub hPg hPc, Real.circleAverage_smul, circleAverage_poissonKernel_zero hw,
    smul_eq_mul, mul_one]
  rfl

lemma poissonInt_tendsto {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere (0 : ℂ) r) :
    Tendsto (poissonInt g r) (𝓝[ball 0 r] ζ₀) (𝓝 (g ζ₀)) := by
  have hζ : ‖ζ₀‖ = r := mem_sphere_zero_iff_norm.mp hζ₀
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ sphere (0 : ℂ) r, ‖g z - g ζ₀‖ ≤ M :=
    (isCompact_sphere 0 r).exists_bound_of_continuousOn (hg.sub continuousOn_const)
  obtain ⟨M', hM'⟩ : ∃ M', M' = max M 0 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M' := by rw [hM']; exact le_max_right _ _
  have hMM : ∀ z ∈ sphere (0 : ℂ) r, ‖g z - g ζ₀‖ ≤ M' := by
    intro z hz
    rw [hM']
    exact (hM z hz).trans (le_max_left _ _)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨η, hη, hgη⟩ := Metric.continuousOn_iff.mp hg ζ₀ hζ₀ (ε / 2) (half_pos hε)
  have hq : 0 < (η / 2) ^ 2 := pow_pos (half_pos hη) 2
  have hden : 0 < 8 * r * (M' + 1) := mul_pos (mul_pos (by norm_num) hr) (by linarith)
  refine ⟨min (η / 2) (ε * (η / 2) ^ 2 / (8 * r * (M' + 1))),
    lt_min (half_pos hη) (div_pos (mul_pos hε hq) hden), ?_⟩
  intro w hw hwd
  have hwb : ‖w‖ < r := mem_ball_zero_iff.mp hw
  have hδ1 : dist w ζ₀ < η / 2 := lt_of_lt_of_le hwd (min_le_left _ _)
  have hδ2 : dist w ζ₀ < ε * (η / 2) ^ 2 / (8 * r * (M' + 1)) :=
    lt_of_lt_of_le hwd (min_le_right _ _)
  have hnum : 0 ≤ r ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  obtain ⟨K, hK⟩ : ∃ K, K = M' * ((r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact mul_nonneg hM0 (div_nonneg hnum hq.le)
  have hd : r - ‖w‖ ≤ dist w ζ₀ := by
    rw [dist_comm, dist_eq_norm, ← hζ]
    exact norm_sub_norm_le ζ₀ w
  have hnum2 : r ^ 2 - ‖w‖ ^ 2 ≤ 2 * r * dist w ζ₀ := by
    nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 * r),
      sq_nonneg (r - ‖w‖), norm_nonneg w]
  have hd2 : dist w ζ₀ * (8 * r * (M' + 1)) < ε * (η / 2) ^ 2 := by
    first
    | exact (lt_div_iff₀ hden).mp hδ2
  have hKq : K * (η / 2) ^ 2 = M' * (r ^ 2 - ‖w‖ ^ 2) := by
    rw [hK, mul_assoc, div_mul_cancel₀ _ hq.ne']
  have hKlt : K < ε / 2 := by
    have h1 : M' * (r ^ 2 - ‖w‖ ^ 2) ≤ (M' + 1) * (2 * r * dist w ζ₀) := by
      have e1 := mul_le_mul_of_nonneg_left hnum2 hM0
      have e2 : 0 ≤ 2 * r * dist w ζ₀ := by positivity
      nlinarith [e1, e2]
    have h2 : K * (η / 2) ^ 2 < ε / 2 * (η / 2) ^ 2 := by
      calc K * (η / 2) ^ 2 = M' * (r ^ 2 - ‖w‖ ^ 2) := hKq
        _ ≤ (M' + 1) * (2 * r * dist w ζ₀) := h1
        _ = dist w ζ₀ * (8 * r * (M' + 1)) / 4 := by ring
        _ < ε * (η / 2) ^ 2 / 4 := by linarith
        _ ≤ ε / 2 * (η / 2) ^ 2 := by nlinarith [mul_pos hε hq]
    exact lt_of_mul_lt_mul_right h2 hq.le
  have hpt : ∀ z ∈ sphere (0 : ℂ) r,
      ‖poissonKernel 0 w z * (g z - g ζ₀)‖ ≤ ε / 2 * poissonKernel 0 w z + K := by
    intro z hz
    have hP0 := poissonKernel_zero_nonneg hw hz
    rw [norm_mul, Real.norm_of_nonneg hP0]
    by_cases hzη : dist z ζ₀ < η
    · have h3 := hgη z hz hzη
      rw [dist_eq_norm] at h3
      have h4 := mul_le_mul_of_nonneg_left h3.le hP0
      linarith
    · push_neg at hzη
      have hzw : η / 2 ≤ ‖z - w‖ := by
        have h5 := dist_triangle z w ζ₀
        rw [dist_eq_norm z w] at h5
        linarith
      have hPle := poissonKernel_zero_le hw hz (half_pos hη) hzw
      have hgM := hMM z hz
      have h6 : poissonKernel 0 w z * ‖g z - g ζ₀‖ ≤
          (r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2 * M' :=
        mul_le_mul hPle hgM (norm_nonneg _) (div_nonneg hnum hq.le)
      have h7 : (r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2 * M' = K := by rw [hK]; ring
      have h8 : 0 ≤ ε / 2 * poissonKernel 0 w z := mul_nonneg (half_pos hε).le hP0
      linarith
  have hPi : IntervalIntegrable (fun θ : ℝ ↦ poissonKernel 0 w (circleMap 0 r θ))
      MeasureTheory.volume 0 (2 * π) :=
    (poissonKernel_zero_continuousOn hr hw).circleIntegrable hr.le
  have hPint : ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ) = 2 * π := by
    have h1 := circleAverage_poissonKernel_zero (r := r) hw
    unfold Real.circleAverage at h1
    rw [smul_eq_mul] at h1
    calc ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ)
        = (2 * π) * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ = 2 * π := by rw [h1, mul_one]
  have hbound : ‖∫ θ in (0 : ℝ)..2 * π,
      poissonKernel 0 w (circleMap 0 r θ) * (g (circleMap 0 r θ) - g ζ₀)‖ ≤
      ∫ θ in (0 : ℝ)..2 * π, (ε / 2 * poissonKernel 0 w (circleMap 0 r θ) + K) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by positivity) ?_ ?_
    · first
      | exact Filter.Eventually.of_forall (fun θ _ ↦ hpt _ (circleMap_mem_sphere 0 hr.le θ))
    · exact (IntervalIntegrable.const_mul hPi (ε / 2)).add intervalIntegrable_const
  have hint : ∫ θ in (0 : ℝ)..2 * π, (ε / 2 * poissonKernel 0 w (circleMap 0 r θ) + K) =
      ε / 2 * (2 * π) + K * (2 * π) := by
    rw [intervalIntegral.integral_add (IntervalIntegrable.const_mul hPi (ε / 2))
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, hPint, sub_zero, smul_eq_mul]
    ring
  have hfin : (2 * π)⁻¹ * (ε / 2 * (2 * π) + K * (2 * π)) = ε / 2 + K := by
    field_simp
  rw [Real.dist_eq, poissonInt_sub hr hg hw (g ζ₀)]
  unfold Real.circleAverage
  simp only [smul_eq_mul]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), ← Real.norm_eq_abs]
  calc _ ≤ (2 * π)⁻¹ * (ε / 2 * (2 * π) + K * (2 * π)) :=
        mul_le_mul_of_nonneg_left (hbound.trans_eq hint) (by positivity)
    _ = ε / 2 + K := hfin
    _ < ε := by linarith

theorem poisson_ext {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (Metric.sphere 0 r)) :
    ∃ Φ : ℂ → ℝ, ContinuousOn Φ (Metric.closedBall 0 r) ∧ (∀ ζ ∈ Metric.sphere 0 r, Φ ζ = g ζ) ∧
      Φ 0 = Real.circleAverage g 0 r ∧
      ∀ a s, 0 < s → Metric.closedBall a s ⊆ Metric.ball 0 r → Real.circleAverage Φ a s = Φ a := by
  refine ⟨fun z ↦ if ‖z‖ < r then poissonInt g r z else g z, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz) with hlt | heq
    · have hzb : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr hlt
      have hca : ContinuousAt (poissonInt g r) z := by
        first
        | exact (poissonInt_harmonicAt hr hg hzb).1.continuousAt
      have hev : poissonInt g r =ᶠ[𝓝 z] fun z ↦ if ‖z‖ < r then poissonInt g r z else g z := by
        filter_upwards [isOpen_ball.mem_nhds hzb] with y hy
        rw [if_pos (mem_ball_zero_iff.mp hy)]
      first
      | exact (hca.congr hev).continuousWithinAt
    · have hzs : z ∈ sphere (0 : ℂ) r := mem_sphere_zero_iff_norm.mpr heq
      have hval : (if ‖z‖ < r then poissonInt g r z else g z) = g z :=
        if_neg (by rw [heq]; exact lt_irrefl r)
      show Filter.Tendsto (fun z ↦ if ‖z‖ < r then poissonInt g r z else g z)
        (𝓝[closedBall 0 r] z) (𝓝 (if ‖z‖ < r then poissonInt g r z else g z))
      rw [hval, ← Metric.ball_union_sphere, nhdsWithin_union]
      refine Filter.Tendsto.sup ?_ ?_
      · refine Filter.Tendsto.congr' ?_ (poissonInt_tendsto hr hg hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [if_pos (mem_ball_zero_iff.mp hy)]
      · refine Filter.Tendsto.congr' ?_ (hg z hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [if_neg (by rw [mem_sphere_zero_iff_norm.mp hy]; exact lt_irrefl r)]
  · intro ζ hζ
    exact if_neg (by rw [mem_sphere_zero_iff_norm.mp hζ]; exact lt_irrefl r)
  · show (if ‖(0 : ℂ)‖ < r then poissonInt g r 0 else g 0) = Real.circleAverage g 0 r
    rw [if_pos (by rw [norm_zero]; exact hr)]
    exact poissonInt_zero hr
  · intro a s hs hsub
    have hev : Set.EqOn (fun z ↦ if ‖z‖ < r then poissonInt g r z else g z) (poissonInt g r)
        (sphere a |s|) := by
      intro y hy
      rw [abs_of_pos hs] at hy
      have hyb : y ∈ ball (0 : ℂ) r := hsub (sphere_subset_closedBall hy)
      exact if_pos (mem_ball_zero_iff.mp hyb)
    rw [Real.circleAverage_congr_sphere hev]
    have ha : a ∈ ball (0 : ℂ) r := hsub (mem_closedBall_self hs.le)
    show _ = (if ‖a‖ < r then poissonInt g r a else g a)
    rw [if_pos (mem_ball_zero_iff.mp ha)]
    apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    intro y hy
    rw [abs_of_pos hs] at hy
    exact poissonInt_harmonicAt hr hg (hsub hy)

end ReciprocityTheory.AnForm.A
