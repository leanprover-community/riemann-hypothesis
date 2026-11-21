import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeOfDet
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormQuotientThetaFlatAttainsSupOffCommonZeros
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.QuotientNoPositiveMaxOffCommonZeros
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsMulNe

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem norm_le_rpow_of_weighted_sq_integrable :
    ∀ (n : ℕ) (g : V n → ℂ) (ρ b : ℝ), 0 < ρ → 0 ≤ b → DifferentiableOn ℂ g (Metric.ball 0 ρ) →
      ∫⁻ z in Metric.ball (0 : V n) ρ,
        ENNReal.ofReal (‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-(b + (n : ℝ)))) < ⊤ →
      ∃ C ε : ℝ, 0 < ε ∧ ∀ z : V n, z ≠ 0 → ‖z‖ < ε → ‖g z‖ ≤ C * ‖z‖ ^ b := by
  intro n g ρ b hρ hb hg hI
  set I := ∫⁻ z in Metric.ball (0 : V n) ρ,
        ENNReal.ofReal (‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-(b + (n : ℝ)))) with hIdef
  set v := volume (Metric.ball (0 : V n) 1) with hv
  have hv0 : v ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hvt : v ≠ ⊤ := measure_ball_lt_top.ne
  have hvr : 0 < v.toReal := ENNReal.toReal_pos hv0 hvt
  have hdim : Module.finrank ℝ (V n) = 2 * n := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  set K : ℝ := (4 : ℝ) ^ b * 16 ^ n * I.toReal / v.toReal with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨Real.sqrt K, ρ / 2, by positivity, fun z hz hzρ => ?_⟩
  set t := ‖z‖ with ht
  have ht0 : 0 < t := norm_pos_iff.2 hz
  have hsub : Metric.ball z (t / 2) ⊆ Metric.ball (0 : V n) ρ := by
    apply Metric.ball_subset_ball'
    rw [dist_zero_right]; linarith
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv n z (t / 2) g (fun _ => 1) (hg.mono hsub) measurable_const
  simp only [mul_one, lintegral_const, Measure.restrict_apply_univ, one_mul] at hmv
  rw [Measure.addHaar_ball_of_pos volume z (half_pos ht0), hdim, ← hv] at hmv
  have hs : 0 ≤ b + (n : ℝ) := by positivity
  have hbound : ∫⁻ w in Metric.ball z (t / 2), ‖g w‖ₑ ^ 2 ≤
      ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) * I := by
    calc ∫⁻ w in Metric.ball z (t / 2), ‖g w‖ₑ ^ 2
        ≤ ∫⁻ w in Metric.ball z (t / 2), ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) *
            ENNReal.ofReal (‖g w‖ ^ 2 * (‖w‖ ^ 2) ^ (-(b + (n : ℝ)))) := by
          refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun w hw => ?_
          have hw' : ‖w - z‖ < t / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
          have h1 : ‖w‖ ≤ 2 * t := by
            have := norm_sub_norm_le w z
            linarith
          have h2 : 0 < ‖w‖ := by
            have := norm_sub_norm_le z w
            rw [norm_sub_rev] at this
            linarith
          rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
            ← ENNReal.ofReal_pow (norm_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          have h3 : (‖w‖ ^ 2) ^ (b + (n : ℝ)) ≤ ((2 * t) ^ 2) ^ (b + (n : ℝ)) :=
            Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ h2.le h1 2) hs
          have h4 : 0 < (‖w‖ ^ 2) ^ (b + (n : ℝ)) := by positivity
          rw [Real.rpow_neg (by positivity)]
          calc ‖g w‖ ^ 2 = (‖w‖ ^ 2) ^ (b + (n : ℝ)) *
                (‖g w‖ ^ 2 * ((‖w‖ ^ 2) ^ (b + (n : ℝ)))⁻¹) := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) * ∫⁻ w in Metric.ball z (t / 2),
            ENNReal.ofReal (‖g w‖ ^ 2 * (‖w‖ ^ 2) ^ (-(b + (n : ℝ)))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          gcongr
          exact lintegral_mono_set hsub
  have hfin := hmv.trans hbound
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hfin
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    toReal_enorm, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hr
  have hid : ((2 * t) ^ 2) ^ (b + (n : ℝ)) =
      (4 : ℝ) ^ b * (t ^ b) ^ 2 * (16 ^ n * (t / 2) ^ (2 * n)) := by
    rw [Real.rpow_add (by positivity), Real.rpow_natCast]
    congr 1
    · rw [show (2 * t) ^ 2 = 4 * (t * t) by ring, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow ht0.le ht0.le, sq]
    · rw [pow_mul, ← mul_pow]
      congr 1
      ring
  rw [hid] at hr
  have hp : 0 < (t / 2) ^ (2 * n) := by positivity
  have hsq : ‖g z‖ ^ 2 ≤ K * (t ^ b) ^ 2 := by
    have hc : 0 < (t / 2) ^ (2 * n) * v.toReal := by positivity
    refine le_of_mul_le_mul_right (hr.trans (le_of_eq ?_)) hc
    rw [hK]
    field_simp
  calc ‖g z‖ ≤ Real.sqrt (K * (t ^ b) ^ 2) := Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt K * t ^ b := by
      rw [Real.sqrt_mul hK0, Real.sqrt_sq (by positivity)]

end GlobalTheory
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_bound_of_weighted_L2 : ∀ (n : ℕ) (g : V n → ℂ) (ρ b : ℝ), 0 < ρ → 0 ≤ b → DifferentiableOn ℂ g (Metric.ball 0 ρ) → ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-(b + (n : ℝ)))) < ⊤ → ∃ C ε : ℝ, 0 < ε ∧ ∀ z : V n, z ≠ 0 → ‖z‖ < ε → ‖g z‖ ≤ C * ‖z‖ ^ b := by
  atlas_forward_decl GlobalTheory.norm_le_rpow_of_weighted_sq_integrable
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem isBigO_norm_pow_of_le_rpow_sub_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Nontrivial E] (a : ℕ) (g : E → ℂ) (ρ C : ℝ) (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ g (Metric.ball 0 ρ))
    (hb : ∀ z : E, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ C * ‖z‖ ^ ((a : ℝ) - 1 / 2)) :
    g =O[𝓝 0] fun z => ‖z‖ ^ a := by
  have hball : Metric.ball (0 : E) ρ ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hρ
  have hc : ContinuousAt g 0 := hd.continuousOn.continuousAt hball
  cases a with
  | zero =>
    simp only [pow_zero]
    exact hc.tendsto.isBigO_one ℝ
  | succ m =>
    have he : ((m + 1 : ℕ) : ℝ) - 1 / 2 = (m : ℝ) + 1 / 2 := by push_cast; ring
    rw [he] at hb
    have hpos : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
    have hb' : ∀ z : E, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ |C| * ‖z‖ ^ ((m : ℝ) + 1 / 2) :=
      fun z hz hzρ => (hb z hz hzρ).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have hpow : ∀ s : ℝ, 0 < s →
        Filter.Tendsto (fun z : E => |C| * ‖z‖ ^ s) (𝓝 0) (𝓝 0) := by
      intro s hs
      have h1 : Continuous (fun z : E => |C| * ‖z‖ ^ s) :=
        continuous_const.mul (continuous_norm.rpow_const fun _ => Or.inr hs.le)
      have h2 := h1.tendsto 0
      simpa [Real.zero_rpow hs.ne'] using h2
    have hg0 : g 0 = 0 := by
      haveI : (𝓝[≠] (0 : E)).NeBot := Module.punctured_nhds_neBot ℂ E 0
      have h1 : Filter.Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto g (𝓝[≠] 0) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ ((hpow _ hpos).mono_left nhdsWithin_le_nhds)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with z hz hzρ
        exact hb' z hz (mem_ball_zero_iff.1 hzρ)
      exact tendsto_nhds_unique h1 h2
    have hb'' : ∀ z : E, ‖z‖ < ρ → ‖g z‖ ≤ |C| * ‖z‖ ^ ((m : ℝ) + 1 / 2) := by
      intro z hz
      rcases eq_or_ne z 0 with rfl | h
      · rw [hg0, norm_zero]; positivity
      · exact hb' z h hz
    have hmaps : Set.MapsTo g (Metric.ball 0 ρ)
        (Metric.closedBall (g 0) (|C| * ρ ^ ((m : ℝ) + 1 / 2))) := by
      intro z hz
      have hz' := mem_ball_zero_iff.1 hz
      rw [hg0, mem_closedBall_zero_iff]
      refine (hb'' z hz').trans ?_
      gcongr
    have ho : (fun w => g w - g 0) =o[𝓝 0] (fun w : E => ‖w - 0‖ ^ m) := by
      simp only [hg0, sub_zero]
      rw [Asymptotics.isLittleO_iff]
      intro ε hε
      filter_upwards [hball, (hpow (1 / 2) (by norm_num)).eventually (gt_mem_nhds hε)]
        with z hz hzε
      refine (hb'' z (mem_ball_zero_iff.1 hz)).trans ?_
      rw [Real.rpow_add' (norm_nonneg z) hpos.ne', Real.rpow_natCast, norm_pow, norm_norm]
      calc |C| * (‖z‖ ^ m * ‖z‖ ^ (1 / 2 : ℝ)) = (|C| * ‖z‖ ^ (1 / 2 : ℝ)) * ‖z‖ ^ m := by ring
        _ ≤ ε * ‖z‖ ^ m := by gcongr
    refine Asymptotics.IsBigO.of_bound (|C| * ρ ^ ((m : ℝ) + 1 / 2) / ρ ^ (m + 1)) ?_
    filter_upwards [hball] with z hz
    have key := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hd hmaps ho hz
    rw [hg0, dist_zero_right, dist_zero_right, div_pow] at key
    rw [norm_pow, norm_norm]
    refine key.trans_eq ?_
    ring

theorem isBigO_norm_pow_of_le_rpow_sub_half_euclidean :
    ∀ (n a : ℕ) (g : V n → ℂ) (ρ C : ℝ), 0 < n → 0 < ρ → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ z : V n, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ C * ‖z‖ ^ ((a : ℝ) - 1 / 2)) → g =O[𝓝 0] fun z => ‖z‖ ^ a := by
  intro n a g ρ C hn hρ hd hb
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (V n) := inferInstance
  exact isBigO_norm_pow_of_le_rpow_sub_half a g ρ C hρ hd hb

end GlobalTheory
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_isBigO_of_half_power_bound : ∀ (n a : ℕ) (g : V n → ℂ) (ρ C : ℝ), 0 < n → 0 < ρ → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ z : V n, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ C * ‖z‖ ^ ((a : ℝ) - 1 / 2)) → g =O[𝓝 0] fun z => ‖z‖ ^ a := by
  atlas_forward_decl GlobalTheory.isBigO_norm_pow_of_le_rpow_sub_half_euclidean
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.IntegralToOrder

open Filter Metric



end GlobalTheory.IntegralToOrder

namespace GlobalTheory


end GlobalTheory
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.HighOrderVanishing

open GlobalTheory.UpperModel

theorem eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (f : Frame X.Ψ r → ℂ), X.IsBddSec (Xa.Fp + Xa.T • Xa.L) f → (∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (Xa.T + nd X + 7)) → ∀ x ∈ X.dom, f x = 0 := by
  intro E _ _ _ r X Xa Fl f hg hO
  by_contra h0
  have hg0 : ∃ x ∈ X.dom, f x ≠ 0 := by
    push Not at h0
    exact h0
  obtain ⟨k, hk⟩ := exists_s_ne Fl
  have d1 := hg.1.1
  have d2 := Xa.secondTheta_vanishes.1.1.1.1
  have d3 := Xa.firstTheta_vanishes.1.1.1.1
  have d4 := Xa.et_sec.1
  have d5 := (Fl.s_van k).1.1.1.1
  obtain ⟨x, hx, hne⟩ := exists_mul_ne (((d1.mul d2).mul d3).mul d4) d5
    (exists_mul_ne ((d1.mul d2).mul d3) d4 (exists_mul_ne (d1.mul d2) d3
      (exists_mul_ne d1 d2 hg0 Xa.secondTheta_ne_zero) Xa.firstTheta_ne_zero) Xa.et_ne) hk
  simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or] at hne
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hne
  obtain ⟨x0, hx0, hs0, hpos, hmax⟩ := GlobalTheory.QuotientMax.main E r X Xa Fl f hg hO ⟨x, hx, by
    have p1 := pnorm_pos X (Xa.Fp + Xa.T • Xa.L) (P := f) hx h1
    have p2 := pnorm_pos X ((nd X + 4) • Xa.L - Xa.Fp) hx h2
    have p3 := pnorm_pos X (2 • Xa.L - Xa.de) hx h3
    have p4 := pnorm_pos X ((Xa.i * (Xa.g0 / 2)) • Xa.de) hx h4
    have p5 : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨k, Finset.mem_univ _, pow_pos (pnorm_pos X _ hx h5) 2⟩
    positivity⟩
  exact GlobalTheory.QuotNoMax.no_pos_max E r X Xa Fl f hg.1 x0 hx0 hs0 hpos hmax

end GlobalTheory.HighOrderVanishing
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UpTie


end GlobalTheory.UpTie
end
