import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWLimOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.GaugeExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PhiDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvT
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueHaarDensityAtIdentity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDens
import BuildAid.ForwardExisting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvO
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TransW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarHyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVolMt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupGaugeVolumeInHermitianUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTubeGaugeMassAsymptotic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI

section
section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.UpperDensBounds

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem tendsto_const_mul_nhdsGT {k : ℝ} (hk : 0 < k) :
    Tendsto (fun r : ℝ => k * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun r : ℝ => k * r) (𝓝 0) (𝓝 (k * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos hk hr

theorem ball_scale (l : Measure V) [l.IsAddHaarMeasure] (x : V) {k s : ℝ} (hk : 0 < k) (hs : 0 < s) :
    l (Metric.ball 0 (k * s)) = ENNReal.ofReal (k ^ Module.finrank ℝ V) * l (Metric.closedBall x s) := by
  rw [Measure.addHaar_ball_of_pos l 0 (mul_pos hk hs), Measure.addHaar_closedBall l x hs.le, mul_pow,
    ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem mul_div_scale (t : ℝ) (ht : 0 < t) (d : ℕ) (a b : ℝ≥0∞) :
    ENNReal.ofReal (t ^ d) * (a / (ENNReal.ofReal (t ^ d) * b)) = a / b := by
  have hp : ENNReal.ofReal (t ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hp ENNReal.ofReal_ne_top]

end GlobalTheory.UpperDensBounds

open GlobalTheory.UpperDensBounds in

theorem GlobalTheory.upperDens_bounds_of_almost_homogeneous : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (c : ℝ≥0∞), c ≠ ⊤ → Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) → ∀ ε η : ℝ, 0 < ε → ε < 1 → (∀ x : V, ‖x‖ < η → ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧ ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) → ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ V) * c ≤ GlobalTheory.HaarDensChart.upperDens l ν x ∧ GlobalTheory.HaarDensChart.upperDens l ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ V) * c := by
  intro V _ _ _ _ _ l ν _ _ c _ hc ε η h0 h1 H x hx
  have he : 0 < 1 - ε := by linarith
  have hp : 0 < 1 + ε := by linarith
  set d := Module.finrank ℝ V
  unfold GlobalTheory.HaarDensChart.upperDens
  constructor
  ·
    set u : ℝ := (1 + ε)⁻¹ with hu
    have hu0 : 0 < u := inv_pos.mpr hp
    have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (u ^ d) *
        (ν (Metric.ball 0 (u * s)) / l (Metric.ball 0 (u * s)))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (u ^ d) * c)) :=
      ENNReal.Tendsto.const_mul (hc.comp (tendsto_const_mul_nhdsGT hu0)) (Or.inr ENNReal.ofReal_ne_top)
    rw [← ht.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [(tendsto_const_mul_nhdsGT hu0).eventually (H x hx), self_mem_nhdsWithin] with s hs hs0
    have hs0 : 0 < s := hs0
    rw [ball_scale l x hu0 hs0, mul_div_scale u hu0 d]
    refine ENNReal.div_le_div_right ?_ _
    have hr : (1 + ε) * (u * s) = s := by rw [hu, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    have := hs.2
    rw [hr] at this
    exact this.trans (measure_mono Metric.ball_subset_closedBall)
  ·
    set t : ℝ := (1 + ε) / (1 - ε) with htdef
    have ht0 : 0 < t := div_pos hp he
    have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (t ^ d) *
        (ν (Metric.ball 0 (t * s)) / l (Metric.ball 0 (t * s)))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (t ^ d) * c)) :=
      ENNReal.Tendsto.const_mul (hc.comp (tendsto_const_mul_nhdsGT ht0)) (Or.inr ENNReal.ofReal_ne_top)
    rw [← ht.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [(tendsto_const_mul_nhdsGT ht0).eventually (H x hx), self_mem_nhdsWithin] with s hs hs0
    have hs0 : 0 < s := hs0
    rw [ball_scale l x ht0 hs0, mul_div_scale t ht0 d]
    refine ENNReal.div_le_div_right ?_ _
    have hr : (1 - ε) * (t * s) = (1 + ε) * s := by
      rw [htdef, ← mul_assoc, mul_div_cancel₀ _ he.ne']
    refine le_trans (measure_mono (Metric.closedBall_subset_ball ?_)) hs.1
    rw [hr]; nlinarith
end
end

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperDensity_bounds_almost_homogeneous_measure : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (c : ℝ≥0∞), c ≠ ⊤ → Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) → ∀ ε η : ℝ, 0 < ε → ε < 1 → (∀ x : V, ‖x‖ < η → ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧ ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) → ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ V) * c ≤ GlobalTheory.HaarDensChart.upperDens l ν x ∧ GlobalTheory.HaarDensChart.upperDens l ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ V) * c := by
  atlas_forward_decl GlobalTheory.upperDens_bounds_of_almost_homogeneous
end

section
section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory

theorem measure_ball_eq_lintegral_upperDens : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (η : ℝ) (C : ℝ≥0), (∀ x : V, ‖x‖ < η → GlobalTheory.HaarDensChart.upperDens l ν x < C) → ∀ ρ : ℝ, ρ ≤ η → ν (Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
  intro V _ _ _ _ _ l ν _ _ η C hC ρ hρ
  set U : Set V := Metric.ball (0 : V) η with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball

  have key : ∀ x ∈ U, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ν (Metric.closedBall x r) ≤ ((C : ℝ≥0) • l) (Metric.closedBall x r) := by
    intro x hx
    have h0 : limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) < (C : ℝ≥0∞) := hC x (mem_ball_zero_iff.1 hx)
    filter_upwards [Filter.eventually_lt_of_limsup_lt h0, self_mem_nhdsWithin] with r hr hr0
    have hpos : l (Metric.closedBall x r) ≠ 0 := (Metric.measure_closedBall_pos l x hr0).ne'
    have hfin : l (Metric.closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ((ENNReal.div_lt_iff (Or.inl hpos) (Or.inl hfin)).1 hr).le

  have hle : ∀ s ⊆ U, ν s ≤ ((C : ℝ≥0) • l) s := fun s hs =>
    (Besicovitch.vitaliFamily ν).measure_le_of_frequently_le ((C : ℝ≥0) • l)
      Measure.AbsolutelyContinuous.rfl s
      (fun x hx => (Besicovitch.tendsto_filterAt ν x).frequently (key x (hs hx)).frequently)
  have hac : ν.restrict U ≪ l := by
    intro s hs
    rw [Measure.restrict_apply' hUo.measurableSet]
    refine le_antisymm ?_ (by simp)
    calc ν (s ∩ U) ≤ ((C : ℝ≥0) • l) (s ∩ U) := hle _ Set.inter_subset_right
      _ ≤ ((C : ℝ≥0) • l) s := measure_mono Set.inter_subset_left
      _ = 0 := by simp [hs]

  have hae : ∀ᵐ x ∂l, x ∈ U →
      GlobalTheory.HaarDensChart.upperDens l ν x = (ν.restrict U).rnDeriv l x := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv (ν.restrict U) l] with x hx hxU
    have hev : (fun r : ℝ => ν.restrict U (Metric.closedBall x r) / l (Metric.closedBall x r))
        =ᶠ[𝓝[>] (0 : ℝ)] (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) := by
      obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hUo x hxU
      filter_upwards [Ioo_mem_nhdsGT εpos] with r hr
      rw [Measure.restrict_eq_self _ ((Metric.closedBall_subset_ball hr.2).trans hε)]
    show limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) = _
    exact (hx.congr' hev).limsup_eq
  have hsub : Metric.ball (0 : V) ρ ⊆ U := Metric.ball_subset_ball hρ
  calc ν (Metric.ball 0 ρ) = ν.restrict U (Metric.ball 0 ρ) :=
        (Measure.restrict_eq_self _ hsub).symm
    _ = l.withDensity ((ν.restrict U).rnDeriv l) (Metric.ball 0 ρ) := by
        rw [Measure.withDensity_rnDeriv_eq _ _ hac]
    _ = ∫⁻ x in Metric.ball 0 ρ, (ν.restrict U).rnDeriv l x ∂l :=
        withDensity_apply _ Metric.isOpen_ball.measurableSet
    _ = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
        refine setLIntegral_congr_fun_ae Metric.isOpen_ball.measurableSet ?_
        filter_upwards [hae] with x hx hxρ
        exact (hx (hsub hxρ)).symm

end GlobalTheory
end

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_ball_eq_lintegral_upperMeasureDensity : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (η : ℝ) (C : ℝ≥0), (∀ x : V, ‖x‖ < η → GlobalTheory.HaarDensChart.upperDens l ν x < C) → ∀ ρ : ℝ, ρ ≤ η → ν (Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
  atlas_forward_decl GlobalTheory.measure_ball_eq_lintegral_upperDens
end

section
section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory

theorem squeeze_continuousAt_zero (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ)
    (f : V → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η →
      ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) :
    f 0 = c ∧ ContinuousAt f 0 := by
  have h1 : Tendsto (fun ε : ℝ => (1 + ε)⁻¹ ^ d) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => (1 + ε)⁻¹ ^ d) 0 :=
      ((continuous_const.add continuous_id).continuousAt.inv₀ (by norm_num)).pow d
    simpa using this.tendsto
  have h2 : Tendsto (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ d) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ d) 0 :=
      ((continuous_const.add continuous_id).continuousAt.div
        (continuous_const.sub continuous_id).continuousAt (by norm_num)).pow d
    simpa using this.tendsto
  have hL : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c) (𝓝 0) (𝓝 c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hc)
    simpa using this
  have hU : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) (𝓝 0) (𝓝 c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h2) (Or.inr hc)
    simpa using this
  have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  have hf : Tendsto f (𝓝 0) (𝓝 c) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c :=
        nhdsWithin_le_nhds (hL.eventually (lt_mem_nhds ha))
      obtain ⟨ε, hε, hεI⟩ := (e1.and hI).exists
      obtain ⟨η, hη, hx⟩ := h ε hεI.1 hεI.2
      filter_upwards [Metric.ball_mem_nhds (0 : V) hη] with x hxb
      rw [mem_ball_zero_iff] at hxb
      exact lt_of_lt_of_le hε (hx x hxb).1
    · intro a ha
      have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c < a :=
        nhdsWithin_le_nhds (hU.eventually (gt_mem_nhds ha))
      obtain ⟨ε, hε, hεI⟩ := (e1.and hI).exists
      obtain ⟨η, hη, hx⟩ := h ε hεI.1 hεI.2
      filter_upwards [Metric.ball_mem_nhds (0 : V) hη] with x hxb
      rw [mem_ball_zero_iff] at hxb
      exact lt_of_le_of_lt (hx x hxb).2 hε
  have h0 : f 0 = c := tendsto_nhds_unique (tendsto_pure_nhds f 0) (hf.mono_left (pure_le_nhds 0))
  refine ⟨h0, ?_⟩
  unfold ContinuousAt
  rw [h0]
  exact hf

example : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (f : V → ℝ≥0∞) (c : ℝ≥0∞), c ≠ ⊤ → (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) → f 0 = c ∧ ContinuousAt f 0 :=
  squeeze_continuousAt_zero

end GlobalTheory
end

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (f : V → ℝ≥0∞) (c : ℝ≥0∞), c ≠ ⊤ → (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) → f 0 = c ∧ ContinuousAt f 0 := by
  atlas_forward_decl GlobalTheory.squeeze_continuousAt_zero
end

section
section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.HaarDensChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU

variable {k r : ℕ}

instance : T2Space (Gp k r) := inferInstanceAs (T2Space {x : Mt k r // x ∈ amb k r})

instance : LocallyCompactSpace (Gp k r) :=
  (amb_closed (k := k) (r := r)).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem isMatGroup_uwb : PI.IsMatGroup (UWb k r) :=
  ⟨amb_closed, uwb_one, fun _ ha _ hb => uwb_mul ha hb, fun a ha => ⟨uwb_inv ha, Matrix.mul_nonsing_inv _ (uwb_unit ha)⟩⟩

theorem exists_haarOn (k r : ℕ) : ∃ νh : Measure (Mt k r), IsHaarOn (UWb k r) νh := by
  let μ : Measure (Gp k r) := Measure.haar
  refine ⟨μ.map inc, inc_memb.sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · intro h
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) h
    simp only [inc_memb.map_apply, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
    exact (IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' this
  · rw [inc_memb.map_apply]
    have : (inc : Gp k r → Mt k r) ⁻¹' {x | Matrix.of x ∉ UWb k r} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact inc_mem x
    rw [this, measure_empty]
  · let a : Gp k r := ⟨s, hs⟩
    rw [Measure.map_map (lmulM_cont s).measurable inc_memb.measurable]
    have : lmulM s ∘ (inc : Gp k r → Mt k r) = inc ∘ fun x => a * x := by
      funext x; rfl
    rw [this, ← Measure.map_map inc_memb.measurable (measurable_const_mul a), map_mul_left_eq_self]

end GlobalTheory.HaarDensChart

namespace GlobalTheory.HaarDensChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU GlobalTheory.MatHaarDensity

theorem haarDens : HaarDens := by
  intro k r hk
  obtain ⟨νh, hνh⟩ := exists_haarOn k r
  have hS : PI.IsMatGroup (UWb k r) := isMatGroup_uwb
  have hμ : PI.IsHaarOnM (UWb k r) νh := hνh
  obtain ⟨hlie, hsurj⟩ := GlobalTheory.T.closed_matrix_subgroup_theorem _ (UWb k r) hS
  obtain ⟨-, hcpt, hop⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ (UWb k r) νh hS hμ
  have hmem : ∀ X, expL (UWb k r) X ∈ UWb k r := fun X => by simpa [expL] using hlie X 1
  have hsurj' : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ UWb k r, (∀ i j, ‖(g - 1) i j‖ < δ) →
      ∃ X : lieE (UWb k r), ‖X‖ < ρ ∧ expL (UWb k r) X = g := by
    intro ρ hρ
    obtain ⟨δ, hδ, h⟩ := hsurj ρ hρ
    refine ⟨δ, hδ, fun g hg hg' => ?_⟩
    obtain ⟨X, hX, e⟩ := h g hg hg'
    exact ⟨X, mem_ball_zero_iff.1 hX, e⟩
  obtain ⟨δ₀, hδ₀, hi⟩ := exists_injOn (UWb k r)
  let φ : lieE (UWb k r) → Mt k r := expC k r
  have hc : Continuous φ := continuous_expL (UWb k r)
  have hi' : Set.InjOn φ (Metric.ball 0 δ₀) := fun X hX Y hY h => hi hX hY h
  have hψ : MeasurableEmbedding ((Metric.ball (0 : lieE (UWb k r)) δ₀).restrict φ) :=
    hc.continuousOn.measurableEmbedding Metric.isOpen_ball.measurableSet hi'
  let ν : Measure (lieE (UWb k r)) := (νh.comap ((Metric.ball (0 : lieE (UWb k r)) δ₀).restrict φ)).map Subtype.val
  have hν : ∀ A : Set (lieE (UWb k r)), MeasurableSet A → ν A = νh (φ '' (A ∩ Metric.ball 0 δ₀)) := by
    intro A hA
    simp only [ν]
    rw [Measure.map_apply measurable_subtype_coe hA, hψ.comap_apply]
    congr 1
    rw [Set.inter_comm, ← Subtype.image_preimage_coe, Set.image_image]
    rfl
  have hνb : ∀ (x : lieE (UWb k r)) (ρ : ℝ), ‖x‖ + ρ ≤ δ₀ → ν (Metric.ball x ρ) = νh (φ '' Metric.ball x ρ) := by
    intro x ρ h
    rw [hν _ Metric.isOpen_ball.measurableSet, Set.inter_eq_left.2]
    exact Metric.ball_subset_ball' (by simpa [add_comm] using h)
  have hfin : νh (φ '' Metric.ball 0 δ₀) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.image_mono Metric.ball_subset_closedBall))
      (hcpt _ ((isCompact_closedBall (0 : lieE (UWb k r)) δ₀).image hc) (by
        rintro _ ⟨X, -, rfl⟩
        exact hmem X))
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν _ MeasurableSet.univ, Set.univ_inter]
    exact hfin⟩
  have hposh : ∀ ρ : ℝ, 0 < ρ → νh (φ '' Metric.ball 0 ρ) ≠ 0 := by
    intro ρ hr h
    obtain ⟨η, hη, H⟩ := hsurj ρ hr
    have hp := hop {g | ∀ i j, ‖(Matrix.of g - 1) i j‖ < η} (isOpen_near_one η)
      ⟨Matrix.of.symm 1, by intro i j; simpa using hη, hS.2.1⟩
    refine hp.ne' (measure_mono_null (fun g hg => ?_) (measure_union_null h hνh.2.2.1))
    by_cases hgS : Matrix.of g ∈ UWb k r
    · exact Or.inl (H _ hgS hg)
    · exact Or.inr hgS
  have hpos : ∀ ρ : ℝ, 0 < ρ → ν (Metric.ball 0 ρ) ≠ 0 := by
    intro ρ hr
    rw [hν _ Metric.isOpen_ball.measurableSet]
    intro h
    refine hposh (min ρ δ₀) (lt_min hr hδ₀) (measure_mono_null (Set.image_mono ?_) h)
    exact Set.subset_inter (Metric.ball_subset_ball (min_le_left _ _)) (Metric.ball_subset_ball (min_le_right _ _))
  have hsν : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : lieE (UWb k r), ‖x‖ < η →
      ∀ᶠ ρ in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * ρ)) ≤ ν (Metric.ball 0 ρ) ∧
        ν (Metric.ball 0 ρ) ≤ ν (Metric.ball x ((1 + ε) * ρ)) := by
    intro ε h0 h1
    obtain ⟨η, hη, H⟩ := sandwich (UWb k r) hS hmem hsurj' ε h0 h1
    refine ⟨min η (δ₀ / 2), lt_min hη (by linarith), fun x hx => ?_⟩
    have hx1 : ‖x‖ < η := hx.trans_le (min_le_left _ _)
    have hx2 : ‖x‖ < δ₀ / 2 := hx.trans_le (min_le_right _ _)
    obtain ⟨hiS, hi1⟩ := hS.2.2.2 _ (hmem x)
    have hi2 : (expL (UWb k r) x)⁻¹ * expL (UWb k r) x = 1 := mul_eq_one_comm.1 hi1
    have hτ : Continuous (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) := lmulM_cont _
    have hτμ : νh.map (lmulM (expL (UWb k r) x)⁻¹) = νh := hνh.2.2.2 _ hiS
    filter_upwards [H x hx1, Ioo_mem_nhdsGT (show (0:ℝ) < δ₀ / 4 by linarith)] with ρ hr hr'
    obtain ⟨hr0, hr1⟩ := hr'
    have hm : MeasurableSet (φ '' Metric.ball 0 ρ) :=
      Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hc.continuousOn
        (hi'.mono (Metric.ball_subset_ball (by linarith)))
    have hinv : νh (φ '' Metric.ball 0 ρ) =
        νh ((lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ)) := by
      rw [← Measure.map_apply hτ.measurable hm, hτμ]
    have hA : φ '' Metric.ball x ((1 - ε) * ρ) ⊆
        (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ) := by
      rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨Z, hZ, e⟩ := hr.1 Y (mem_ball_iff_norm.1 hY)
      refine ⟨Z, mem_ball_zero_iff.2 hZ, ?_⟩
      change expL (UWb k r) Z = (expL (UWb k r) x)⁻¹ * expL (UWb k r) Y
      rw [e, ← Matrix.mul_assoc, hi2, Matrix.one_mul]
    have hB : (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ) ⊆
        φ '' Metric.ball x ((1 + ε) * ρ) := by
      rintro g ⟨Z, hZ, e⟩
      obtain ⟨Y, hY, e'⟩ := hr.2 Z (mem_ball_zero_iff.1 hZ)
      refine ⟨Y, mem_ball_iff_norm.2 hY, ?_⟩
      change expL (UWb k r) Z = (expL (UWb k r) x)⁻¹ * Matrix.of g at e
      change expL (UWb k r) Y = Matrix.of g
      rw [e', e, ← Matrix.mul_assoc, hi1, Matrix.one_mul]
    rw [hνb x _ (by nlinarith), hνb x _ (by nlinarith), hνb 0 ρ (by simp; linarith), hinv]
    exact ⟨measure_mono hA, measure_mono hB⟩
  obtain ⟨c, hc0, hct, hlim⟩ :=
    GlobalTheory.exists_density_origin_of_almost_homogeneous (lieE (UWb k r)) volume ν hpos hsν
  have hb : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : lieE (UWb k r), ‖x‖ < η →
      ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ (lieE (UWb k r))) * c ≤ upperDens volume ν x ∧
        upperDens volume ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ (lieE (UWb k r))) * c := by
    intro ε h0 h1
    obtain ⟨η, hη, H⟩ := hsν ε h0 h1
    exact ⟨η, hη, GlobalTheory.T.upperDensity_bounds_almost_homogeneous_measure _ volume ν c hct hlim ε η h0 h1 H⟩
  obtain ⟨hδ0, hδc⟩ := GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds _ _ (upperDens volume ν) c hct hb
  obtain ⟨η₀, hη₀, H₀⟩ := hb (1 / 2) (by norm_num) (by norm_num)
  set a := ENNReal.ofReal (((1 + 1 / 2) / (1 - 1 / 2)) ^ Module.finrank ℝ (lieE (UWb k r)) : ℝ) * c with ha
  have hne : a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct
  have hC : ∀ x : lieE (UWb k r), ‖x‖ < η₀ → upperDens volume ν x < ((a.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) := by
    intro x hx
    refine lt_of_le_of_lt (H₀ x hx).2 ?_
    have h := ENNReal.coe_lt_coe.2 (lt_add_one a.toNNReal)
    rwa [ENNReal.coe_toNNReal hne] at h
  refine ⟨νh, hνh, upperDens volume ν, hδc, by rw [hδ0]; exact hc0, by rw [hδ0]; exact hct,
    min η₀ δ₀, lt_min hη₀ hδ₀, fun ρ hρ hρε => ?_⟩
  have e1 : νh (bBall k r ρ) = ν (Metric.ball 0 ρ) := by
    rw [hν _ Metric.isOpen_ball.measurableSet,
      Set.inter_eq_left.2 (Metric.ball_subset_ball (hρε.le.trans (min_le_right _ _)))]
    rfl
  rw [e1]
  exact GlobalTheory.T.measure_ball_eq_lintegral_upperMeasureDensity _ volume ν η₀ _ hC ρ (hρε.le.trans (min_le_left _ _))

end GlobalTheory.HaarDensChart
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_unitaryGroupWb_density_chart : PI.RhsWLim.W.HaarDens := by
  atlas_forward_decl GlobalTheory.HaarDensChart.haarDens
end

section
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.HyperboloidPolar

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

theorem opVec_inWb (p : (Fin k → ℂ) × ℂ) : inWb k r (opVec k r p) := by
  intro i hi
  unfold opVec
  rw [dif_neg (by omega), if_neg (by omega)]

theorem wbPart_opVec (p : (Fin k → ℂ) × ℂ) : wbPart k r (opVec k r p) = toW k p := by
  funext m
  have := m.isLt
  unfold wbPart opVec toW wI
  by_cases h : m.val < k
  · rw [dif_pos (by simp only; omega), dif_pos h]
    exact congrArg p.1 (Fin.ext (by simp))
  · rw [dif_neg (by simp only; omega), dif_neg h, if_pos (by simp only; omega)]

theorem opCo_eq (v : Fin (2 * r + k + 1) → ℂ) : opCo k r v = ofW k (wbPart k r v) := rfl

theorem opCo_opVec (p : (Fin k → ℂ) × ℂ) : opCo k r (opVec k r p) = p := by
  rw [opCo_eq, wbPart_opVec, ofW_toW]

theorem eq_of_wbPart {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w)
    (h : wbPart k r v = wbPart k r w) : v = w := by
  funext i
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hv i hi, hw i hi]
  · have hm : MB.mid k r i := by constructor <;> omega
    have := congrFun h (MB.midx hm)
    simpa only [wbPart, MB.wI_midx] using this

theorem opVec_opCo {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : opVec k r (opCo k r v) = v :=
  eq_of_wbPart (opVec_inWb _) hv (by rw [wbPart_opVec, opCo_eq, toW_ofW])

theorem inWb_uwb {s : Mat k r} (hs : s ∈ UWb k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (s *ᵥ v) := by
  rw [op_uwb_eq_emb hs]
  exact RI.inWb_emb _ hv

theorem continuous_opVec : Continuous (opVec k r) := by
  refine continuous_pi fun i => ?_
  unfold opVec
  by_cases h : r ≤ i.val ∧ i.val < r + k
  · simp only [dif_pos h]
    exact (continuous_apply _).comp continuous_fst
  · simp only [dif_neg h]
    by_cases h' : i.val = r + k
    · simp only [if_pos h']
      exact continuous_snd
    · simp only [if_neg h']
      exact continuous_const

theorem continuous_opCo : Continuous (opCo k r) :=
  (continuous_pi fun i => continuous_apply (wI k r (Fin.castSucc i))).prodMk
    (continuous_apply (wI k r (Fin.last k)))

theorem herm_opVec (p : (Fin k → ℂ) × ℂ) :
    herm (Hpk k r) (opVec k r p) (opVec k r p) = (qf k p : ℂ) := by
  rw [herm_wb _ _ (opVec_inWb p), wbPart_opVec, qf_eq]
  rfl

theorem herm_self_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    herm (Hpk k r) z z = ((-Tz k r z : ℝ) : ℂ) := by
  unfold Tz
  rw [neg_neg, herm_wb _ _ hz, hermHb_self, Complex.ofReal_re]

def hypAmb (k r : ℕ) (T' : ℝ) : Measure (Fin (2 * r + k + 1) → ℂ) := (hypM k T').map (opVec k r)

theorem hypAmb_sigmaFinite {T' : ℝ} (hT' : 0 < T') : SigmaFinite (hypAmb k r T') := by
  have : IsFiniteMeasureOnCompacts (hypAmb k r T') := by
    refine ⟨fun C hC => ?_⟩
    rw [hypAmb, Measure.map_apply continuous_opVec.measurable hC.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) ((hypLF k T' hT').2 _ (hC.image continuous_opCo))
    intro p hp
    exact ⟨_, hp, opCo_opVec p⟩
  infer_instance

theorem hypAmb_inv (hk : 1 ≤ k) {T' : ℝ} (hT' : 0 < T') {s : Mat k r} (hs : s ∈ UWb k r) :
    (hypAmb k r T').map (fun v => s *ᵥ v) = hypAmb k r T' := by
  have hI := hypInv_of lebInvB (coneForm_of hypTh coneVol) k r T' hk hT' s hs
  have hm : Continuous (fun v : Fin (2 * r + k + 1) → ℂ => s *ᵥ v) :=
    continuous_const.matrix_mulVec continuous_id
  have hA : Continuous (opAct k r s) := continuous_opCo.comp (hm.comp continuous_opVec)
  have e : (fun v => s *ᵥ v) ∘ opVec k r = opVec k r ∘ opAct k r s := by
    funext p
    exact (opVec_opCo (inWb_uwb hs (opVec_inWb p))).symm
  rw [hypAmb, Measure.map_map hm.measurable continuous_opVec.measurable, e,
    ← Measure.map_map continuous_opVec.measurable hA.measurable, hI]

theorem hypAmb_conc {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    hypAmb k r (Tz k r z') {v | ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} = 0 := by
  have hc : IsClosed {v : Fin (2 * r + k + 1) → ℂ |
      inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z'} := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : {v : Fin (2 * r + k + 1) → ℂ | inWb k r v} =
          ⋂ i : Fin (2 * r + k + 1), ⋂ _ : (i.val < r ∨ r + k < i.val), {v | v i = 0} := by
        ext v
        simp only [inWb, Set.mem_iInter]
        rfl
      show IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v}
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
    · unfold herm
      exact continuous_id.star.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hm : MeasurableSet {v : Fin (2 * r + k + 1) → ℂ |
      ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} := hc.measurableSet.compl
  rw [hypAmb, Measure.map_apply continuous_opVec.measurable hm]
  refine measure_mono_null ?_ (hypLF k _ hT').1
  intro p hp hS
  apply hp
  refine ⟨opVec_inWb p, ?_⟩
  rw [herm_opVec, herm_self_eq hz', (hypS_iff _ p).1 hS]

theorem hypAmb_polar (hk : 1 ≤ k) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {T' : ℝ} (hT' : 0 < T') (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T' =
      ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * Tz k r z ^ k)) *
        ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) T' ζ) * g ζ := by
  obtain ⟨p, hp, hpz⟩ := transW k r z hz hT
  set s := Real.sqrt (Tz k r z) with hs
  have hs0 : (s : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hT).ne'
  set zs := ((s : ℂ) • wLast k r) with hzs
  have hgm : Measurable fun v => g (herm (Hpk k r) v zs) := hg.comp (RI.cont_herm zs).measurable
  have hm : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => p⁻¹ *ᵥ v) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have step1 : ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T' = ∫⁻ v, g (herm (Hpk k r) v zs) ∂hypAmb k r T' := by
    calc ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T'
        = ∫⁻ v, (fun y => g (herm (Hpk k r) y zs)) (p⁻¹ *ᵥ v) ∂hypAmb k r T' := by
          refine lintegral_congr fun v => ?_
          rw [← hpz, herm_mulVec_right hp.1]
      _ = ∫⁻ y, g (herm (Hpk k r) y zs) ∂((hypAmb k r T').map (fun v => p⁻¹ *ᵥ v)) :=
          (lintegral_map hgm hm).symm
      _ = _ := by rw [hypAmb_inv hk hT' (HU.uwb_inv hp)]
  set f : (Fin k → ℂ) × ℂ → ℝ≥0∞ := fun v => g (-((s : ℂ) * v.2)) with hf
  have hfm : Measurable f := hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step2 : ∫⁻ v, g (herm (Hpk k r) v zs) ∂hypAmb k r T' = hypMeas k T' f := by
    rw [hypMeas_eq k T' hfm, hypAmb, lintegral_map hgm continuous_opVec.measurable]
    refine lintegral_congr fun q => ?_
    have e : opVec k r q (wI k r (Fin.last k)) = q.2 := congrArg Prod.snd (opCo_opVec (r := r) q)
    rw [hzs, herm_wLast, e]
  set G : ℝ → ℂ → ℝ≥0∞ := fun _ c => g (-((s : ℂ) * c)) with hGdef
  have hGm : Measurable (Function.uncurry G) :=
    hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step3 := polarHyp k (Tz k r z) T' hk hT hT' G hGm
  rw [← hs] at step3
  have hcancel : ∀ ζ : ℂ, -((s : ℂ) * -(ζ / (s : ℂ))) = ζ := by
    intro ζ; field_simp
  have e3 : hypMeas k T' f =
      hypMeas k T' (fun v => G ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) := rfl
  rw [step1, step2, e3, step3]
  simp only [hGdef, hcancel]

theorem hypQ : RI.HypQ := by
  intro k r z z' hk hz hz' hT hT'
  refine ⟨hypAmb k r (Tz k r z'), hypAmb_sigmaFinite hT', fun s hs => hypAmb_inv hk hT' hs,
    hypAmb_conc hz' hT', ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * Tz k r z ^ k)),
    ?_, ENNReal.ofReal_ne_top, fun g hg => hypAmb_polar hk hz hT hT' g hg⟩
  have := Real.pi_pos
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

end GlobalTheory.HyperboloidPolar
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_polar_form : PI.RhsWLim.W.RI.HypQ := by
  atlas_forward_decl GlobalTheory.HyperboloidPolar.hypQ
end

section
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace GlobalTheory.HypChartPf

open PI.RhsWLim PI.RhsWLim.W

private lemma ofLp_qFw_kapT (k : ℕ) (v : (Fin k → ℂ) × ℂ) :
    WithLp.ofLp (qFw k (kapT k v)) = (WithLp.toLp 2 v.1, Complex.arg v.2) := by
  ext a
  · simp [qFw, kapT, Complex.re_add_im]
  · simp [qFw, kapT]

private lemma hypPar_toLp_arg_of_mem_hypS (k : ℕ) (T' : ℝ) (v : (Fin k → ℂ) × ℂ) (hv : v ∈ hypS k T') :
    hypPar k T' (WithLp.toLp 2 v.1, Complex.arg v.2) = v := by
  simp only [hypS, Set.mem_ofPred_eq] at hv
  have hn : ‖(WithLp.toLp 2 v.1 : EuclideanSpace ℂ (Fin k))‖ ^ 2 + T' = ‖v.2‖ ^ 2 := by
    rw [← normSq_sum_eq, ← Complex.normSq_eq_norm_sq]
    simp only []
    linarith
  simp only [hypPar, hn, Real.sqrt_sq (norm_nonneg _), Complex.norm_mul_exp_arg_mul_I, ]

private lemma kapT_hypPar_ofLp_qFw (k : ℕ) (T' : ℝ) (hT' : 0 < T') (x : TrE k)
    (hx : (WithLp.ofLp (qFw k x)).2 ∈ Set.Ioc (-Real.pi) Real.pi) :
    kapT k (hypPar k T' (WithLp.ofLp (qFw k x))) = x := by
  ext o
  rcases o with _ | ⟨a, b⟩
  · simp only [kapT, hypPar]
    simp only [qFw] at hx ⊢
    simp only [WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
    rw [Complex.arg_real_mul _ (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hT')),
      Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I hx]
  · cases b <;> simp [kapT, hypPar, qFw]

theorem restrict_periodic (A : Set ℝ) (hA : MeasurableSet A) (hp : ∀ x, x + 2 * Real.pi ∈ A ↔ x ∈ A) :
    volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) A = volume.restrict (Set.Ioc (-Real.pi) Real.pi) A := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 := isAddFundamentalDomain_Ioc hpos 0 (volume : Measure ℝ)
  have h2 := isAddFundamentalDomain_Ioc hpos (-Real.pi) (volume : Measure ℝ)
  rw [zero_add] at h1
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h2
  have key : ∀ n : ℤ, ∀ x, n • (2 * Real.pi) + x ∈ A ↔ x ∈ A := by
    intro n
    induction n using Int.induction_on with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [← ih x, ← hp ((m : ℤ) • (2 * Real.pi) + x)]
      rw [show ((m : ℤ) + 1) • (2 * Real.pi) + x = (m : ℤ) • (2 * Real.pi) + x + 2 * Real.pi by
        rw [add_smul, one_smul]; abel]
    | pred m ih =>
      intro x
      have h := hp ((-(m : ℤ) - 1) • (2 * Real.pi) + x)
      rw [show (-(m : ℤ) - 1) • (2 * Real.pi) + x + 2 * Real.pi = (-(m : ℤ)) • (2 * Real.pi) + x by
        rw [sub_smul, one_smul]; abel, ih x] at h
      exact h.symm
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  refine h1.measure_set_eq h2 hA ?_
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
  ext x
  exact key n x

theorem hypM_eq (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E) :
    hypM k T' E = (1 / 2) * (volume.prod volume)
      (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) := by
  have hmeas : Measurable (hypPar k T') := (continuous_hypPar k T').measurable
  have hP : MeasurableSet (hypPar k T' ⁻¹' E) := hmeas hE
  unfold hypM
  rw [Measure.smul_apply, Measure.map_apply hmeas hE, smul_eq_mul]
  congr 1
  rw [Measure.prod_apply hP, Measure.prod_apply (hP.inter (MeasurableSet.univ.prod measurableSet_Ioc))]
  refine lintegral_congr (fun y => ?_)
  have hs : MeasurableSet (Prod.mk y ⁻¹' (hypPar k T' ⁻¹' E)) := measurable_prodMk_left hP
  rw [restrict_periodic _ hs ?_, Measure.restrict_apply hs]
  · congr 1
    ext θ
    simp
  · intro x
    have e : hypPar k T' (y, x + 2 * Real.pi) = hypPar k T' (y, x) := by
      simp only [hypPar, Prod.mk.injEq, true_and]
      rw [show ((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I = (x : ℂ) * Complex.I + 2 * Real.pi * Complex.I by
        push_cast; ring, Complex.exp_periodic]
    simp only [Set.mem_preimage]
    rw [e]

theorem hypM_eq_kapT (k : ℕ) (T' : ℝ) (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E)
    (hS : E ⊆ hypS k T') : hypM k T' E = (1 / 2) * volume (kapT k '' E) := by
  rw [hypM_eq k T' E hE]
  congr 1
  have hFm : MeasurableSet (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) :=
    ((continuous_hypPar k T').measurable hE).inter (MeasurableSet.univ.prod measurableSet_Ioc)
  have hset : kapT k '' E =
      (fun x : TrE k => WithLp.ofLp (qFw k x)) ⁻¹' (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [ofLp_qFw_kapT k v, hypPar_toLp_arg_of_mem_hypS k T' v (hS hv)]
      exact ⟨hv, Complex.arg_mem_Ioc _⟩
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, kapT_hypPar_ofLp_qFw k T' hT' x h2⟩
  rw [hset, (qIso_measurePreserving k).measure_preimage hFm.nullMeasurableSet]

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ i.val ∧ i.val < r + k then 1 else if i.val = r + k then -1 else 0

theorem gen_semiconj (k r : ℕ) (q : TrE k) :
    SemiconjBy (Matrix.diagonal (sgn k r)) (-opGen k r q) (opGen k r q)ᴴ := by
  show _ = _
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]
  unfold opGen sgn
  split_ifs <;> (try (exfalso; omega)) <;> simp

private lemma exp_conjTranspose_mul_mul_exp_of_skew {n : Type*} [Fintype n] [DecidableEq n] (U X : Matrix n n ℂ)
    (hU : IsUnit U) (h : U * -X = Xᴴ * U) : (NormedSpace.exp X)ᴴ * U * NormedSpace.exp X = U := by
  have hdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have h1 : Xᴴ = U * -X * U⁻¹ := by rw [h, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  have h3 : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hU]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hdet, h3, Matrix.mul_one]

private lemma exp_opGen_conjTranspose_mul_diagonal_mul (k r : ℕ) (q : TrE k) (u : ℂ) (hu : u ≠ 0) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (fun i => if sgn k r i = 0 then u else sgn k r i) *
      NormedSpace.exp (opGen k r q) = Matrix.diagonal (fun i => if sgn k r i = 0 then u else sgn k r i) := by
  have hsemi := gen_semiconj k r q
  unfold SemiconjBy at hsemi
  have hent : ∀ i j, sgn k r i * -opGen k r q i j = star (opGen k r q j i) * sgn k r j := by
    intro i j
    have := congrFun (congrFun hsemi i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply] at this
  have hz : ∀ i j, sgn k r i = 0 → opGen k r q i j = 0 ∧ opGen k r q j i = 0 := by
    intro i j hi
    unfold sgn at hi
    split_ifs at hi with h1 h2
    · norm_num at hi
    · norm_num at hi
    · unfold opGen
      constructor <;> split_ifs <;> rfl
  apply exp_conjTranspose_mul_mul_exp_of_skew
  · refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
    rw [Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    split_ifs with h
    · exact hu
    · exact h
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]
    by_cases hi : sgn k r i = 0
    · obtain ⟨h1, h2⟩ := hz i j hi
      simp [h1, h2]
    by_cases hj : sgn k r j = 0
    · obtain ⟨h1, h2⟩ := hz j i hj
      simp [h1, h2]
    simp only [if_neg hi, if_neg hj]
    exact hent i j

theorem exp_form (k r : ℕ) (q : TrE k) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (sgn k r) * NormedSpace.exp (opGen k r q) =
      Matrix.diagonal (sgn k r) := by
  have hD : Matrix.diagonal (sgn k r) = (1 / 2 : ℂ) •
      (Matrix.diagonal (fun i => if sgn k r i = 0 then 1 else sgn k r i) +
        Matrix.diagonal (fun i => if sgn k r i = 0 then -1 else sgn k r i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      split_ifs with h <;> [rw [h]; skip] <;> ring
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [hD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    exp_opGen_conjTranspose_mul_diagonal_mul k r q 1 one_ne_zero, exp_opGen_conjTranspose_mul_diagonal_mul k r q (-1) (neg_ne_zero.2 one_ne_zero)]

private lemma wI_injective' (k r : ℕ) : Function.Injective (wI k r) := by
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [wI] at this
  omega

theorem form_eq (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) :
    star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) =
      ((∑ i, Complex.normSq ((opCo k r v).1 i) - Complex.normSq (opCo k r v).2 : ℝ) : ℂ) := by
  have hs : star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) =
      ∑ j : Fin (k + 1), star (v (wI k r j)) * (sgn k r (wI k r j) * v (wI k r j)) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    symm
    refine Fintype.sum_of_injective _ (wI_injective' k r) _ (fun i => star (v i) * (sgn k r i * v i)) ?_ (fun _ => rfl)
    intro i hi
    have : sgn k r i = 0 := by
      unfold sgn
      rw [if_neg, if_neg]
      · intro h; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩
      · rintro ⟨h1, h2⟩; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩
    simp [this]
  have h1 : ∀ j : Fin k, sgn k r (wI k r j.castSucc) = 1 := by
    intro j; unfold sgn; rw [if_pos]; simp [wI]
  have h2 : sgn k r (wI k r (Fin.last k)) = -1 := by
    unfold sgn; rw [if_neg, if_pos] <;> simp [wI]
  rw [hs, Fin.sum_univ_castSucc, h2]
  simp only [h1, opCo]
  push_cast
  simp [Complex.normSq_eq_conj_mul_self, sub_eq_add_neg]

theorem opE_subset (k r : ℕ) (T' : ℝ) (hT' : 0 < T') (ρ : ℝ) : opE k r T' ρ ⊆ hypS k T' := by
  rintro p ⟨q, -, rfl⟩
  have hq : star (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T') ⬝ᵥ
      (Matrix.diagonal (sgn k r) *ᵥ (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) =
      star (opBase k r T') ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ opBase k r T') := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, exp_form]
  rw [form_eq, form_eq] at hq
  have hb : ∀ i : Fin k, opBase k r T' (wI k r i.castSucc) = 0 := by
    intro i
    have hne : wI k r i.castSucc ≠ wI k r (Fin.last k) := fun h => (Fin.castSucc_lt_last i).ne (wI_injective' k r h)
    simp [opBase, wLast, bvec, hne]
  have hl : opBase k r T' (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ) := by
    simp [opBase, wLast, bvec]
  simp only [opCo, hb, hl, map_zero, Finset.sum_const_zero, Complex.normSq_ofReal,
    Real.mul_self_sqrt hT'.le] at hq
  simp only [hypS, Set.mem_ofPred_eq, opCo]
  linarith [Complex.ofReal_injective hq]

theorem hypChart : HypChart := by
  unfold HypChart
  intro k r T' hk hT'
  refine ⟨1, one_pos, fun ρ _ _ => ?_⟩
  have himg : phiT k r T' '' Metric.ball 0 ρ = kapT k '' opE k r T' ρ := by
    rw [opE, Set.image_image]; rfl
  rw [himg, hypM_eq_kapT k T' hT' _ (opEMeas k r T' ρ) (opE_subset k r T' hT' ρ)]

end GlobalTheory.HypChartPf
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_chart_measure_formula : PI.RhsWLim.W.HypChart := by
  atlas_forward_decl GlobalTheory.HypChartPf.hypChart
end

section
section
noncomputable section

namespace GlobalTheory.GaugeKExists

theorem gaugeK : PI.RhsWLim.W.GaugeK := by
  intro k r _
  exact ⟨Formalism.L2.SG.Pf.GV.nu0 k r, Formalism.L2.SG.Pf.GV.gauge_measure_is_gauge⟩

end GlobalTheory.GaugeKExists
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure : PI.RhsWLim.W.GaugeK := by
  atlas_forward_decl GlobalTheory.GaugeKExists.gaugeK
end

section
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace GlobalTheory.HypOrbitUnique

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU PI.RhsWLim.W.MB

theorem fubini_identity {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    [MeasurableSpace X] (act : G → X → X) (hm : Measurable (Function.uncurry act))
    (hmul : ∀ g g' x, act (g * g') x = act g (act g' x)) (hone : ∀ x, act 1 x = x)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Q : Measure X) [SFinite Q] (hQ : ∀ g, Q.map (act g) = Q) (x₀ : X)
    (htr : ∀ᵐ x ∂Q, ∃ g, act g x₀ = x) {f h : X → ℝ≥0∞} (hf : Measurable f) (hh : Measurable h) :
    (∫⁻ g, f (act g x₀) ∂μ) * ∫⁻ x, h x ∂Q = (∫⁻ x, f x ∂Q) * ∫⁻ g, h (act g⁻¹ x₀) ∂μ := by
  have hmg : ∀ g, Measurable (act g) := fun g => hm.comp measurable_prodMk_left
  have hm1 : Measurable fun p : X × G => act p.2 p.1 := hm.comp measurable_swap
  have hm2 : Measurable fun p : G × X => act p.1⁻¹ p.2 :=
    hm.comp (measurable_fst.inv.prodMk measurable_snd)
  calc (∫⁻ g, f (act g x₀) ∂μ) * ∫⁻ x, h x ∂Q
      = ∫⁻ x, (∫⁻ g, f (act g x₀) ∂μ) * h x ∂Q := (lintegral_const_mul _ hh).symm
    _ = ∫⁻ x, ∫⁻ g, f (act g x) * h x ∂μ ∂Q := by
        refine lintegral_congr_ae (htr.mono ?_)
        rintro x ⟨p, rfl⟩
        have hmx : Measurable fun g => f (act g (act p x₀)) := hf.comp (hm.comp measurable_prodMk_right)
        simp only
        rw [lintegral_mul_const _ hmx]
        congr 1
        simp_rw [← hmul]
        exact (lintegral_mul_right_eq_self (fun g => f (act g x₀)) p).symm
    _ = ∫⁻ g, ∫⁻ x, f (act g x) * h x ∂Q ∂μ :=
        lintegral_lintegral_swap ((hf.comp hm1).mul (hh.comp measurable_fst)).aemeasurable
    _ = ∫⁻ g, ∫⁻ x, f x * h (act g⁻¹ x) ∂Q ∂μ := by
        refine lintegral_congr fun g => ?_
        conv_rhs => rw [← hQ g]
        rw [lintegral_map (f := fun x => f x * h (act g⁻¹ x)) (hf.mul (hh.comp (hmg g⁻¹))) (hmg g)]
        refine lintegral_congr fun x => ?_
        rw [← hmul, inv_mul_cancel, hone]
    _ = ∫⁻ x, ∫⁻ g, f x * h (act g⁻¹ x) ∂μ ∂Q :=
        lintegral_lintegral_swap ((hf.comp measurable_snd).mul (hh.comp hm2)).aemeasurable
    _ = ∫⁻ x, f x * ∫⁻ g, h (act g⁻¹ x₀) ∂μ ∂Q := by
        refine lintegral_congr_ae (htr.mono ?_)
        rintro x ⟨p, rfl⟩
        have hmx : Measurable fun g : G => h (act g⁻¹ (act p x₀)) :=
          hh.comp (hm2.comp measurable_prodMk_right)
        simp only
        rw [lintegral_const_mul _ hmx]
        congr 1
        rw [← lintegral_mul_left_eq_self (fun g : G => h (act g⁻¹ x₀)) p⁻¹]
        refine lintegral_congr fun g => ?_
        rw [← hmul, _root_.mul_inv_rev, inv_inv]
    _ = _ := lintegral_mul_const _ hf

variable {k r : ℕ}

def act (g : Gp k r) (p : (Fin k → ℂ) × ℂ) : (Fin k → ℂ) × ℂ := opAct k r (Matrix.of (inc g)) p

theorem opVec_wI (p : (Fin k → ℂ) × ℂ) (m : Fin (k + 1)) : opVec k r p (wI k r m) = toW k p m := by
  have := m.isLt
  unfold opVec toW wI
  by_cases h : m.val < k
  · rw [dif_pos (by simp only; omega), dif_pos h]
    exact congrArg p.1 (Fin.ext (by simp))
  · rw [dif_neg (by simp only; omega), dif_neg h, if_pos (by simp only; omega)]

theorem opVec_inWb (p : (Fin k → ℂ) × ℂ) : inWb k r (opVec k r p) := by
  intro i hi
  unfold opVec
  rw [dif_neg (by omega), if_neg (by omega)]

theorem opCo_opVec (p : (Fin k → ℂ) × ℂ) : opCo k r (opVec k r p) = p := by
  refine Eq.trans ?_ (ofW_toW p)
  unfold opCo ofW
  simp only [opVec_wI]

theorem continuous_opVec : Continuous (opVec k r) := by
  refine continuous_pi fun i => ?_
  unfold opVec
  split_ifs
  · exact (continuous_apply _).comp continuous_fst
  · exact continuous_snd
  · exact continuous_const

theorem continuous_act : Continuous (Function.uncurry (act (k := k) (r := r))) := by
  have hc : Continuous fun q : Gp k r × ((Fin k → ℂ) × ℂ) =>
      (Matrix.of (inc q.1) : Mat k r) *ᵥ opVec k r q.2 :=
    Continuous.matrix_mulVec (inc_cont.comp continuous_fst) (continuous_opVec.comp continuous_snd)
  exact (continuous_pi fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp hc).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp hc)

theorem act_mul (g g' : Gp k r) (p : (Fin k → ℂ) × ℂ) : act (g * g') p = act g (act g' p) := by
  unfold act
  have e : (Matrix.of (inc (g * g')) : Mat k r) = Matrix.of (inc g) * Matrix.of (inc g') := rfl
  rw [e, op_uwb_eq_emb (inc_mem g), op_uwb_eq_emb (inc_mem g'), ← emb_mul, opAct_emb, opAct_emb, opAct_emb,
    blkAct_mul]

theorem act_one (p : (Fin k → ℂ) × ℂ) : act (1 : Gp k r) p = p := by
  have e : (Matrix.of (inc (1 : Gp k r)) : Mat k r) = 1 := rfl
  unfold act opAct
  rw [e, Matrix.one_mulVec, opCo_opVec]

def pt (k : ℕ) (T' : ℝ) : (Fin k → ℂ) × ℂ := (0, (Real.sqrt T' : ℂ))

theorem opVec_pt (T' : ℝ) : opVec k r (pt k T') = opBase k r T' := by
  funext i
  unfold opVec pt opBase wLast
  simp only [Pi.smul_apply, bvec_apply, wI, Fin.ext_iff, Fin.val_last, smul_eq_mul, Pi.zero_apply]
  split_ifs <;> first | omega | simp

theorem act_pt (T' : ℝ) (g : Gp k r) : act g (pt k T') = opOrb k r T' (inc g) := by
  unfold act opAct opOrb
  rw [opVec_pt]

theorem act_trans {T' : ℝ} (hT : 0 < T') {x : (Fin k → ℂ) × ℂ} (hx : x ∈ hypS k T') :
    ∃ g : Gp k r, act g (pt k T') = x := by
  have hTz : Tz k r (opVec k r x) = T' := by
    unfold Tz
    rw [herm_wb _ _ (opVec_inWb x)]
    have e : wbPart k r (opVec k r x) = toW k x := funext fun m => opVec_wI x m
    rw [e]
    unfold herm
    rw [← qf_eq, Complex.ofReal_re, (hypS_iff T' x).1 hx, neg_neg]
  obtain ⟨p, hp, hpz⟩ := transW k r (opVec k r x) (opVec_inWb x) (hTz ▸ hT)
  rw [hTz] at hpz
  refine ⟨⟨p, hp⟩, (act_pt T' _).trans ?_⟩
  show opCo k r (p *ᵥ ((Real.sqrt T' : ℂ) • wLast k r)) = x
  rw [hpz, opCo_opVec]

theorem entry_bound {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) (i j : Fin (k + 1)) :
    Complex.normSq (μ i j) ≤ 1 + Complex.normSq (μ (Fin.last k) (Fin.last k)) := by
  have col : ∀ {ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}, νᴴ * Hb k * ν = Hb k → ∀ j,
      ∑ l : Fin k, Complex.normSq (ν l.castSucc j) - Complex.normSq (ν (Fin.last k) j) =
        if j = Fin.last k then -1 else 1 := by
    intro ν hν j
    have h := form_apply ν j j
    rw [hν] at h
    simp only [Hb, Matrix.diagonal_apply_eq, ← Complex.normSq_eq_conj_mul_self] at h
    apply Complex.ofReal_injective
    push_cast
    rw [← h]
    split_ifs <;> simp
  have hsq : Hb k * Hb k = 1 := by
    rw [Hb, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext j; split_ifs <;> norm_num
  have hμ' : (μᴴ)ᴴ * Hb k * μᴴ = Hb k := by
    have h1 : μ * (Hb k * μᴴ * Hb k) = 1 := mul_eq_one_comm.1 (hb_inv_mul hμ)
    rw [conjTranspose_conjTranspose]
    calc μ * Hb k * μᴴ = μ * (Hb k * μᴴ * Hb k) * Hb k := by
          simp only [Matrix.mul_assoc]; rw [hsq, Matrix.mul_one]
      _ = Hb k := by rw [h1, Matrix.one_mul]
  have row : ∀ j, Complex.normSq (μ (Fin.last k) j) ≤ Complex.normSq (μ (Fin.last k) (Fin.last k)) := by
    intro j
    refine Fin.lastCases le_rfl (fun j => ?_) j
    have h := col hμ' (Fin.last k)
    simp only [conjTranspose_apply, if_true, Complex.star_def, Complex.normSq_conj] at h
    have := Finset.single_le_sum (f := fun l : Fin k => Complex.normSq (μ (Fin.last k) l.castSucc))
      (fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    linarith
  refine Fin.lastCases (by linarith [row j]) (fun i => ?_) i
  have h := col hμ j
  have := Finset.single_le_sum (f := fun l : Fin k => Complex.normSq (μ l.castSucc j))
    (fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have h2 := row j
  split_ifs at h <;> linarith

theorem inc_closedEmbedding : IsClosedEmbedding (inc : Gp k r → Mt k r) :=
  amb_closed.isClosedEmbedding_subtypeVal

theorem orbit_proper {T' : ℝ} (hT : 0 < T') (R : ℝ) :
    ∃ K : Set (Gp k r), IsCompact K ∧ ∀ g, act g (pt k T') ∈ Metric.closedBall 0 R → g ∈ K := by
  refine ⟨inc ⁻¹' Metric.closedBall 0 (Real.sqrt (1 + R ^ 2 / T')),
    inc_closedEmbedding.isCompact_preimage (isCompact_closedBall _ _), fun g hg => ?_⟩
  set μ := (Matrix.of (inc g) : Mat k r).submatrix (wI k r) (wI k r) with hμdef
  have he : (Matrix.of (inc g) : Mat k r) = embWb k r μ := op_uwb_eq_emb (inc_mem g)
  have hμ : μᴴ * Hb k * μ = Hb k := by
    rw [← emb_mem (r := r), ← he]; exact (inc_mem g).1
  have hlast : Complex.normSq (μ (Fin.last k) (Fin.last k)) ≤ R ^ 2 / T' := by
    rw [mem_closedBall_zero_iff] at hg
    have h2 : ‖(act g (pt k T')).2‖ ≤ R := (norm_snd_le _).trans hg
    have e : (act g (pt k T')).2 = (Real.sqrt T' : ℂ) * μ (Fin.last k) (Fin.last k) := by
      rw [act_pt]
      show ((Matrix.of (inc g) : Mat k r) *ᵥ ((Real.sqrt T' : ℂ) • bvec (wI k r (Fin.last k))))
        (wI k r (Fin.last k)) = _
      rw [Matrix.mulVec_smul, Pi.smul_apply, mulVec_bvec]
      rfl
    have h3 : Complex.normSq (act g (pt k T')).2 ≤ R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [e, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hT.le] at h3
    rw [le_div_iff₀ hT]
    linarith
  have hpos : 0 ≤ R ^ 2 / T' := by positivity
  have hent : ∀ i j, Complex.normSq (inc g i j) ≤ 1 + R ^ 2 / T' := by
    intro i j
    have e : inc g i j = embWb k r μ i j := congrFun (congrFun he i) j
    rw [e]
    by_cases hi : mid k r i
    · by_cases hj : mid k r j
      · rw [emb_mid _ i j hi hj]
        linarith [entry_bound hμ (midx hi) (midx hj)]
      · rw [emb_out_col _ i j hj]
        split_ifs <;> simp <;> linarith
    · rw [emb_out_row _ i j hi]
      split_ifs <;> simp <;> linarith
  show inc g ∈ Metric.closedBall 0 _
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro j
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  exact hent i j

theorem pull_right (ν : Measure (Mt k r)) (hc : ν {x | Matrix.of x ∉ UWb k r} = 0)
    (h : ∀ p ∈ UWb k r, ν.map (rmulM p) = ν) : (pull ν).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  apply inc_memb.map_injective
  have e : (inc : Gp k r → Mt k r) ∘ (fun x => x * g) = rmulM (Matrix.of (inc g)) ∘ inc := rfl
  show ((pull ν).map (fun x => x * g)).map inc = (pull ν).map inc
  rw [Measure.map_map inc_memb.measurable (continuous_mul_const g).measurable, e,
    ← Measure.map_map (rmulM_cont _).measurable inc_memb.measurable, map_pull ν hc, h _ (inc_mem g)]

theorem pull_compact (ν : Measure (Mt k r)) (hG : IsGaugeOn k r (UWb k r) ν) {K : Set (Gp k r)}
    (hK : IsCompact K) : pull ν K ≠ ⊤ := by
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  obtain ⟨⟨hσ, hne, hc, hl⟩, -⟩ := hG
  haveI : LocallyCompactSpace (Gp k r) := inc_closedEmbedding.locallyCompactSpace
  haveI : T2Space (Gp k r) := inc_closedEmbedding.isEmbedding.t2Space
  haveI := pull_sigmaFinite ν
  haveI := pull_left ν hl
  have key := measure_eq_div_smul (Measure.haar : Measure (Gp k r)) (pull ν) (s := inc ⁻¹' bBall k r ρ)
    (by rw [pull_apply ν hc]; exact h0.ne') (by rw [pull_apply ν hc]; exact ht.ne)
  set c := (Measure.haar : Measure (Gp k r)) (inc ⁻¹' bBall k r ρ) / pull ν (inc ⁻¹' bBall k r ρ)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at key
    exact NeZero.ne _ key
  have h1 : (Measure.haar : Measure (Gp k r)) K ≠ ⊤ := hK.measure_lt_top.ne
  rw [key, Measure.smul_apply, smul_eq_mul] at h1
  intro htop
  rw [htop, ENNReal.mul_top hc0] at h1
  exact h1 rfl

theorem orbRepY : OrbRepY := by
  intro k r T' hk hT νg hG Q hQ hS hC
  by_cases hQ0 : Q = 0
  · exact ⟨0, ENNReal.zero_ne_top, by rw [hQ0, zero_smul]⟩
  haveI : IsFiniteMeasureOnCompacts Q := ⟨fun C h => hC C h⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, Q (Metric.closedBall 0 R) ≠ 0 := by
    by_contra h
    push Not at h
    apply hQ0
    rw [← Measure.measure_univ_eq_zero, ← Metric.iUnion_closedBall_nat (0 : (Fin k → ℂ) × ℂ)]
    exact measure_iUnion_null h
  set C : Set ((Fin k → ℂ) × ℂ) := Metric.closedBall 0 R with hCdef
  have hCm : MeasurableSet C := Metric.isClosed_closedBall.measurableSet
  have hRt : Q C ≠ ⊤ := (hC C (isCompact_closedBall _ _)).ne
  have hU := unimodW k r νg hk hG
  have hfin := fun K => pull_compact νg hG (K := K)
  obtain ⟨⟨hσ, hne, hc, hl⟩, -⟩ := hG
  haveI := pull_sigmaFinite νg
  haveI := pull_left νg hl
  haveI := pull_right νg hc hU
  have hom := (continuous_opOrb (k := k) (r := r) T').measurable
  have htr : ∀ᵐ x ∂Q, ∃ g : Gp k r, act g (pt k T') = x := by
    have : ∀ᵐ x ∂Q, x ∈ hypS k T' := hS
    exact this.mono fun x hx => act_trans hT hx
  set b := ∫⁻ g : Gp k r, C.indicator 1 (act g⁻¹ (pt k T')) ∂(pull νg) with hb
  have key : ∀ E, MeasurableSet E → νg.map (opOrb k r T') E * Q C = Q E * b := by
    intro E hE
    have h := fubini_identity act continuous_act.measurable act_mul act_one (pull νg) Q
      (fun g => hQ _ (inc_mem g)) (pt k T') htr (measurable_one.indicator hE) (measurable_one.indicator hCm)
    rw [lintegral_indicator_one hE, lintegral_indicator_one hCm] at h
    rw [← h]
    congr 1
    rw [← lintegral_indicator_one hE, ← map_pull νg hc, lintegral_map (measurable_one.indicator hE) hom,
      inc_memb.lintegral_map, map_pull νg hc]
    simp_rw [act_pt]
  have hbt : b ≠ ⊤ := by
    obtain ⟨K, hK, hKm⟩ := orbit_proper (k := k) (r := r) hT R
    haveI : T2Space (Gp k r) := inc_closedEmbedding.isEmbedding.t2Space
    refine ne_top_of_le_ne_top (hfin K⁻¹ hK.inv) ?_
    rw [← lintegral_indicator_one hK.inv.measurableSet]
    refine lintegral_mono fun g => ?_
    by_cases hg : act g⁻¹ (pt k T') ∈ C
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (Set.mem_inv.2 (hKm _ hg))]
      rfl
    · rw [Set.indicator_of_notMem hg]; exact zero_le
  have hb0 : b ≠ 0 := by
    intro h0
    have h := key Set.univ MeasurableSet.univ
    rw [h0, mul_zero, Measure.map_apply hom MeasurableSet.univ, Set.preimage_univ] at h
    rcases mul_eq_zero.1 h with h | h
    · exact hne (Measure.measure_univ_eq_zero.1 h)
    · exact hR h
  refine ⟨Q C / b, (ENNReal.div_lt_top hRt hb0).ne, ?_⟩
  ext E hE
  rw [Measure.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_right_comm, mul_comm (Q C), key E hE, mul_assoc,
    ENNReal.mul_inv_cancel hb0 hbt, mul_one]

end GlobalTheory.HypOrbitUnique
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_orbit_representation : PI.RhsWLim.W.OrbRepY := by
  atlas_forward_decl GlobalTheory.HypOrbitUnique.orbRepY
end

section
noncomputable section

namespace GlobalTheory.RankOneChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI

theorem rhsWLim_of_leaves (hD : HaarDens) (hQ : HypQ) (hC : HypChart) (hK : GaugeK) (hV : GaugeVolUk)
    (hT : TubeLimK) (hR : OrbRepY) : Formalism.L2.SG.Pf.WB.RhsWLim := by
  have hL : PI.RhsWLim.RhsWLim :=
    rhsWLim_of mBaseMem tBallMeas (gaugeExists_of_dens hD) (rhsHaar_of (rhsWInv_of_hypQ hQ)) haarUniq
      (constVal_of_orbit (orbitPush_of hV hK hT (hypInv_of lebInvB (coneForm_of hypTh coneVol)) hR
        (hypLocal_of chartJac hC hermitianDefectAdd) opEMeas hypLF))
  exact fun k r z z' μW μW' a a' μsec hW => hL k r z z' μW μW' a a' μsec
    ⟨hW.k_pos, hW.z_mem, hW.z'_mem, hW.T_pos, hW.T'_pos, hW.haarW, hW.haarW', hW.a_pos, hW.a'_pos, hW.massW,
      hW.massW', hW.sec⟩

theorem rhsWLim : Formalism.L2.SG.Pf.WB.RhsWLim :=
  rhsWLim_of_leaves GlobalTheory.T.haar_unitaryGroupWb_density_chart GlobalTheory.T.hyperboloid_invariant_measure_polar_form GlobalTheory.T.hyperboloid_chart_measure_formula GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure GlobalTheory.T.unitaryGroup_gaugeVolume_in_hermitianUnitary GlobalTheory.T.stabilizerTube_gaugeMass_asymptotic GlobalTheory.T.hyperboloid_invariant_measure_orbit_representation

instance : Fact (Formalism.L2.SG.Pf.WB.RhsWLim) := ⟨rhsWLim⟩

end GlobalTheory.RankOneChart
end
end
