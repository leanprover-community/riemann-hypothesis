module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

def fnRho (i : ι) (v : V n) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))

theorem fn_symm_aemeas (i : ι) :
    AEMeasurable (A.chart i).symm (volume.restrict (A.chart i).target) :=
  (A.chart i).continuousOn_symm.aemeasurable (A.chart i).open_target.measurableSet

theorem fn_rho_aemeas (i : ι) : AEMeasurable (fnRho A i) (volume.restrict (A.chart i).target) := by
  have h : ContinuousOn (fnRho A i) (A.chart i).target :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)
  exact h.aemeasurable (A.chart i).open_target.measurableSet

theorem fn_map (i : ι) :
    Measure.map (A.chart i).symm ((volume.restrict (A.chart i).target).withDensity (fnRho A i)) =
      A.mu.restrict (A.chart i).source := by
  have hsymm : AEMeasurable (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity (fnRho A i)) :=
    (fn_symm_aemeas A i).mono_ac (withDensity_absolutelyContinuous _ _)
  refine Measure.ext fun t ht => ?_
  rw [Measure.map_apply_of_aemeasurable hsymm ht, withDensity_apply' _ _,
    Measure.restrict_restrict' (A.chart i).open_target.measurableSet, Measure.restrict_apply ht,
    A.mu_chart i _ (ht.inter (A.chart i).open_source.measurableSet) Set.inter_subset_right,
    Set.inter_comm t (A.chart i).source, (A.chart i).image_source_inter_eq', Set.inter_comm]
  rfl

theorem fn_lint (i : ι) {φ : Y → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x in (A.chart i).source, φ x ∂A.mu =
      ∫⁻ v in (A.chart i).target, fnRho A i v * φ ((A.chart i).symm v) := by
  have hsymm : AEMeasurable (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity (fnRho A i)) :=
    (fn_symm_aemeas A i).mono_ac (withDensity_absolutelyContinuous _ _)
  rw [← fn_map A i, lintegral_map' hφ.aemeasurable hsymm]
  exact lintegral_withDensity_eq_lintegral_mul₀ (fn_rho_aemeas A i)
    (hφ.comp_aemeasurable (fn_symm_aemeas A i))
theorem fn_contOn_sec {la : La} {U : Set Y} {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) (i : ι) :
    ContinuousOn (F i) ((A.chart i).source ∩ U) := by
  have h := (hFs.1 i).continuousOn.comp ((A.chart i).continuousOn.mono Set.inter_subset_left)
    (fun x hx => ⟨(A.chart i).map_source hx.1, by
      show (A.chart i).symm ((A.chart i) x) ∈ U
      rw [(A.chart i).left_inv hx.1]
      exact hx.2⟩)
  refine h.congr fun x hx => ?_
  simp [Function.comp, (A.chart i).left_inv hx.1]

theorem fn_contOn_ph (la : La) (i : ι) : ContinuousOn (A.ph la i) (A.chart i).source := by
  have h := (A.smooth_ph la i).continuousOn.comp (A.chart i).continuousOn
    (fun x hx => (A.chart i).map_source hx)
  refine h.congr fun x hx => ?_
  simp [Function.comp, (A.chart i).left_inv hx]

theorem fn_nsq_eq {la : La} {U : Set Y} {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) {i : ι} {x : Y}
    (hxs : x ∈ (A.chart i).source) (hxU : x ∈ U) :
    ‖F i x‖ ^ 2 * Real.exp (-A.ph la i x) = A.nsq la F x := by
  unfold WeightedAtlas.nsq
  have hj : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
  have hg : 0 < ‖A.g la i (A.pick x) x‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (A.g_ne la i (A.pick x) x hxs hj)) 2
  rw [hFs.2 i (A.pick x) x hxU hxs hj, A.ph_trans la i (A.pick x) x hxs hj,
    show -(A.ph la i x - Real.log (‖A.g la i (A.pick x) x‖ ^ 2)) =
      Real.log (‖A.g la i (A.pick x) x‖ ^ 2) + -A.ph la i x by ring,
    Real.exp_add, Real.exp_log hg, norm_mul]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
