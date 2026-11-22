module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNullB
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem hyq_nsq_chart (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source)
    (hs : s i y = A.g la i (A.pick y) y * s (A.pick y) y) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold WeightedAtlas.nsq
  have hp := A.mem_pick y
  have hg := A.g_ne la i (A.pick y) y hi hp
  have hpos : 0 < ‖A.g la i (A.pick y) y‖ ^ 2 := pow_pos (norm_pos_iff.2 hg) 2
  rw [A.ph_trans la i (A.pick y) y hi hp, hs, norm_mul, mul_pow]
  rw [show -(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2)) =
      -A.ph la i y + Real.log (‖A.g la i (A.pick y) y‖ ^ 2) by ring, Real.exp_add,
    Real.exp_log hpos]
  ring

theorem hyq_bdd {f : V n → ℝ} {c : V n} {r : ℝ} (hf : ContinuousOn f (closedBall c r)) :
    ∃ C : ℝ, ∀ v ∈ closedBall c r, f v ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r).bddAbove_image hf
  exact ⟨C, fun v hv => hC (Set.mem_image_of_mem f hv)⟩

theorem hyq_contDiffAt_of_holo {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {c : V n} (hc : c ∈ U) : ContDiffAt ℝ ∞ g c :=
  (((contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hc))).restrict_scalars ℝ

theorem hyq_contDiffAt_of_ev {g : V n → ℂ} {c : V n}
    (hg : ∀ᶠ v in 𝓝 c, DifferentiableAt ℂ g v) : ContDiffAt ℝ ∞ g c := by
  obtain ⟨U, hU, hUo, hcU⟩ := _root_.eventually_nhds_iff.1 hg
  exact hyq_contDiffAt_of_holo hUo (fun v hv => (hU v hv).differentiableWithinAt) hcU

variable   (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {la : La} {σ : ι → Y → ℂ}

end

end ReciprocityTheory.L2DbarEstimates.Y
