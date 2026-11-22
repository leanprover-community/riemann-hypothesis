module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem nsq_eq_chart (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s)
    {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold nsq
  set j := A.pick y
  have hj : y ∈ (A.chart j).source := A.mem_pick y
  have h1 : s i y = A.g la i j y * s j y := hs.2 i j y trivial hy hj
  have h2 : A.ph la j y = A.ph la i y - Real.log (‖A.g la i j y‖ ^ 2) := A.ph_trans la i j y hy hj
  have hg : 0 < ‖A.g la i j y‖ ^ 2 := by
    have := A.g_ne la i j y hy hj
    positivity
  rw [h1, h2, norm_mul, mul_pow, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hg]
  ring

theorem continuousOn_sec (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s)
    (i : ι) : ContinuousOn (s i) (A.chart i).source := by
  have h1 : ContinuousOn (s i ∘ (A.chart i).symm) (A.chart i).target := by
    have := (hs.1 i).continuousOn
    simpa [Set.preimage_univ, Set.inter_univ] using this
  have h2 : ContinuousOn ((s i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)
  refine h2.congr (fun x hx => ?_)
  simp [Function.comp, (A.chart i).left_inv hx]

theorem continuousOn_ph (A : WeightedAtlas n Y ι La) (la : La) (i : ι) :
    ContinuousOn (A.ph la i) (A.chart i).source := by
  have h1 : ContinuousOn (A.ph la i ∘ (A.chart i).symm) (A.chart i).target :=
    (A.smooth_ph la i).continuousOn
  have h2 : ContinuousOn ((A.ph la i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)
  refine h2.congr (fun x hx => ?_)
  simp [Function.comp, (A.chart i).left_inv hx]

theorem continuous_nsq (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s) :
    Continuous (A.nsq la s) := by
  rw [continuous_iff_continuousAt]
  intro y
  set i := A.pick y
  have hU : (A.chart i).source ∈ 𝓝 y := (A.chart i).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousOn (fun x => ‖s i x‖ ^ 2 * Real.exp (-A.ph la i x)) (A.chart i).source :=
    ((A.continuousOn_sec hs i).norm.pow 2).mul ((A.continuousOn_ph la i).neg.rexp)
  refine (hc.continuousAt hU).congr ?_
  filter_upwards [hU] with x hx
  exact (A.nsq_eq_chart hs hx).symm

theorem continuous_sqn (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    (hw : ∀ k, A.IsSec la (w k)) : Continuous (A.sqn la w) := by
  unfold sqn
  exact continuous_finsetSum _ (fun k _ => A.continuous_nsq (hw k))

theorem nsq_nonneg (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) (y : Y) :
    0 ≤ A.nsq la s y := by
  unfold nsq; positivity

theorem sqn_nonneg (A : WeightedAtlas n Y ι La) (la : La) {N : ℕ} (w : Fin N → ι → Y → ℂ) (y : Y) :
    0 ≤ A.sqn la w y := by
  unfold sqn; exact Finset.sum_nonneg (fun k _ => A.nsq_nonneg la (w k) y)

theorem nsq_sum_le (A : WeightedAtlas n Y ι La) (la : La) {κ : Type*} (F : Finset κ)
    (h : κ → ι → Y → ℂ) (y : Y) :
    A.nsq la (fun i y => ∑ q ∈ F, h q i y) y ≤ (F.card : ℝ) * ∑ q ∈ F, A.nsq la (h q) y := by
  unfold nsq
  have h1 : ‖∑ q ∈ F, h q (A.pick y) y‖ ^ 2 ≤ (F.card : ℝ) * ∑ q ∈ F, ‖h q (A.pick y) y‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq
  have he : 0 ≤ Real.exp (-A.ph la (A.pick y) y) := (Real.exp_pos _).le
  calc ‖∑ q ∈ F, h q (A.pick y) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y) y)
      ≤ ((F.card : ℝ) * ∑ q ∈ F, ‖h q (A.pick y) y‖ ^ 2) * Real.exp (-A.ph la (A.pick y) y) :=
        mul_le_mul_of_nonneg_right h1 he
    _ = _ := by rw [mul_assoc, Finset.sum_mul]

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
