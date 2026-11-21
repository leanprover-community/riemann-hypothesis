import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HormanderEstimateOnBallConstLeviBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPart
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import BuildAid.ForwardExisting

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.GlueDist

theorem sq_norm_smoothSection_sub_glued_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n0 A la (F0 - glue C la u) ≤ (C.m : ℝ≥0∞) * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 u hF hu
  classical
  set L := A.kap + la with hL

  set D : Fin C.m → ι → Y → ℂ := fun a j y =>
    F0 j y - A.g L j (C.idx a) y * u a (A.chart (C.idx a) y) with hD
  set S : Fin C.m → Set Y := fun a =>
    (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) with hS
  have hSo : ∀ a, IsOpen (S a) := fun a =>
    (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hsec : ∀ a, ∀ y ∈ (A.chart (C.idx a)).source, ∀ j, y ∈ (A.chart j).source →
      D a j y = A.g L j (C.idx a) y * D a (C.idx a) y := by
    intro a y hy j hj
    simp only [hD]
    rw [hF.2 j (C.idx a) y hj hy, A.g_self L (C.idx a) hy]
    ring
  have hchart : ∀ a, ∀ y ∈ (A.chart (C.idx a)).source,
      A.nsq L (D a) y = ‖F0 (C.idx a) y - u a (A.chart (C.idx a) y)‖ ^ 2 *
        Real.exp (-A.ph L (C.idx a) y) := by
    intro a y hy
    rw [A.nsq_chart L (D a) (C.idx a) hy (hsec a y hy _ (A.mem_pick y))]
    simp only [hD, A.g_self L (C.idx a) hy, one_mul]

  have hsum1 : ∀ y, ∑ a, (C.chi a y : ℂ) = 1 := by
    intro y; rw [← Complex.ofReal_sum, C.sum_one y, Complex.ofReal_one]
  have hG : F0 - glue C la u = fun j y => ∑ a, (C.chi a y : ℂ) * D a j y := by
    funext j y
    simp only [Pi.sub_apply, glue, hD, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hsum1 y, one_mul]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have hchi1 : ∀ a y, C.chi a y ≤ 1 := by
    intro a y
    rw [← C.sum_one y]
    exact Finset.single_le_sum (fun b _ => C.nonneg b y) (Finset.mem_univ a)

  have hpt : ∀ y, A.nsq L (F0 - glue C la u) y ≤
      (C.m : ℝ) * ∑ a, (S a).indicator (A.nsq L (D a)) y := by
    intro y
    rw [hG]
    refine (A.nsq_sum_le L Finset.univ (fun a j y => (C.chi a y : ℂ) * D a j y) y).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)
    have he : A.nsq L (fun j y => (C.chi a y : ℂ) * D a j y) y = C.chi a y ^ 2 * A.nsq L (D a) y := by
      unfold WeightedAtlas.nsq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.nonneg a y)]
      ring
    rw [he]
    by_cases h0 : C.chi a y = 0
    · rw [h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact Set.indicator_nonneg (fun x _ => A.nsq_nonneg L (D a) x) y
    · have hyS : y ∈ S a := C.supp a (subset_tsupport _ h0)
      rw [Set.indicator_of_mem hyS]
      have h2 : C.chi a y ^ 2 ≤ 1 := pow_le_one₀ (C.nonneg a y) (hchi1 a y)
      nlinarith [A.nsq_nonneg L (D a) y]

  have hF0c : ∀ i, ContinuousOn (F0 i) (A.chart i).source := by
    intro i
    have h1 : ContinuousOn (F0 i ∘ (A.chart i).symm) (A.chart i).target := (hF.1 i).continuousOn
    refine (h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)).congr
      (fun x hx => ?_)
    simp [Function.comp, (A.chart i).left_inv hx]
  have hcont : ∀ a, ContinuousOn (fun y => ENNReal.ofReal (A.nsq L (D a) y)) (S a) := by
    intro a
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    have hu' : ContinuousOn (fun y => u a (A.chart (C.idx a) y)) (S a) :=
      (hu a).continuousOn.comp ((A.chart (C.idx a)).continuousOn.mono Set.inter_subset_left)
        (fun y hy => hy.2)
    have hc : ContinuousOn (fun y => ‖F0 (C.idx a) y - u a (A.chart (C.idx a) y)‖ ^ 2 *
        Real.exp (-A.ph L (C.idx a) y)) (S a) :=
      ((((hF0c (C.idx a)).mono Set.inter_subset_left).sub hu').norm.pow 2).mul
        ((A.continuousOn_ph L (C.idx a)).mono Set.inter_subset_left).neg.rexp
    exact hc.congr (fun y hy => hchart a y hy.1)
  have hmeas : ∀ a, AEMeasurable ((S a).indicator (fun y => ENNReal.ofReal (A.nsq L (D a) y))) A.mu :=
    fun a => (aemeasurable_indicator_iff (hSo a).measurableSet).2
      ((hcont a).aemeasurable (hSo a).measurableSet)

  have hpiece : ∀ a, ∫⁻ y in S a, ENNReal.ofReal (A.nsq L (D a) y) ∂A.mu =
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro a
    have hWt : ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
      ball_subset_closedBall.trans (C.sub a)
    have heq : ∀ v ∈ ball (C.c a) (C.r a),
        D a (C.idx a) ((A.chart (C.idx a)).symm v) = F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v := by
      intro v hv
      have hvt := hWt hv
      simp only [hD, A.g_self L (C.idx a) ((A.chart (C.idx a)).map_target hvt),
        (A.chart (C.idx a)).right_inv hvt, one_mul]
    have hae : AEMeasurable (D a (C.idx a) ∘ (A.chart (C.idx a)).symm) (volume.restrict (ball (C.c a) (C.r a))) := by
      have hc : ContinuousOn (fun v => F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v) (ball (C.c a) (C.r a)) :=
        (((hF.1 (C.idx a)).continuousOn.mono hWt).sub (hu a).continuousOn)
      exact (hc.congr (fun v hv => heq v hv)).aemeasurable measurableSet_ball
    rw [GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx a) (ball (C.c a) (C.r a)) (D a) measurableSet_ball hWt
      (fun y hy _ => hsec a y hy _ (A.mem_pick y)) hae]
    refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
    rw [heq v hv]

  unfold n0
  calc ∫⁻ y, ENNReal.ofReal (A.nsq L (F0 - glue C la u) y) ∂A.mu
      ≤ ∫⁻ y, (C.m : ℝ≥0∞) * ∑ a, (S a).indicator (fun y => ENNReal.ofReal (A.nsq L (D a) y)) y ∂A.mu := by
        refine lintegral_mono fun y => ?_
        refine (ENNReal.ofReal_le_ofReal (hpt y)).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun a _ => Set.indicator_nonneg (fun x _ => A.nsq_nonneg L (D a) x) y)]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hy : y ∈ S a
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
    _ = (C.m : ℝ≥0∞) * ∑ a, ∫⁻ y in S a, ENNReal.ofReal (A.nsq L (D a) y) ∂A.mu := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_finset_sum' _ (fun a _ => hmeas a)]
        congr 1
        exact Finset.sum_congr rfl fun a _ => lintegral_indicator (hSo a).measurableSet _
    _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun a _ => hpiece a

end GlobalTheory.GlueDist
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.n0_sub_glue_le_card_mul_sum_lintegral : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n0 A la (F0 - glue C la u) ≤ (C.m : ℝ≥0∞) * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  atlas_forward_decl GlobalTheory.GlueDist.sq_norm_smoothSection_sub_glued_le
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem glue_wdb_eq : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) (i : ι) (v : V n) (w : ℂ) (j : Fin n), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → v ∈ (A.chart i).target → wdb n j (glue C la u i ∘ (A.chart i).symm) v = ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) * u a (A.chart (C.idx a) ((A.chart i).symm v)) - w) := by
  intro n Y _ _ _ _ _ ι La _ A C la u i v w j hu hv
  have hopen : IsOpen (A.chart i).target := (A.chart i).open_target
  have hchi : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v := by
    intro a
    have h1 : ContDiffOn ℝ ∞ (C.chi a ∘ (A.chart i).symm) (A.chart i).target := C.smooth a i
    have h2 : DifferentiableAt ℝ (C.chi a ∘ (A.chart i).symm) v :=
      (h1.contDiffAt (hopen.mem_nhds hv)).differentiableAt (by simp)
    exact ReciprocityTheory.L2DbarEstimates.differentiableAt_ofReal h2
  have key : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v ∧
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v =
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v *
        (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
          u a (A.chart (C.idx a) ((A.chart i).symm v))) := by
    intro a
    by_cases hs : (A.chart i).symm v ∈ tsupport (C.chi a)
    · have hsrc := (C.supp a hs).1
      have hball : A.chart (C.idx a) ((A.chart i).symm v) ∈ ball (C.c a) (C.r a) := (C.supp a hs).2
      have hovl : IsOpen (ovl A.chart i (C.idx a)) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source
      have hmem : v ∈ ovl A.chart i (C.idx a) := ⟨hv, hsrc⟩
      have hg : DifferentiableAt ℂ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_g _ i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have htr : DifferentiableAt ℂ (A.chart (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_trans i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have hua : DifferentiableAt ℂ (u a) (A.chart (C.idx a) ((A.chart i).symm v)) :=
        (hu a).differentiableAt (isOpen_ball.mem_nhds hball)
      have hh : DifferentiableAt ℂ (fun x => A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) v :=
        hg.mul (hua.comp v htr)
      have heq : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =
          (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x)))) := by
        funext x; ring
      rw [heq]
      refine ⟨(hchi a).mul (hh.restrictScalars ℝ), ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_mul (hchi a) (hh.restrictScalars ℝ),
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt hh]
      ring
    · have hn : (A.chart i).symm ⁻¹' (tsupport (C.chi a))ᶜ ∈ 𝓝 v :=
        ((A.chart i).continuousAt_symm hv).preimage_mem_nhds
          ((isClosed_tsupport _).isOpen_compl.mem_nhds hs)
      have hz : ∀ᶠ x in 𝓝 v, C.chi a ((A.chart i).symm x) = 0 :=
        Filter.mem_of_superset hn fun x hx => image_eq_zero_of_notMem_tsupport hx
      have hf0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hc0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hw0 : wdb n j (fun _ : V n => (0 : ℂ)) v = 0 :=
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
      refine ⟨(differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hf0, ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hf0, ReciprocityTheory.L2DbarEstimates.wdb_congr hc0, hw0, zero_mul]
  have hglue : glue C la u i ∘ (A.chart i).symm = fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x)) := by
    funext x; rfl
  have hone : (fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ)) = fun _ : V n => (1 : ℂ) := by
    funext x; rw [← Complex.ofReal_sum, C.sum_one]; simp
  have hsum0 : ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
    rw [← ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => hchi a), hone]
    exact ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
  rw [hglue, ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => (key a).1)]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum0, zero_mul, sub_zero]
  exact Finset.sum_congr rfl fun a _ => (key a).2

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_glueSectionByPartition_eq : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) (i : ι) (v : V n) (w : ℂ) (j : Fin n), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → v ∈ (A.chart i).target → wdb n j (glue C la u i ∘ (A.chart i).symm) v = ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) * u a (A.chart (C.idx a) ((A.chart i).symm v)) - w) := by
  atlas_forward_decl GlobalTheory.glue_wdb_eq
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.GlueEnergy

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] {A : WeightedAtlas n Y ι La}

theorem exists_bound (C : Cover A) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a b j, ∀ v ∈ ball (C.c b) (C.r b),
    ‖wdb n j (fun x => (C.chi a ((A.chart (C.idx b)).symm x) : ℂ)) v‖ ≤ B := by
  have h : ∀ p : Fin C.m × Fin C.m × Fin n, ∃ B : ℝ, ∀ v ∈ closedBall (C.c p.2.1) (C.r p.2.1),
      ‖wdb n p.2.2 (fun x => (C.chi p.1 ((A.chart (C.idx p.2.1)).symm x) : ℂ)) v‖ ≤ B := by
    rintro ⟨a, b, j⟩
    apply (isCompact_closedBall _ _).exists_bound_of_continuousOn
    refine ContinuousOn.mono ?_ (C.sub b)
    have h1 : ContDiffOn ℝ ∞ (fun x => (C.chi a ((A.chart (C.idx b)).symm x) : ℂ))
        (A.chart (C.idx b)).target :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (C.smooth a (C.idx b))
    have h2 := h1.continuousOn_fderiv_of_isOpen (A.chart (C.idx b)).open_target (by simp)
    unfold wdb
    exact ((h2.clm_apply continuousOn_const).add
      (continuousOn_const.mul (h2.clm_apply continuousOn_const))).div_const _
  choose B hB using h
  refine ⟨∑ p, |B p|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun a b j v hv => ?_⟩
  exact ((hB (a, b, j) v (ball_subset_closedBall hv)).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun p => |B p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))

theorem wdb_eq_zero (C : Cover A) (a : Fin C.m) (i : ι) (j : Fin n) (v : V n)
    (hv : v ∈ (A.chart i).target)
    (h : (A.chart i).symm v ∉
      (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) :
    wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
  have h1 : (A.chart i).symm v ∉ tsupport (C.chi a) := fun h' => h (C.supp a h')
  have h2 := notMem_tsupport_iff_eventuallyEq.mp h1
  have h3 := ((A.chart i).continuousAt_symm hv).eventually h2
  have h4 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => 0 :=
    h3.mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]
  unfold wdb
  rw [h4.fderiv_eq]
  simp

theorem sq_sum_le {m : ℕ} (x d : Fin m → ℂ) (B : ℝ) (e : Fin m → ℝ)
    (h : ∀ a, ‖x a * d a‖ ^ 2 ≤ B ^ 2 * e a) :
    ‖∑ a, x a * d a‖ ^ 2 ≤ m * B ^ 2 * ∑ a, e a := by
  calc ‖∑ a, x a * d a‖ ^ 2 ≤ (∑ a, ‖x a * d a‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ m * ∑ a, ‖x a * d a‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖x a * d a‖)
    _ ≤ m * ∑ a, B ^ 2 * e a := by gcongr with a; exact h a
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem energy_glue_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n1 C la (glue C la u) ≤ ENNReal.ofReal K * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A C
  obtain ⟨B, hB0, hB⟩ := exists_bound C
  refine ⟨C.m * (n * (C.m * B ^ 2)), by positivity, fun la F0 u hF hu => ?_⟩
  set D : Fin C.m → ι → Y → ℂ := fun a i y =>
    A.g (A.kap + la) i (C.idx a) y * u a (A.chart (C.idx a) y) - F0 i y with hD
  set U : Fin C.m → Set Y := fun a =>
    (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) with hU
  have hUo : ∀ a, IsOpen (U a) := fun a => (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hbt : ∀ b, ball (C.c b) (C.r b) ⊆ (A.chart (C.idx b)).target := fun b =>
    ball_subset_closedBall.trans (C.sub b)
  set W : Fin C.m → Fin C.m → Set (V n) := fun b a =>
    ball (C.c b) (C.r b) ∩ ((A.chart (C.idx b)).target ∩ (A.chart (C.idx b)).symm ⁻¹' U a) with hW
  have hWo : ∀ b a, IsOpen (W b a) := fun b a =>
    isOpen_ball.inter ((A.chart (C.idx b)).isOpen_inter_preimage_symm (hUo a))
  have hDc : ∀ b a, ContinuousOn (D a (C.idx b) ∘ (A.chart (C.idx b)).symm) (W b a) := by
    intro b a
    have hov : W b a ⊆ ovl A.chart (C.idx b) (C.idx a) := fun v hv => ⟨hv.2.1, hv.2.2.1⟩
    have h1 := (A.holo_g (A.kap + la) (C.idx b) (C.idx a)).continuousOn.mono hov
    have h2 := (A.holo_trans (C.idx b) (C.idx a)).continuousOn.mono hov
    have h3 := (hu a).continuousOn.comp h2 (fun v hv => hv.2.2.2)
    have h4 := (hF.1 (C.idx b)).continuousOn.mono (t := W b a) (fun v hv => hv.2.1)
    exact (h1.mul h3).sub h4
  have hcomp : ∀ a i y, y ∈ (A.chart i).source → y ∈ (A.chart (C.idx a)).source →
      D a (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D a i y := by
    intro a i y hi ha
    simp only [hD]
    rw [A.g_cocycle _ (A.pick y) i (C.idx a) y (A.mem_pick y) hi ha,
      hF.2 (A.pick y) i y (A.mem_pick y) hi]
    ring
  set f : Fin C.m → Fin C.m → V n → ℝ≥0∞ := fun b a v => ENNReal.ofReal
    (‖D a (C.idx b) ((A.chart (C.idx b)).symm v)‖ ^ 2 *
      Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) with hf
  have hk : ∀ b a, ∫⁻ y in (A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' W b a,
      ENNReal.ofReal (A.nsq (A.kap + la) (D a) y) ∂A.mu = ∫⁻ v in W b a, f b a v := by
    intro b a
    refine GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx b) (W b a) (D a) (hWo b a).measurableSet
      (fun v hv => hv.2.1) (fun y hy hy' => hcomp a _ y hy ?_)
      ((hDc b a).aemeasurable (hWo b a).measurableSet)
    have := hy'.2.2.1
    rwa [(A.chart (C.idx b)).left_inv hy] at this
  have hWaa : ∀ a, W a a = ball (C.c a) (C.r a) := by
    intro a
    refine Set.inter_eq_left.mpr fun v hv => ⟨hbt a hv, (A.chart _).map_target (hbt a hv), ?_⟩
    show A.chart (C.idx a) ((A.chart (C.idx a)).symm v) ∈ ball (C.c a) (C.r a)
    rwa [(A.chart (C.idx a)).right_inv (hbt a hv)]
  have hE : ∀ b a, ∫⁻ v in W b a, f b a v ≤ ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
      (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro b a
    calc _ = _ := (hk b a).symm
      _ ≤ ∫⁻ y in (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' W a a,
          ENNReal.ofReal (A.nsq (A.kap + la) (D a) y) ∂A.mu := by
        apply lintegral_mono_set
        intro y hy
        rw [hWaa]
        have := hy.2.2.2
        rwa [Set.mem_preimage, (A.chart (C.idx b)).left_inv hy.1] at this
      _ = _ := hk a a
      _ = _ := by
        rw [hWaa]
        refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
        have hs := (A.chart (C.idx a)).map_target (hbt a hv)
        have h1 : A.g (A.kap + la) (C.idx a) (C.idx a) ((A.chart (C.idx a)).symm v) = 1 := by
          have h2 := A.g_cocycle (A.kap + la) _ _ _ _ hs hs hs
          have h3 := A.g_ne (A.kap + la) _ _ _ hs hs
          exact (mul_right_eq_self₀.mp h2.symm).resolve_right h3
        simp only [hf, hD]
        rw [h1, one_mul, (A.chart (C.idx a)).right_inv (hbt a hv), norm_sub_rev]
  have hfm : ∀ b a, AEMeasurable ((W b a).indicator (f b a))
      (volume.restrict (ball (C.c b) (C.r b))) := by
    intro b a
    refine AEMeasurable.restrict ?_
    rw [aemeasurable_indicator_iff (hWo b a).measurableSet]
    refine ContinuousOn.aemeasurable ?_ (hWo b a).measurableSet
    have h4 := (A.smooth_ph la (C.idx b)).continuousOn.mono (t := W b a) (fun v hv => hv.2.1)
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (((hDc b a).norm.pow 2).mul (Real.continuous_exp.comp_continuousOn h4.neg))
  have hpt : ∀ b, ∀ v ∈ ball (C.c b) (C.r b), ENNReal.ofReal
      ((∑ j, ‖wdb n j (glue C la u (C.idx b) ∘ (A.chart (C.idx b)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) ≤
      ENNReal.ofReal (n * (C.m * B ^ 2)) * ∑ a, (W b a).indicator (f b a) v := by
    intro b v hv
    set e : Fin C.m → ℝ := fun a => (W b a).indicator
      (fun v => ‖D a (C.idx b) ((A.chart (C.idx b)).symm v)‖ ^ 2) v with he
    have he0 : ∀ a, 0 ≤ e a := fun a => Set.indicator_nonneg (fun _ _ => by positivity) _
    have h1 : ∀ j, ‖wdb n j (glue C la u (C.idx b) ∘ (A.chart (C.idx b)).symm) v‖ ^ 2 ≤
        C.m * B ^ 2 * ∑ a, e a := by
      intro j
      rw [GlobalTheory.T.dbar_glueSectionByPartition_eq n Y ι La A C la u (C.idx b) v (F0 (C.idx b) ((A.chart (C.idx b)).symm v))
        j hu (hbt b hv)]
      apply sq_sum_le
      intro a
      by_cases hm : v ∈ W b a
      · simp only [he, Set.indicator_of_mem hm, hD]
        rw [norm_mul, mul_pow]
        gcongr
        exact hB a b j v hv
      · rw [wdb_eq_zero C a (C.idx b) j v (hbt b hv) (fun h => hm ⟨hv, hbt b hv, h⟩)]
        simp only [zero_mul, norm_zero]
        have := he0 a
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    have h2 : ∑ a, (W b a).indicator (f b a) v = ENNReal.ofReal ((∑ a, e a) *
        Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
        (fun a _ => mul_nonneg (he0 a) (Real.exp_pos _).le)]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hm : v ∈ W b a
      · simp only [he, hf, Set.indicator_of_mem hm]
      · simp [he, Set.indicator_of_notMem hm]
    rw [h2, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    apply ENNReal.ofReal_le_ofReal
    gcongr
    calc _ ≤ ∑ _j : Fin n, C.m * B ^ 2 * ∑ a, e a := Finset.sum_le_sum fun j _ => h1 j
      _ = _ := by simp [mul_assoc]
  unfold n1
  calc _ ≤ ∑ _b : Fin C.m, ENNReal.ofReal (n * (C.m * B ^ 2)) * ∑ a,
        ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
        (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
        refine Finset.sum_le_sum fun b _ => ?_
        refine (setLIntegral_mono' measurableSet_ball (hpt b)).trans ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finset_sum' _ (fun a _ => hfm b a)]
        refine mul_le_mul_right (Finset.sum_le_sum fun a _ => ?_) _
        refine le_trans (setLIntegral_le_lintegral _ _) ?_
        rw [lintegral_indicator (hWo b a).measurableSet]
        exact hE b a
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (C.m : ℝ)) (by positivity), ENNReal.ofReal_natCast, mul_assoc]

end GlobalTheory.OTY.GlueEnergy
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_energy_glued_section_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n1 C la (glue C la u) ≤ ENNReal.ofReal K * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  atlas_forward_decl GlobalTheory.OTY.GlueEnergy.energy_glue_le
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem glue_isSSec_of_holo : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type)
    [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La)
    (u : Fin C.m → V n → ℂ), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) →
    A.IsSSec (A.kap + la) (glue C la u) := by
  intro n Y _ _ _ _ _ ι La _ A C la u hu
  refine ⟨fun i => ?_, fun i j y hi hj => ?_⟩
  · have key : ∀ a, ContDiffOn ℝ ∞ (fun v => (C.chi a ((A.chart i).symm v) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
        u a (A.chart (C.idx a) ((A.chart i).symm v))) (A.chart i).target := by
      intro a v hv
      apply ContDiffAt.contDiffWithinAt
      by_cases hy : (A.chart i).symm v ∈ tsupport (C.chi a)
      · have hs := C.supp a hy
        have hovo : IsOpen (ovl A.chart i (C.idx a)) :=
          (A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source
        have hvov : v ∈ ovl A.chart i (C.idx a) := ⟨hv, hs.1⟩
        have hUo : IsOpen (ovl A.chart i (C.idx a) ∩
            (A.chart (C.idx a) ∘ (A.chart i).symm) ⁻¹' ball (C.c a) (C.r a)) :=
          (A.holo_trans i (C.idx a)).continuousOn.isOpen_inter_preimage hovo isOpen_ball
        have hvU : v ∈ ovl A.chart i (C.idx a) ∩
            (A.chart (C.idx a) ∘ (A.chart i).symm) ⁻¹' ball (C.c a) (C.r a) := ⟨hvov, hs.2⟩
        have h1 : ContDiffAt ℝ ∞ (C.chi a ∘ (A.chart i).symm) v :=
          (C.smooth a i).contDiffAt ((A.chart i).open_target.mem_nhds hv)
        have h1' : ContDiffAt ℝ ∞ (fun v => (C.chi a ((A.chart i).symm v) : ℂ)) v :=
          Complex.ofRealCLM.contDiff.contDiffAt.comp v h1
        have h2 : ContDiffAt ℝ ∞ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v :=
          hyq_contDiffAt_of_holo hovo (A.holo_g _ _ _) hvov
        have h3 : ContDiffAt ℝ ∞ (u a ∘ (A.chart (C.idx a) ∘ (A.chart i).symm)) v :=
          hyq_contDiffAt_of_holo hUo ((hu a).comp
            ((A.holo_trans i (C.idx a)).mono Set.inter_subset_left) (fun w hw => hw.2)) hvU
        exact (h1'.mul h2).mul h3
      · have hn : (tsupport (C.chi a))ᶜ ∈ 𝓝 ((A.chart i).symm v) :=
          (isClosed_tsupport _).isOpen_compl.mem_nhds hy
        have h2 : ∀ᶠ w in 𝓝 v, (A.chart i).symm w ∉ tsupport (C.chi a) :=
          ((A.chart i).continuousAt_symm hv).preimage_mem_nhds hn
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [h2] with w hw
        simp [image_eq_zero_of_notMem_tsupport hw]
    have he : (glue C la u i ∘ (A.chart i).symm) = fun v => ∑ a, (C.chi a ((A.chart i).symm v) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
        u a (A.chart (C.idx a) ((A.chart i).symm v)) := by
      funext v; simp [glue]
    rw [he]
    exact ContDiffOn.sum fun a _ => key a
  · simp only [glue]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : C.chi a y = 0
    · simp [h]
    · have hk := (C.supp a (subset_tsupport _ h)).1
      rw [A.g_cocycle (A.kap + la) i j (C.idx a) y hi hj hk]
      ring

end GlobalTheory.OTY
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSSec_glueSectionByPartition_of_holo : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → A.IsSSec (A.kap + la) (glue C la u) := by
  atlas_forward_decl GlobalTheory.OTY.glue_isSSec_of_holo
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem hormander_step : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), 0 < t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F1 : ι → Y → ℂ, A.IsSSec (A.kap + la) F1 ∧ n0 A la (F0 - F1) ≤ ENNReal.ofReal (K / t) * n1 C la F0 ∧ n1 C la F1 ≤ ENNReal.ofReal (K / t) * n1 C la F0 := by
  intro n Y _ _ _ _ _ ι La _ A C
  obtain ⟨K', hK'0, hK'⟩ := GlobalTheory.T.dbar_energy_glued_section_le n Y ι La A C
  refine ⟨max (C.m : ℝ) K', le_max_of_le_right hK'0, ?_⟩
  intro la t ht hcurv F0 hF0
  have hball : ∀ a : Fin C.m, ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball (C.c a) (C.r a)) ∧
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - F v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤
      ENNReal.ofReal t⁻¹ * ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro a
    have hsub : ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
      ball_subset_closedBall.trans (C.sub a)
    refine GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound n (C.c a) (C.r a) t (fun w => A.ph la (C.idx a) ((A.chart (C.idx a)).symm w))
      (F0 (C.idx a) ∘ (A.chart (C.idx a)).symm) ht ((A.smooth_ph la (C.idx a)).mono hsub)
      ((hF0.1 (C.idx a)).mono hsub) ?_
    intro v hv ξ
    have h := hcurv a v hv ξ
    unfold WeightedAtlas.leviAt at h
    rwa [(A.chart (C.idx a)).right_inv (hsub hv)] at h
  choose u hu hE using hball
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hE a)
  rw [← Finset.mul_sum] at hsum
  have hK : ENNReal.ofReal (max (C.m : ℝ) K' / t) =
      ENNReal.ofReal (max (C.m : ℝ) K') * ENNReal.ofReal t⁻¹ := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (le_max_of_le_right hK'0)]
  refine ⟨glue C la u, GlobalTheory.T.isSSec_glueSectionByPartition_of_holo n Y ι La A C la u hu, ?_, ?_⟩
  · have hm : (C.m : ℝ≥0∞) ≤ ENNReal.ofReal (max (C.m : ℝ) K') := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    calc n0 A la (F0 - glue C la u) ≤ _ := GlobalTheory.T.n0_sub_glue_le_card_mul_sum_lintegral n Y ι La A C la F0 u hF0 hu
      _ ≤ (C.m : ℝ≥0∞) * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr; exact hsum
      _ ≤ ENNReal.ofReal (max (C.m : ℝ) K') * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr
      _ = _ := by rw [hK, mul_assoc]
  · calc n1 C la (glue C la u) ≤ _ := hK' la F0 u hF0 hu
      _ ≤ ENNReal.ofReal K' * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr; exact hsum
      _ ≤ ENNReal.ofReal (max (C.m : ℝ) K') * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by
        gcongr; exact le_max_right _ _
      _ = _ := by rw [hK, mul_assoc]

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_hormander_iteration_step : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), 0 < t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F1 : ι → Y → ℂ, A.IsSSec (A.kap + la) F1 ∧ n0 A la (F0 - F1) ≤ ENNReal.ofReal (K / t) * n1 C la F0 ∧ n1 C la F1 ≤ ENNReal.ofReal (K / t) * n1 C la F0 := by
  atlas_forward_decl GlobalTheory.hormander_step
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.L2LimitHolomorphic

open Set

variable {n : ℕ}

theorem exists_pos_le_on_compact {W K : Set (V n)} {ρ : V n → ℝ} (hρ : ContinuousOn ρ W)
    (hpos : ∀ v ∈ W, 0 < ρ v) (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ K, c ≤ ρ v := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (hρ.mono hKW)
  exact ⟨ρ x, hpos x (hKW hx), fun v hv => hmin hv⟩

theorem lintegral_sq_le {W K : Set (V n)} {ρ : V n → ℝ} {c : ℝ} (hc : 0 < c)
    (hK : MeasurableSet K) (hKW : K ⊆ W) (hcK : ∀ v ∈ K, c ≤ ρ v) (g : V n → ℂ) :
    ∫⁻ v in K, ‖g v‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ v in W, ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) := by
  calc ∫⁻ v in K, ‖g v‖ₑ ^ 2
      ≤ ∫⁻ v in K, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) := by
        apply setLIntegral_mono' hK
        intro v hv
        rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ c⁻¹ * ρ v := by
          rw [le_inv_mul_iff₀ hc]; simpa using hcK v hv
        have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖g v‖)
        nlinarith
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ v in K, ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr

theorem integrableOn_of_limit {W K : Set (V n)} {ρ : V n → ℝ} {u : ℕ → V n → ℂ}
    {f : V n → ℂ} (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v)
    (hu : ∀ m, DifferentiableOn ℂ (u m) W) (hf : AEMeasurable f (volume.restrict W))
    (hlim : Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0))
    (hK : IsCompact K) (hKW : K ⊆ W) : IntegrableOn f K := by
  obtain ⟨c, hc, hcK⟩ := exists_pos_le_on_compact hρ hpos hK hKW
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
  have hum : IntegrableOn (u m) K := ((hu m).continuousOn.mono hKW).integrableOn_compact hK
  have hfK : AEStronglyMeasurable f (volume.restrict K) :=
    (hf.mono_measure (Measure.restrict_mono hKW le_rfl)).aestronglyMeasurable
  have hfin : ∫⁻ v in K, ‖f v - u m v‖ₑ ^ 2 < ⊤ :=
    lt_of_le_of_lt (lintegral_sq_le hc hK.measurableSet hKW hcK (fun v => f v - u m v))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hm.trans ENNReal.one_lt_top))
  have hd : IntegrableOn (fun v => f v - u m v) K := by
    refine ⟨hfK.sub hum.aestronglyMeasurable, ?_⟩
    show ∫⁻ v in K, ‖f v - u m v‖ₑ < ⊤
    have hpt : ∀ x : ℝ≥0∞, x ≤ 1 + x ^ 2 := by
      intro x
      rcases le_total x 1 with h | h
      · exact h.trans le_self_add
      · calc x = x * 1 := (mul_one x).symm
          _ ≤ x * x := by gcongr
          _ = x ^ 2 := (sq x).symm
          _ ≤ 1 + x ^ 2 := le_add_self
    calc ∫⁻ v in K, ‖f v - u m v‖ₑ ≤ ∫⁻ v in K, (1 + ‖f v - u m v‖ₑ ^ 2) :=
          lintegral_mono fun v => hpt _
      _ = volume K + ∫⁻ v in K, ‖f v - u m v‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const]; simp
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hfin⟩
  exact (hd.add hum).congr_fun (fun v _ => by simp) hK.measurableSet

theorem enorm_integral_mul_le {W : Set (V n)} (hW : IsOpen W) {ρ : V n → ℝ}
    (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v) {d h : V n → ℂ}
    (hd : AEMeasurable d (volume.restrict W)) (hh : Continuous h) :
    ‖∫ v in W, d v * h v‖ₑ ≤
      (∫⁻ v in W, ENNReal.ofReal (‖d v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ) := by
  have hρm : AEMeasurable ρ (volume.restrict W) := hρ.aemeasurable hW.measurableSet
  have hsq : AEMeasurable (fun v => Real.sqrt (ρ v)) (volume.restrict W) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hρm
  have ham : AEMeasurable (fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)))
      (volume.restrict W) := (hd.norm.mul hsq).ennreal_ofReal
  have hbm : AEMeasurable (fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)))
      (volume.restrict W) := (hh.measurable.norm.aemeasurable.div hsq).ennreal_ofReal
  have hab : EqOn (fun v => ‖d v * h v‖ₑ)
      ((fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v))) *
        fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v))) W := by
    intro v hv
    have hs : 0 < Real.sqrt (ρ v) := Real.sqrt_pos.2 (hpos v hv)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, norm_mul]
    congr 1
    field_simp
  have ha2 : EqOn (fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)) ^ (2 : ℝ))
      (fun v => ENNReal.ofReal (‖d v‖ ^ 2 * ρ v)) W := by
    intro v hv
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, mul_pow,
      Real.sq_sqrt (hpos v hv).le]
  have hb2 : EqOn (fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)) ^ (2 : ℝ))
      (fun v => ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) W := by
    intro v hv
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, div_pow,
      Real.sq_sqrt (hpos v hv).le]
  calc ‖∫ v in W, d v * h v‖ₑ ≤ ∫⁻ v in W, ‖d v * h v‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ v in W, ((fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v))) *
          fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v))) v :=
        setLIntegral_congr_fun hW.measurableSet hab
    _ ≤ (∫⁻ v in W, ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ v in W, ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two ham hbm
    _ = _ := by
        rw [setLIntegral_congr_fun hW.measurableSet ha2,
          setLIntegral_congr_fun hW.measurableSet hb2]

theorem integral_mul_eq_zero {W : Set (V n)} (hW : IsOpen W) {ρ : V n → ℝ}
    (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v) {u : ℕ → V n → ℂ} {f : V n → ℂ}
    (hu : ∀ m, DifferentiableOn ℂ (u m) W) (hf : AEMeasurable f (volume.restrict W))
    (hlim : Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0))
    {h : V n → ℂ} (hhc : Continuous h) (hhs : HasCompactSupport h) (hsupp : tsupport h ⊆ W)
    (h0 : ∀ m, ∫ v in W, u m v * h v = 0) : ∫ v in W, f v * h v = 0 := by
  have hkc : Continuous fun v => ‖h v‖ ^ 2 / ρ v := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ W
    · exact (hhc.norm.pow 2).continuousAt.div (hρ.continuousAt (hW.mem_nhds hx))
        (hpos x hx).ne'
    · have hx' : x ∉ tsupport h := fun h' => hx (hsupp h')
      have hev : (fun v => ‖h v‖ ^ 2 / ρ v) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hx')] with v hv
        simp [hv]
      exact continuousAt_const.congr hev.symm
  have hks : HasCompactSupport fun v => ‖h v‖ ^ 2 / ρ v := by
    refine hhs.mono fun x hx => ?_
    intro h1
    apply hx
    simp [h1]
  have hH : ∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v) < ⊤ :=
    lt_of_le_of_lt (setLIntegral_le_lintegral _ _)
      (hkc.integrable_of_hasCompactSupport hks).lintegral_lt_top
  by_cases hfi : Integrable (fun v => f v * h v) (volume.restrict W)
  swap
  · exact integral_undef hfi
  have key : ∀ m, ‖∫ v in W, f v * h v‖ₑ ≤
      (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ) := by
    intro m
    have hUi : Integrable (fun v => u m v * h v) (volume.restrict W) := by
      have h1 : IntegrableOn (fun v => u m v * h v) (tsupport h) :=
        (((hu m).continuousOn.mono hsupp).mul hhc.continuousOn).integrableOn_compact hhs
      exact h1.of_forall_sdiff_eq_zero hW.measurableSet fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx.2]
    have heq : ∫ v in W, f v * h v = ∫ v in W, (f v - u m v) * h v := by
      simp_rw [sub_mul]
      rw [integral_sub hfi hUi, h0 m, sub_zero]
    rw [heq]
    exact enorm_integral_mul_le hW hρ hpos
      (hf.sub ((hu m).continuousOn.aemeasurable hW.measurableSet)) hhc
  have hT : Tendsto (fun m =>
      (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m =>
        (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
      simpa [Function.comp_def] using this
    have := ENNReal.Tendsto.mul_const h1
      (b := (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ))
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hH.ne))
    simpa using this
  have hle := ge_of_tendsto' hT key
  exact enorm_eq_zero.mp (le_antisymm hle bot_le)

theorem tsupport_dbarDir_subset (g : V n → ℂ) (w : V n) :
    tsupport (fun z => C.dbarDir g z w) ⊆ tsupport g := by
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  refine Function.mem_support.2 fun h0 => Function.mem_support.1 hz ?_
  simp [C.dbarDir, h0]

theorem exists_holo_ae_eq : ∀ (n : ℕ) (W : Set (V n)) (ρ : V n → ℝ) (u : ℕ → V n → ℂ) (f : V n → ℂ), IsOpen W → ContinuousOn ρ W → (∀ v ∈ W, 0 < ρ v) → (∀ m, DifferentiableOn ℂ (u m) W) → AEMeasurable f (volume.restrict W) → Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0) → ∃ g : V n → ℂ, DifferentiableOn ℂ g W ∧ g =ᵐ[volume.restrict W] f := by
  intro n W ρ u f hW hρ hpos hu hf hlim
  have hwh : C.WeakHolo W f := by
    refine ⟨(locallyIntegrableOn_iff hW.isLocallyClosed).2 fun K hKW hK =>
      integrableOn_of_limit hρ hpos hu hf hlim hK hKW, ?_⟩
    intro g hg w
    obtain ⟨hhc, hhs⟩ := C.dbarDir_continuous_hasCompactSupport hg.1 hg.2.1 w
    exact integral_mul_eq_zero hW hρ hpos hu hf hlim hhc hhs
      ((tsupport_dbarDir_subset g w).trans hg.2.2)
      (fun m => (C.holoWeak n W (u m) hW (hu m)).2 g hg w)
  obtain ⟨U, hU, hfU⟩ := C.reg n W f hW hwh
  exact ⟨U, hU, hfU.symm⟩

end GlobalTheory.L2LimitHolomorphic
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_differentiableOn_ae_eq_of_weighted_L2_limit : ∀ (n : ℕ) (W : Set (V n)) (ρ : V n → ℝ) (u : ℕ → V n → ℂ) (f : V n → ℂ), IsOpen W → ContinuousOn ρ W → (∀ v ∈ W, 0 < ρ v) → (∀ m, DifferentiableOn ℂ (u m) W) → AEMeasurable f (volume.restrict W) → Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0) → ∃ g : V n → ℂ, DifferentiableOn ℂ g W ∧ g =ᵐ[volume.restrict W] f := by
  atlas_forward_decl GlobalTheory.L2LimitHolomorphic.exists_holo_ae_eq
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.L2Limit

theorem norm_sub_sq_le (a : ℕ → ℂ) (m k : ℕ) :
    ‖a m - a (k + m)‖ ^ 2 ≤ 2 / 2 ^ m *
      ∑ i ∈ Finset.range k, 2 ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 := by
  have htel : a m - a (k + m) = ∑ i ∈ Finset.range k, (a (i + m) - a (i + m + 1)) := by
    have := Finset.sum_range_sub' (fun i => a (i + m)) k
    simp only [zero_add] at this
    rw [← this]; exact Finset.sum_congr rfl fun i _ => by rw [add_right_comm]
  have h1 : ‖a m - a (k + m)‖ ≤ ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ := by
    rw [htel]; exact norm_sum_le _ _
  have hg : ∀ i ∈ Finset.range k, (0:ℝ) < (1/2) ^ (i + m) := fun i _ => by positivity
  have h2 := Finset.sq_sum_div_le_sum_sq_div (Finset.range k)
    (fun i => ‖a (i + m) - a (i + m + 1)‖) hg
  have hsg : ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) ≤ 2 / 2 ^ m := by
    have : ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) =
        (1/2) ^ m * ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
    rw [this]
    have := sum_geometric_two_le k
    have h2m : (0:ℝ) < (1/2) ^ m := by positivity
    calc (1/2:ℝ) ^ m * ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i ≤ (1/2) ^ m * 2 :=
          mul_le_mul_of_nonneg_left this h2m.le
      _ = 2 / 2 ^ m := by rw [one_div_pow]; ring
  have hsum_pos : 0 < ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.sum_pos (fun i hi => hg i hi) ⟨0, by simp [h]⟩)
  rcases hsum_pos with hpos | hk
  · have h3 : (∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖) ^ 2 ≤
        (∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m)) *
          ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ ^ 2 / (1/2) ^ (i + m) := by
      rwa [div_le_iff₀ hpos, mul_comm] at h2
    have h4 : ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ ^ 2 / (1/2) ^ (i + m) =
        ∑ i ∈ Finset.range k, 2 ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_div_pow, div_div_eq_mul_div, div_one, mul_comm]
    rw [h4] at h3
    have hn : 0 ≤ ∑ i ∈ Finset.range k, (2:ℝ) ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    calc ‖a m - a (k + m)‖ ^ 2 ≤ (∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_right hsg hn
  · subst hk; simp

theorem tendsto_of_summable (a : ℕ → ℂ)
    (hs : Summable (fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2)) :
    ∃ L, Tendsto a atTop (𝓝 L) ∧ ∀ m, ‖a m - L‖ ^ 2 ≤
      2 / 2 ^ m * ∑' k, (2:ℝ) ^ (k + m) * ‖a (k + m) - a (k + m + 1)‖ ^ 2 := by
  set c : ℕ → ℝ := fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2 with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  have hfin : ∀ m k, ‖a m - a (k + m)‖ ^ 2 ≤ 2 / 2 ^ m * ∑' i, c (i + m) := by
    intro m k
    refine (norm_sub_sq_le a m k).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Summable.sum_le_tsum _ (fun i _ => hc0 _) ((summable_nat_add_iff m).mpr hs)
  have htail := tendsto_sum_nat_add c
  have hcau : CauchySeq a := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev : ∀ᶠ m in atTop, 2 * ∑' i, c (i + m) < ε ^ 2 := by
      have := htail.const_mul 2
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm⟩ := hev.exists_forall_of_atTop
    refine ⟨m, fun N hN => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, N = k + m := ⟨N - m, by omega⟩
    have h1 := hfin m k
    have h2 : 2 / 2 ^ m * ∑' i, c (i + m) ≤ 2 * ∑' i, c (i + m) := by
      refine mul_le_mul_of_nonneg_right ?_ (tsum_nonneg fun i => hc0 _)
      exact div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
    have h3 : dist (a (k + m)) (a m) ^ 2 < ε ^ 2 := by
      rw [dist_eq_norm, norm_sub_rev]; linarith [hm m le_rfl]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, hL, fun m => ?_⟩
  have hlim : Tendsto (fun k => ‖a m - a (k + m)‖ ^ 2) atTop (𝓝 (‖a m - L‖ ^ 2)) :=
    (((hL.comp (tendsto_add_atTop_nat m)).const_sub (a m)).norm).pow 2
  exact le_of_tendsto' hlim fun k => hfin m k

end GlobalTheory.L2Limit

namespace GlobalTheory.L2Limit

section
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

open Classical in

noncomputable def limSec (F : ℕ → ι → Y → ℂ) : ι → Y → ℂ := fun i y =>
  if ∃ c, Tendsto (fun m => F m i y) atTop (𝓝 c) then limUnder atTop (fun m => F m i y) else 0

theorem limSec_eq (F : ℕ → ι → Y → ℂ) (i : ι) (y : Y) {c : ℂ}
    (h : Tendsto (fun m => F m i y) atTop (𝓝 c)) : limSec F i y = c := by
  unfold limSec; rw [if_pos ⟨c, h⟩]; exact h.limUnder_eq

theorem limSec_trans (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (i j : ι) (y : Y) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : limSec F i y = A.g la i j y * limSec F j y := by
  have hg := A.g_ne la i j y hi hj
  have hseq : (fun m => F m i y) = fun m => A.g la i j y * F m j y :=
    funext fun m => (hF m).2 i j y hi hj
  by_cases hc : ∃ c, Tendsto (fun m => F m j y) atTop (𝓝 c)
  · obtain ⟨c, hc⟩ := hc
    rw [limSec_eq F j y hc, limSec_eq F i y (by rw [hseq]; exact hc.const_mul _)]
  · have hc' : ¬ ∃ c, Tendsto (fun m => F m i y) atTop (𝓝 c) := by
      rintro ⟨c, hc'⟩
      apply hc
      refine ⟨(A.g la i j y)⁻¹ * c, ?_⟩
      have h2 : Tendsto (fun m => A.g la i j y * F m j y) atTop (𝓝 c) := by
        rw [← hseq]; exact hc'
      have := h2.const_mul (A.g la i j y)⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hg] using this
    unfold limSec
    rw [if_neg hc, if_neg hc', mul_zero]

theorem limSec_aemeas (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (i : ι) :
    AEMeasurable (limSec F i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target) := by
  classical
  set T := (A.chart i).target with hTdef
  have hT : MeasurableSet T := (A.chart i).open_target.measurableSet
  let G : ℕ → V n → ℂ := fun m => T.piecewise (F m i ∘ (A.chart i).symm) 0
  have hG : ∀ m, StronglyMeasurable (G m) := fun m =>
    (ContinuousOn.measurable_piecewise ((hF m).1 i).continuousOn continuousOn_const
      hT).stronglyMeasurable
  have hS := StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hG
  have hL := StronglyMeasurable.limUnder (l := atTop) hG
  have hmeas : StronglyMeasurable ({v | ∃ c, Tendsto (fun m => G m v) atTop (𝓝 c)}.piecewise
      (fun v => limUnder atTop (fun m => G m v)) (fun _ => (0:ℂ))) :=
    StronglyMeasurable.piecewise hS hL stronglyMeasurable_const
  refine hmeas.measurable.aemeasurable.congr ?_
  refine (ae_restrict_iff' hT).mpr (Eventually.of_forall fun v hv => ?_)
  have hGv : (fun m => G m v) = fun m => F m i ((A.chart i).symm v) :=
    funext fun m => by simp only [G, Set.piecewise_eq_of_mem _ _ _ hv, Function.comp_apply]
  simp only [Set.piecewise, Set.mem_setOf_eq, hGv, Function.comp_apply, limSec]

theorem measurable_step (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (j : ℕ) :
    Measurable (fun y => ENNReal.ofReal (A.nsq la (F j - F (j + 1)) y)) :=
  ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq la (F j - F (j + 1)) (fun i k y hi hk => by
      simp only [Pi.sub_apply]; rw [(hF j).2 i k y hi hk, (hF (j + 1)).2 i k y hi hk]; ring)
    (fun i => ((hF j).1 i).continuousOn.sub ((hF (j + 1)).1 i).continuousOn)).measurable

end

theorem exists_l2_limit : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (F : ℕ → ι → Y → ℂ) (K : ℝ), 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → ∃ f : ι → Y → ℂ, (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g (A.kap + la) i j y * f j y) ∧ (∀ i, AEMeasurable (f i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target)) ∧ ∀ m, n0 A la (F m - f) ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
  intro n Y _ _ _ _ _ ι La _ A la F K hK hF hn
  set L := A.kap + la with hLdef
  set e : ℕ → Y → ℝ≥0∞ := fun j y => ENNReal.ofReal (A.nsq L (F j - F (j + 1)) y) with he_def
  have he : ∀ j, Measurable (e j) := measurable_step A L F hF
  have hint : ∀ j, ∫⁻ y, e j y ∂A.mu ≤ ENNReal.ofReal (K / 4 ^ j) := hn
  set S : ℕ → Y → ℝ≥0∞ := fun m y => ∑' k, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y with hSdef
  have hSm : ∀ m, Measurable (S m) := fun m =>
    Measurable.ennreal_tsum fun k => measurable_const.mul (he _)
  have hSint : ∀ m, ∫⁻ y, S m y ∂A.mu ≤ ENNReal.ofReal (K / 2 ^ m * 2) := by
    intro m
    show ∫⁻ y, ∑' k, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y ∂A.mu ≤ _
    rw [lintegral_tsum fun k => ((he (k + m)).const_mul _).aemeasurable]
    calc ∑' k, ∫⁻ y, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y ∂A.mu
        = ∑' k, ENNReal.ofReal (2 ^ (k + m)) * ∫⁻ y, e (k + m) y ∂A.mu := by
          congr 1; ext k; exact lintegral_const_mul _ (he _)
      _ ≤ ∑' k, ENNReal.ofReal (2 ^ (k + m)) * ENNReal.ofReal (K / 4 ^ (k + m)) :=
          ENNReal.tsum_le_tsum fun k => by gcongr; exact hint _
      _ = ∑' k, ENNReal.ofReal (K / 2 ^ m * (1 / 2) ^ k) := by
          congr 1; ext k
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (4:ℝ) ^ (k + m) = 2 ^ (k + m) * 2 ^ (k + m) by rw [← mul_pow]; norm_num]
          rw [pow_add, one_div_pow]; field_simp
      _ = ENNReal.ofReal (∑' k, K / 2 ^ m * (1 / 2) ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            (summable_geometric_two.mul_left _)).symm
      _ = ENNReal.ofReal (K / 2 ^ m * 2) := by rw [tsum_mul_left, tsum_geometric_two]
  have hfin : ∀ᵐ y ∂A.mu, S 0 y < ⊤ :=
    ae_lt_top (hSm 0) ((hSint 0).trans_lt ENNReal.ofReal_lt_top).ne
  have hpt : ∀ m, ∀ᵐ y ∂A.mu, ENNReal.ofReal (A.nsq L (F m - limSec F) y) ≤
      ENNReal.ofReal (2 / 2 ^ m) * S m y := by
    intro m
    filter_upwards [hfin] with y hy
    set p := A.pick y
    set E := Real.exp (-A.ph L p y) with hE
    have hEpos : 0 < E := Real.exp_pos _
    set a : ℕ → ℂ := fun j => F j p y with ha
    have he_eq : ∀ j, e j y = ENNReal.ofReal (‖a j - a (j + 1)‖ ^ 2 * E) := fun j => rfl
    set b : ℕ → ℝ := fun k => 2 ^ k * (‖a k - a (k + 1)‖ ^ 2 * E) with hb_def
    have hb0 : ∀ k, 0 ≤ b k := fun k => by positivity
    have hSb : ∀ m', S m' y = ∑' k, ENNReal.ofReal (b (k + m')) := by
      intro m'
      simp only [hSdef, he_eq]
      congr 1; ext k
      rw [← ENNReal.ofReal_mul (by positivity)]
    have hb : Summable b := by
      have h0 := hSb 0
      simp only [add_zero] at h0
      have hs := ENNReal.summable_toReal (h0 ▸ hy.ne)
      refine hs.congr fun k => ?_
      exact ENNReal.toReal_ofReal (hb0 k)
    have hb' : Summable (fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2) := by
      refine (hb.div_const E).congr fun k => ?_
      simp only [hb_def]; field_simp
    obtain ⟨Lm, hLm, hbd⟩ := tendsto_of_summable a hb'
    have hf : limSec F p y = Lm := limSec_eq F p y hLm
    have hnsq : A.nsq L (F m - limSec F) y = ‖a m - Lm‖ ^ 2 * E := by
      show ‖F m p y - limSec F p y‖ ^ 2 * E = _
      rw [hf]
    rw [hnsq, hSb m, ← ENNReal.ofReal_tsum_of_nonneg (fun k => hb0 _)
      ((summable_nat_add_iff m).mpr hb), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right (hbd m) hEpos.le
    calc ‖a m - Lm‖ ^ 2 * E
        ≤ 2 / 2 ^ m * (∑' k, (2:ℝ) ^ (k + m) * ‖a (k + m) - a (k + m + 1)‖ ^ 2) * E := this
      _ = 2 / 2 ^ m * ∑' k, b (k + m) := by
          rw [mul_assoc, ← tsum_mul_right]
          congr 2; ext k; simp only [hb_def]; ring
  refine ⟨limSec F, fun i j y hi hj => limSec_trans A L F hF i j y hi hj,
    fun i => limSec_aemeas A L F hF i, fun m => ?_⟩
  calc n0 A la (F m - limSec F) = ∫⁻ y, ENNReal.ofReal (A.nsq L (F m - limSec F) y) ∂A.mu := rfl
    _ ≤ ∫⁻ y, ENNReal.ofReal (2 / 2 ^ m) * S m y ∂A.mu := lintegral_mono_ae (hpt m)
    _ = ENNReal.ofReal (2 / 2 ^ m) * ∫⁻ y, S m y ∂A.mu := lintegral_const_mul _ (hSm m)
    _ ≤ ENNReal.ofReal (2 / 2 ^ m) * ENNReal.ofReal (K / 2 ^ m * 2) := by gcongr; exact hSint m
    _ = ENNReal.ofReal (4 * K / 4 ^ m) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show (4:ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
      field_simp; ring

end GlobalTheory.L2Limit
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_series_sections_l2_limit : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (F : ℕ → ι → Y → ℂ) (K : ℝ), 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → ∃ f : ι → Y → ℂ, (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g (A.kap + la) i j y * f j y) ∧ (∀ i, AEMeasurable (f i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target)) ∧ ∀ m, n0 A la (F m - f) ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
  atlas_forward_decl GlobalTheory.L2Limit.exists_l2_limit
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.AeHoloGlue

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem mu_ne_zero_of_open (A : WeightedAtlas n Y ι La) {O : Set Y} (hO : IsOpen O)
    (hne : O.Nonempty) : A.mu O ≠ 0 := by
  obtain ⟨y, hy⟩ := hne
  have hW : IsOpen (O ∩ (A.chart (A.pick y)).source) := hO.inter (A.chart (A.pick y)).open_source
  have hWs : O ∩ (A.chart (A.pick y)).source ⊆ (A.chart (A.pick y)).source := Set.inter_subset_right
  have hS : IsOpen (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)) :=
    (A.chart (A.pick y)).isOpen_image_of_subset_source hW hWs
  have hSne : (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ ⟨hy, A.mem_pick y⟩⟩
  have hSt : A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source) ⊆ (A.chart (A.pick y)).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart (A.pick y)).map_source hx.2
  intro h0
  have h1 : A.mu (O ∩ (A.chart (A.pick y)).source) = 0 := measure_mono_null Set.inter_subset_left h0
  rw [A.mu_chart _ _ hW.measurableSet hWs] at h1
  have hc : ContinuousOn (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) ((A.chart (A.pick y)).symm v))))
      (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)) := by
    have := (A.smooth_ph A.kap (A.pick y)).continuousOn.mono hSt
    exact ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn this)
  rw [lintegral_eq_zero_iff' (hc.aemeasurable hS.measurableSet)] at h1
  have h3 := ae_iff.mp h1
  have hu : {v | ¬ (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) ((A.chart (A.pick y)).symm v)))) v
      = (0 : V n → ℝ≥0∞) v} = Set.univ := by
    ext v; simp [ENNReal.ofReal_eq_zero, Real.exp_pos]
  rw [hu, Measure.restrict_apply_univ] at h3
  exact hS.measure_ne_zero volume hSne h3

theorem exists_null (A : WeightedAtlas n Y ι La) (i : ι) (c : V n) (r : ℝ) (u : V n → ℂ)
    (f : Y → ℂ) (h : u =ᵐ[volume.restrict (ball c r)] f ∘ (A.chart i).symm) :
    ∃ M : Set Y, A.mu M = 0 ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball c r → y ∉ M →
      u (A.chart i y) = f y := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at h
  obtain ⟨T, hET, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  classical
  have hφ : Measurable ((A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n))) :=
    ContinuousOn.measurable_piecewise (A.chart i).continuousOn continuousOn_const
      (A.chart i).open_source.measurableSet
  refine ⟨(A.chart i).source ∩ (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) ⁻¹' T,
    ?_, ?_⟩
  · have hm : MeasurableSet ((A.chart i).source ∩
        (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) ⁻¹' T) :=
      (A.chart i).open_source.measurableSet.inter (hφ hTm)
    rw [A.mu_chart i _ hm Set.inter_subset_left]
    refine le_antisymm ?_ (by simp)
    calc _ ≤ ∫⁻ v in T, ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by
          apply lintegral_mono_set
          rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
          have : (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) x = A.chart i x :=
            Set.piecewise_eq_of_mem _ _ _ hx1
          simpa [this] using hx2
      _ = 0 := setLIntegral_measure_zero _ _ hT0
  · intro y hy hb hM
    by_contra hne
    apply hM
    refine ⟨hy, ?_⟩
    show (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) y ∈ T
    rw [Set.piecewise_eq_of_mem _ _ _ hy]
    apply hET
    simp only [Set.mem_setOf_eq, _root_.not_imp]
    refine ⟨hb, ?_⟩
    simpa [Function.comp, (A.chart i).left_inv hy] using hne

theorem continuousOn_g (A : WeightedAtlas n Y ι La) (la : La) (i j : ι) :
    ContinuousOn (A.g la i j) ((A.chart i).source ∩ (A.chart j).source) := by
  have h1 : ContinuousOn (A.g la i j ∘ (A.chart i).symm ∘ A.chart i)
      ((A.chart i).source ∩ (A.chart j).source) := by
    refine (A.holo_g la i j).continuousOn.comp ((A.chart i).continuousOn.mono Set.inter_subset_left) ?_
    intro y hy
    exact ⟨(A.chart i).map_source hy.1, by simpa [(A.chart i).left_inv hy.1] using hy.2⟩
  refine h1.congr ?_
  intro y hy
  simp [(A.chart i).left_inv hy.1]

theorem main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La),
    ∀ (C : Cover A) (la : La) (f : ι → Y → ℂ) (u : Fin C.m → V n → ℂ),
    (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g la i j y * f j y) →
    (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) →
    (∀ a, u a =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm) →
    ∃ F : ι → Y → ℂ, A.IsSec la F ∧ ∀ᵐ y ∂A.mu, F (A.pick y) y = f (A.pick y) y := by
  intro n Y _ _ _ _ _ ι La _ A C la f u hf hu hae
  classical

  have hBo : ∀ a, IsOpen ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) :=
    fun a => (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hcov : ∀ y, ∃ a, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) := by
    intro y
    by_contra hno
    push_neg at hno
    have h0 : ∀ a, C.chi a y = 0 := fun a => by
      by_contra hne
      exact hno a (C.supp a (subset_tsupport _ hne))
    have := C.sum_one y
    simp [h0] at this
  choose M hM0 hM using fun a => exists_null A (C.idx a) (C.c a) (C.r a) (u a) (f (C.idx a)) (hae a)
  have hM0' : A.mu (⋃ a, M a) = 0 := measure_iUnion_null hM0

  have hoff : ∀ a y, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) →
      y ∉ ⋃ a, M a → u a (A.chart (C.idx a) y) = f (C.idx a) y := fun a y hy hn =>
    hM a y hy.1 hy.2 (fun h => hn (Set.mem_iUnion.mpr ⟨a, h⟩))
  have hcu : ∀ a, ContinuousOn (fun y => u a (A.chart (C.idx a) y))
      ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) := fun a =>
    (hu a).continuousOn.comp ((A.chart (C.idx a)).continuousOn.mono Set.inter_subset_left)
      (fun y hy => hy.2)

  have hagree : ∀ a b y, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) →
      y ∈ (A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' ball (C.c b) (C.r b) →
      u a (A.chart (C.idx a) y) = A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y) := by
    intro a b y hya hyb
    set D := ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) ∩
      ((A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' ball (C.c b) (C.r b)) with hD
    have hcont : ContinuousOn (fun y => u a (A.chart (C.idx a) y) -
        A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y)) D :=
      ((hcu a).mono Set.inter_subset_left).sub
        (((continuousOn_g A la (C.idx a) (C.idx b)).mono
          (fun z hz => ⟨hz.1.1, hz.2.1⟩)).mul ((hcu b).mono Set.inter_subset_right))
    have hop := hcont.isOpen_inter_preimage ((hBo a).inter (hBo b)) (isOpen_compl_singleton (x := (0 : ℂ)))
    have hsub : D ∩ (fun y => u a (A.chart (C.idx a) y) -
        A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y)) ⁻¹' {0}ᶜ ⊆ ⋃ a, M a := by
      intro z ⟨hz, hz0⟩
      by_contra hn
      apply hz0
      simp only [Set.mem_singleton_iff]
      rw [hoff a z hz.1 hn, hoff b z hz.2 hn, hf _ _ z hz.1.1 hz.2.1]
      ring
    by_contra hne
    exact mu_ne_zero_of_open A hop ⟨y, ⟨hya, hyb⟩, by simpa [sub_eq_zero] using hne⟩
      (measure_mono_null hsub hM0')
  choose α hα using hcov
  refine ⟨fun i y => A.g la i (C.idx (α y)) y * u (α y) (A.chart (C.idx (α y)) y), ⟨?_, ?_⟩, ?_⟩
  ·
    intro i v hv
    have hvs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hv.1
    set a0 := α ((A.chart i).symm v)
    have hO : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0))) :=
      (A.chart i).isOpen_inter_preimage_symm (hBo a0)
    have hvO : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0)) :=
      ⟨hv.1, hα _⟩
    have hOovl : (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0)) ⊆
        ovl A.chart i (C.idx a0) := fun w hw => ⟨hw.1, hw.2.1⟩
    have hG : DifferentiableOn ℂ (fun w => A.g la i (C.idx a0) ((A.chart i).symm w) *
        u a0 ((A.chart (C.idx a0) ∘ (A.chart i).symm) w))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
          ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0))) :=
      ((A.holo_g la i (C.idx a0)).mono hOovl).mul
        ((hu a0).comp ((A.holo_trans i (C.idx a0)).mono hOovl) (fun w hw => hw.2.2))
    have hloc : (fun w => A.g la i (C.idx a0) ((A.chart i).symm w) *
        u a0 ((A.chart (C.idx a0) ∘ (A.chart i).symm) w)) =ᶠ[𝓝 v]
        ((fun i y => A.g la i (C.idx (α y)) y * u (α y) (A.chart (C.idx (α y)) y)) i ∘
          (A.chart i).symm) := by
      filter_upwards [hO.mem_nhds hvO] with w hw
      have hws : (A.chart i).symm w ∈ (A.chart i).source := (A.chart i).map_target hw.1
      simp only [Function.comp]
      rw [hagree (α ((A.chart i).symm w)) a0 _ (hα _) hw.2, ← mul_assoc,
        ← A.g_cocycle la i _ _ _ hws (hα _).1 hw.2.1]
    exact ((hG.differentiableAt (hO.mem_nhds hvO)).congr_of_eventuallyEq hloc.symm).differentiableWithinAt
  ·
    intro i j y _ hi hj
    simp only
    rw [A.g_cocycle la i j (C.idx (α y)) y hi hj (hα y).1]
    ring
  ·
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hM0'] with y hy
    rw [hoff _ y (hα y) hy, ← hf _ _ y (A.mem_pick y) (hα y).1]

end GlobalTheory.AeHoloGlue
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holo_section_ae_eq_of_ball_cover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (f : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g la i j y * f j y) → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → (∀ a, u a =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm) → ∃ F : ι → Y → ℂ, A.IsSec la F ∧ ∀ᵐ y ∂A.mu, F (A.pick y) y = f (A.pick y) y := by
  atlas_forward_decl GlobalTheory.AeHoloGlue.main
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem ofReal_sq_sub_mul_le (x y z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ENNReal.ofReal (‖x - y‖ ^ 2 * ρ) ≤
      2 * ENNReal.ofReal (‖z - x‖ ^ 2 * ρ) + 2 * ENNReal.ofReal (‖z - y‖ ^ 2 * ρ) := by
  have h1 : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
    calc ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; ring
      _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
      _ = ‖z - x‖ + ‖z - y‖ := add_comm _ _
  have h2 : ‖x - y‖ ^ 2 ≤ 2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 := by
    nlinarith [norm_nonneg (x - y), norm_nonneg (z - x), norm_nonneg (z - y),
      sq_nonneg (‖z - x‖ - ‖z - y‖)]
  have h3 : ‖x - y‖ ^ 2 * ρ ≤ 2 * (‖z - x‖ ^ 2 * ρ) + 2 * (‖z - y‖ ^ 2 * ρ) := by
    have := mul_le_mul_of_nonneg_right h2 hρ
    linarith
  calc ENNReal.ofReal (‖x - y‖ ^ 2 * ρ)
      ≤ ENNReal.ofReal (2 * (‖z - x‖ ^ 2 * ρ) + 2 * (‖z - y‖ ^ 2 * ρ)) := ENNReal.ofReal_le_ofReal h3
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      simp

theorem exists_isSec_of_rapid_cauchy : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (t K : ℝ) (F : ℕ → ι → Y → ℂ), 0 < t → CurvGe C la t → 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → Tendsto (fun m => n1 C la (F m)) atTop (𝓝 0) → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + la) G ∧ n0 A la (F 0 - G) ≤ ENNReal.ofReal (4 * K) := by
  intro n Y _ _ _ _ _ ι La _ A C la t K F ht hcurv hK hF hcau hn1
  obtain ⟨f, hfc, hfm, hfn⟩ := GlobalTheory.T.geometric_series_sections_l2_limit n Y ι La A la F K hK hF hcau

  have hWsub : ∀ a, ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
    fun a => ball_subset_closedBall.trans (C.sub a)

  have hH : ∀ m a, ∃ u : V n → ℂ, DifferentiableOn ℂ u (ball (C.c a) (C.r a)) ∧
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤ ENNReal.ofReal t⁻¹ * n1 C la (F m) := by
    intro m a
    obtain ⟨u, hu, hle⟩ := GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound n (C.c a) (C.r a) t
      (fun w => A.ph la (C.idx a) ((A.chart (C.idx a)).symm w)) (F m (C.idx a) ∘ (A.chart (C.idx a)).symm) ht
      ((A.smooth_ph la (C.idx a)).mono (hWsub a)) (((hF m).1 (C.idx a)).mono (hWsub a))
      (by
        intro v hv ξ
        have := hcurv a v hv ξ
        simp only [WeightedAtlas.leviAt] at this
        rwa [(A.chart (C.idx a)).right_inv (hWsub a hv)] at this)
    refine ⟨u, hu, hle.trans ?_⟩
    gcongr
    unfold n1
    exact Finset.single_le_sum (f := fun a => ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
      ((∑ j, ‖wdb n j (F m (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) (fun _ _ => bot_le) (Finset.mem_univ a)
  choose u hu hule using hH

  have hD : ∀ m a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) -
      f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
      ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
    intro m a
    have e := GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx a) (ball (C.c a) (C.r a)) (F m - f) measurableSet_ball (hWsub a)
      (by
        intro y hy _
        simp only [Pi.sub_apply]
        rw [(hF m).2 _ _ _ (A.mem_pick y) hy, hfc _ _ _ (A.mem_pick y) hy]
        ring)
      (((((hF m).1 (C.idx a)).continuousOn.aemeasurable (A.chart (C.idx a)).open_target.measurableSet).sub
        (hfm (C.idx a))).mono_measure (Measure.restrict_mono (hWsub a) le_rfl))
    refine le_trans (le_of_eq e.symm) ?_
    exact (setLIntegral_le_lintegral _ _).trans (hfn m)
  have hT : Tendsto (fun m : ℕ => 2 * ENNReal.ofReal (4 * K / 4 ^ m) +
      2 * (ENNReal.ofReal t⁻¹ * n1 C la (F m))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ENNReal.ofReal (4 * K / 4 ^ m)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal
        (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
    have h2 : Tendsto (fun m => ENNReal.ofReal t⁻¹ * n1 C la (F m)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hn1 (Or.inr ENNReal.ofReal_ne_top)
    simpa using (ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofNat_ne_top)).add
      (ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofNat_ne_top))

  have hG : ∀ a, ∃ g : V n → ℂ, DifferentiableOn ℂ g (ball (C.c a) (C.r a)) ∧
      g =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm := by
    intro a
    have hρ : ContinuousOn (fun v => Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
        (ball (C.c a) (C.r a)) :=
      Real.continuous_exp.comp_continuousOn
        (((A.smooth_ph la (C.idx a)).continuousOn.mono (hWsub a)).neg)
    refine GlobalTheory.T.exists_differentiableOn_ae_eq_of_weighted_L2_limit n (ball (C.c a) (C.r a)) _ (fun m => u m a)
      (f (C.idx a) ∘ (A.chart (C.idx a)).symm) isOpen_ball hρ (fun v _ => Real.exp_pos _)
      (fun m => hu m a) ((hfm (C.idx a)).mono_measure (Measure.restrict_mono (hWsub a) le_rfl)) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le) ?_
    intro m
    have hY : AEMeasurable (fun v => 2 * ENNReal.ofReal
        (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))))
        (volume.restrict (ball (C.c a) (C.r a))) := by
      refine AEMeasurable.const_mul ?_ _
      refine ContinuousOn.aemeasurable ?_ measurableSet_ball
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.mul ?_ hρ
      refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.norm ?_
      exact ((((hF m).1 (C.idx a)).continuousOn.mono (hWsub a))).sub (hu m a).continuousOn
    calc ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖(f (C.idx a) ∘ (A.chart (C.idx a)).symm) v - u m a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
        ≤ ∫⁻ v in ball (C.c a) (C.r a), (2 * ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) +
          2 * ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) :=
          lintegral_mono (fun v => ofReal_sq_sub_mul_le _ _ _ _ (Real.exp_pos _).le)
      _ = 2 * (∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) +
          2 * (∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) := by
          rw [lintegral_add_right' _ hY, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      _ ≤ 2 * ENNReal.ofReal (4 * K / 4 ^ m) + 2 * (ENNReal.ofReal t⁻¹ * n1 C la (F m)) := by
          gcongr
          · exact hD m a
          · exact hule m a
  choose g hg hgae using hG
  obtain ⟨G, hGs, hGae⟩ := GlobalTheory.T.exists_holo_section_ae_eq_of_ball_cover n Y ι La A C (A.kap + la) f g hfc hg hgae
  refine ⟨G, hGs, ?_⟩
  have e : n0 A la (F 0 - G) = n0 A la (F 0 - f) := by
    unfold n0
    apply lintegral_congr_ae
    filter_upwards [hGae] with y hy
    simp only [WeightedAtlas.nsq, Pi.sub_apply, hy]
  rw [e]
  simpa using hfn 0

end GlobalTheory.OTY
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphicSection_of_rapid_cauchy_dbar : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (t K : ℝ) (F : ℕ → ι → Y → ℂ), 0 < t → CurvGe C la t → 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → Tendsto (fun m => n1 C la (F m)) atTop (𝓝 0) → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + la) G ∧ n0 A la (F 0 - G) ≤ ENNReal.ofReal (4 * K) := by
  atlas_forward_decl GlobalTheory.OTY.exists_isSec_of_rapid_cauchy
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem n1_lt_infty_of_isSSec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ), A.IsSSec (A.kap + la) F0 → n1 C la F0 < ⊤ := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 hF
  unfold n1
  rw [ENNReal.sum_lt_top]
  intro a _
  set i := C.idx a
  set T := (A.chart i).target
  have hT : IsOpen T := (A.chart i).open_target
  have hsub : closedBall (C.c a) (C.r a) ⊆ T := C.sub a
  have hF' : ContDiffOn ℝ ∞ (F0 i ∘ (A.chart i).symm) T := hF.1 i
  have hD : ContinuousOn (fun v => fderiv ℝ (F0 i ∘ (A.chart i).symm) v) T :=
    hF'.continuousOn_fderiv_of_isOpen hT (by simp)
  have hph : ContinuousOn (fun v => A.ph la i ((A.chart i).symm v)) T :=
    (A.smooth_ph la i).continuousOn
  have hcont : ContinuousOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) := by
    refine ContinuousOn.mono ?_ hsub
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_finset_sum _ (fun j _ => ?_)
      refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
      unfold wdb
      refine ContinuousOn.div_const (ContinuousOn.add ?_ (ContinuousOn.mul continuousOn_const ?_)) _
      · exact hD.clm_apply continuousOn_const
      · exact hD.clm_apply continuousOn_const
    · exact (hph.neg).rexp
  have hint : IntegrableOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  calc _ ≤ ∫⁻ v in closedBall (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
          Real.exp (-A.ph la i ((A.chart i).symm v))) :=
        lintegral_mono_set ball_subset_closedBall
    _ < ⊤ := hint.lintegral_lt_top

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbarEnergyOnCoverBalls_lt_top_of_smooth : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ), A.IsSSec (A.kap + la) F0 → n1 C la F0 < ⊤ := by
  atlas_forward_decl GlobalTheory.n1_lt_infty_of_isSSec
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.rough_hormander_compact : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K t0 : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), t0 ≤ t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧ n0 A la (F0 - F) ≤ ENNReal.ofReal K * n1 C la F0 := by
  intro n Y _ _ _ _ _ _ ι La _ A C
  obtain ⟨K4, hK4, h4⟩ := GlobalTheory.T.exists_local_hormander_iteration_step n Y ι La A C
  refine ⟨4, 4 * K4 + 1, by norm_num, ?_⟩
  intro la t ht hC F0 hF0
  have tpos : 0 < t := by linarith
  have hq : K4 / t ≤ 1 / 4 := by rw [div_le_iff₀ tpos]; linarith
  have step : ∀ F : {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F},
      ∃ G : {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F},
        n0 A la (F.1 - G.1) ≤ ENNReal.ofReal (1 / 4) * n1 C la F.1 ∧
        n1 C la G.1 ≤ ENNReal.ofReal (1 / 4) * n1 C la F.1 := by
    intro F
    obtain ⟨G, hG, h1, h2⟩ := h4 la t tpos hC F.1 F.2
    have hq' : ENNReal.ofReal (K4 / t) ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal hq
    exact ⟨⟨G, hG⟩, h1.trans (by gcongr), h2.trans (by gcongr)⟩
  choose g hg using step
  let S : ℕ → {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F} := fun m => g^[m] ⟨F0, hF0⟩
  have hS : ∀ m, S (m + 1) = g (S m) := fun m => Function.iterate_succ_apply' g m _
  have hN : n1 C la F0 < ⊤ := GlobalTheory.T.dbarEnergyOnCoverBalls_lt_top_of_smooth n Y ι La A C la F0 hF0
  have hq1 : ENNReal.ofReal (1 / 4) ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h1 : ∀ m, n1 C la (S m).1 ≤ ENNReal.ofReal ((1 / 4) ^ m) * n1 C la F0 := by
    intro m
    induction m with
    | zero => simp [S]
    | succ m ih =>
      rw [hS]
      refine (hg (S m)).2.trans ?_
      calc ENNReal.ofReal (1 / 4) * n1 C la (S m).1
          ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal ((1 / 4) ^ m) * n1 C la F0) := by
            gcongr
        _ = ENNReal.ofReal ((1 / 4) ^ (m + 1)) * n1 C la F0 := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), pow_succ']
  have h0 : ∀ m, n0 A la ((S m).1 - (S (m + 1)).1) ≤
      ENNReal.ofReal ((n1 C la F0).toReal / 4 ^ m) := by
    intro m
    rw [hS]
    refine (hg (S m)).1.trans ?_
    refine (mul_le_of_le_one_left (zero_le) hq1).trans ((h1 m).trans (le_of_eq ?_))
    rw [show (n1 C la F0).toReal / 4 ^ m = (1 / 4) ^ m * (n1 C la F0).toReal by
        rw [one_div, inv_pow]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hN.ne]
  have hT : Tendsto (fun m => n1 C la (S m).1) atTop (𝓝 0) := by
    have hp : Tendsto (fun m : ℕ => ENNReal.ofReal ((1 / 4 : ℝ) ^ m)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num))
      simpa using this
    have hl := ENNReal.Tendsto.mul_const hp (Or.inr hN.ne)
    rw [zero_mul] at hl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
      (fun _ => zero_le) h1
  obtain ⟨G, hG, hfin⟩ := GlobalTheory.T.exists_holomorphicSection_of_rapid_cauchy_dbar n Y ι La A C la t (n1 C la F0).toReal (fun m => (S m).1)
    tpos hC ENNReal.toReal_nonneg (fun m => (S m).2) h0 hT
  refine ⟨G, hG, hfin.trans (le_of_eq ?_)⟩
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hN.ne]
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rough_hormander_estimate_compact_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K t0 : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), t0 ≤ t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧ n0 A la (F0 - F) ≤ ENNReal.ofReal K * n1 C la F0 := by
  atlas_forward_decl GlobalTheory.rough_hormander_compact
end
