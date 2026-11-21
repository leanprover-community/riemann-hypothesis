import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
import BuildAid.ForwardExisting

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.BallStein

variable {n : ℕ}

noncomputable def sqd (c : V n) (y : V n) : ℝ := ‖y - c‖ ^ 2

theorem contDiff_sqd (c : V n) : ContDiff ℝ ∞ (sqd c) :=
  (contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const)

theorem sqd_lt {c y : V n} {r : ℝ} (hy : y ∈ ball c r) : sqd c y < r ^ 2 := by
  have h1 : ‖y - c‖ < r := by simpa [dist_eq_norm] using hy
  have h0 : 0 ≤ ‖y - c‖ := norm_nonneg _
  unfold sqd
  nlinarith

theorem hasDerivAt_k (r t : ℝ) (ht : t < r ^ 2) :
    HasDerivAt (fun t : ℝ => (r ^ 2 - t)⁻¹) (((r ^ 2 - t) ^ 2)⁻¹) t := by
  have hne : r ^ 2 - t ≠ 0 := by linarith
  have := ((hasDerivAt_id t).const_sub (r ^ 2)).inv hne
  refine this.congr_deriv ?_
  simp only [id]
  ring

theorem hasDerivAt_k' (r t : ℝ) (ht : t < r ^ 2) :
    HasDerivAt (fun t : ℝ => ((r ^ 2 - t) ^ 2)⁻¹) (2 * (r ^ 2 - t) / ((r ^ 2 - t) ^ 2) ^ 2) t := by
  have hne : (r ^ 2 - t) ^ 2 ≠ 0 := by
    have : r ^ 2 - t ≠ 0 := by linarith
    positivity
  have h1 := (((hasDerivAt_id t).const_sub (r ^ 2)).pow 2).inv hne
  refine h1.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  norm_num

theorem deriv_k (r t : ℝ) (ht : t < r ^ 2) :
    deriv (fun t : ℝ => (r ^ 2 - t)⁻¹) t = ((r ^ 2 - t) ^ 2)⁻¹ :=
  (hasDerivAt_k r t ht).deriv

theorem deriv_deriv_k (r t : ℝ) (ht : t < r ^ 2) :
    deriv (deriv (fun t : ℝ => (r ^ 2 - t)⁻¹)) t = 2 * (r ^ 2 - t) / ((r ^ 2 - t) ^ 2) ^ 2 := by
  have hev : deriv (fun t : ℝ => (r ^ 2 - t)⁻¹) =ᶠ[𝓝 t] fun t : ℝ => ((r ^ 2 - t) ^ 2)⁻¹ := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact deriv_k r u hu
  rw [hev.deriv_eq]
  exact (hasDerivAt_k' r t ht).deriv

theorem leviV_sqd_nonneg (c x : V n) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((sqd c y : ℝ) : ℂ)) x ξ).re := by
  let u : Fin n → V n → ℝ := fun j y => Complex.normSq (EuclideanSpace.proj j (y - c))
  have hfun : (fun y => ((sqd c y : ℝ) : ℂ)) = fun y => ((∑ j, u j y : ℝ) : ℂ) := by
    funext y
    congr 1
    simp only [sqd, u, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]
    rfl
  have hg : ∀ j : Fin n, ContDiffAt ℂ 2 (fun y : V n => EuclideanSpace.proj j (y - c)) x := fun j =>
    ((EuclideanSpace.proj j : V n →L[ℂ] ℂ).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hu : ∀ j, ContDiffAt ℝ 2 (u j) x := fun j => by
    have hu' : u j = fun y => ‖EuclideanSpace.proj j (y - c)‖ ^ 2 := by
      funext y; simp only [u, Complex.normSq_eq_norm_sq]
    rw [hu']
    exact (contDiff_norm_sq ℂ).contDiffAt.comp x ((hg j).restrict_scalars ℝ)
  rw [hfun, leviV_ofReal_sum hu, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => ((logPshAt_normSq (hg j)).2 ξ).1

end GlobalTheory.BallStein

namespace GlobalTheory.BallStein

variable {n : ℕ}

noncomputable def exh (c : V n) (r : ℝ) (y : V n) : ℝ := (r ^ 2 - sqd c y)⁻¹

theorem contDiffOn_exh (c : V n) (r : ℝ) : ContDiffOn ℝ ∞ (exh c r) (ball c r) :=
  (contDiffOn_const.sub (contDiff_sqd c).contDiffOn).inv fun _ hy => (sub_pos.2 (sqd_lt hy)).ne'

theorem leviV_exh_nonneg {c y : V n} {r : ℝ} (hy : y ∈ ball c r) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun w => ((exh c r w : ℝ) : ℂ)) y ξ).re := by
  have hlt := sqd_lt hy
  have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 hlt
  have hk : ContDiffAt ℝ 2 (fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c y) :=
    (contDiffAt_const.sub contDiffAt_id).inv hp.ne'
  have hc := leviChain n (fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c) y ξ
    (((contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const) : ContDiff ℝ 2 (sqd c)).contDiffAt) hk
  have he : (fun w => ((exh c r w : ℝ) : ℂ)) =
      fun w => (((fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c w) : ℝ) : ℂ) := rfl
  rw [he, hc, deriv_k r _ hlt, deriv_deriv_k r _ hlt]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  have h1 := leviV_sqd_nonneg c y ξ
  have h2 := Complex.normSq_nonneg (∑ j, wd n j (fun w => ((sqd c w : ℝ) : ℂ)) y * ξ j)
  refine add_nonneg (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2)

theorem isCompact_exh (c : V n) (r a : ℝ) : IsCompact {y | y ∈ ball c r ∧ exh c r y ≤ a} := by
  by_cases hr : r ≤ 0
  · have : {y | y ∈ ball c r ∧ exh c r y ≤ a} = ∅ := by
      ext y; simp [Metric.ball_eq_empty.2 hr]
    rw [this]; exact isCompact_empty
  push_neg at hr
  by_cases ha : a ≤ 0
  · have : {y | y ∈ ball c r ∧ exh c r y ≤ a} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro hy
      have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 (sqd_lt hy)
      exact lt_of_le_of_lt ha (inv_pos.2 hp)
    rw [this]; exact isCompact_empty
  push_neg at ha
  have heq : {y | y ∈ ball c r ∧ exh c r y ≤ a} = {y | sqd c y ≤ r ^ 2 - a⁻¹} := by
    ext y
    simp only [Set.mem_setOf_eq, exh]
    constructor
    · rintro ⟨hy, hle⟩
      have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 (sqd_lt hy)
      have := (inv_le_comm₀ hp ha).1 hle
      linarith
    · intro hle
      have hai : 0 < a⁻¹ := inv_pos.2 ha
      have hp : 0 < r ^ 2 - sqd c y := by linarith
      refine ⟨?_, (inv_le_comm₀ hp ha).2 (by linarith)⟩
      rw [mem_ball, dist_eq_norm]
      by_contra hcon
      push_neg at hcon
      have : r ^ 2 ≤ sqd c y := by unfold sqd; nlinarith
      linarith
  rw [heq]
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (contDiff_sqd c).continuous continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := c) (r := r)).subset fun y hy => ?_
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have h1 : sqd c y ≤ r ^ 2 := by simp only [Set.mem_setOf_eq] at hy; linarith
  rw [mem_closedBall, dist_eq_norm]
  unfold sqd at h1
  nlinarith [norm_nonneg (y - c)]

theorem ball_etaleStein : ∀ (n : ℕ) (c : V n) (r : ℝ), ∃ X : EtaleStein n (ball c r), X.z = Subtype.val := by
  intro n c r
  have hU : IsOpen (ball c r) := isOpen_ball
  refine ⟨{ z := Subtype.val
            isLocalHomeomorph := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.val_lh hU
            e := fun x => exh c r x.1
            smooth_e := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.smoothR_val (contDiffOn_exh c r)
            levi_e := fun x ξ => by
              rw [ReciprocityTheory.ChartRestriction.G.AR.Up.HE.levi_val hU]
              exact leviV_exh_nonneg x.2 ξ
            isCompact_le := fun a => by
              rw [Subtype.isCompact_iff]
              convert isCompact_exh c r a using 1
              ext y
              constructor
              · rintro ⟨x, hx, rfl⟩
                exact ⟨x.2, hx⟩
              · rintro ⟨hy, hy'⟩
                exact ⟨⟨y, hy⟩, hy', rfl⟩ }, rfl⟩

end GlobalTheory.BallStein
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_exists_etaleStein_exhaustion : ∀ (n : ℕ) (c : V n) (r : ℝ), ∃ X : EtaleStein n (ball c r), X.z = Subtype.val := by
  atlas_forward_decl GlobalTheory.BallStein.ball_etaleStein
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.HormanderBall

open ReciprocityTheory.ChartRestriction.G.AR.Up.HE

theorem measurable_wdb (n : ℕ) (j : Fin n) (g : V n → ℂ) : Measurable (wdb n j g) := by
  unfold wdb
  exact (((measurable_fderiv_apply_const ℝ g _).add
    ((measurable_fderiv_apply_const ℝ g _).const_mul _)).div_const _)

theorem norm_sum_mul_conj_sq_le {n : ℕ} (a ξ : Fin n → ℂ) :
    ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
  have h1 : ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ≤ ∑ j, ‖a j‖ * ‖ξ j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖ξ j‖)
  calc ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖ξ j‖) ^ 2 := by
        gcongr
    _ ≤ _ := h2

theorem hormander_ball : ∀ (n : ℕ) (c : V n) (r t : ℝ) (φ : V n → ℝ) (F0 : V n → ℂ), 0 < t → ContDiffOn ℝ ∞ φ (ball c r) → ContDiffOn ℝ ∞ F0 (ball c r) → (∀ v ∈ ball c r, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (φ w : ℂ)) v ξ).re) → ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball c r) ∧ ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - F v‖ ^ 2 * Real.exp (-φ v)) ≤ ENNReal.ofReal t⁻¹ * ∫⁻ v in ball c r, ENNReal.ofReal ((∑ j, ‖wdb n j F0 v‖ ^ 2) * Real.exp (-φ v)) := by
  intro n c r t φ F0 ht hφ hF0 hlevi
  have hU : IsOpen (ball c r) := isOpen_ball
  obtain ⟨X, hX⟩ := GlobalTheory.T.ball_exists_etaleStein_exhaustion n c r
  set h : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (t⁻¹ * ∑ j, ‖wdb n j F0 v‖ ^ 2) with hhdef
  have hh : Measurable h := by
    refine ENNReal.measurable_ofReal.comp (Measurable.const_mul ?_ _)
    exact Finset.measurable_sum _ fun j _ => ((measurable_wdb n j F0).norm.pow_const 2)
  have hb : ∀ y ∈ ball c r, ∀ ξ : Fin n → ℂ,
      ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤
        h y * ENNReal.ofReal (leviV n (fun w => (φ w : ℂ)) y ξ).re := by
    intro y hy ξ
    rw [hhdef, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((norm_sum_mul_conj_sq_le _ _).trans ?_)
    have h1 := hlevi y hy ξ
    have h2 : ∑ j, ‖ξ j‖ ^ 2 ≤ t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re := by
      rw [le_inv_mul_iff₀ ht]; exact h1
    have h3 : 0 ≤ ∑ j, ‖wdb n j F0 y‖ ^ 2 := by positivity
    calc (∑ j, ‖wdb n j F0 y‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2
        ≤ (∑ j, ‖wdb n j F0 y‖ ^ 2) * (t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re) := by
          gcongr
      _ = _ := by ring
  obtain ⟨F, hF, hest⟩ := hormander n (ball c r) X (fun x => φ x.1) (fun x => F0 x.1)
    (fun x => h x.1)
    (by rw [hX]; exact smoothR_val hφ)
    (fun x ξ => by
      rw [hX, levi_val hU]
      exact le_trans (by positivity) (hlevi x.1 x.2 ξ))
    (by rw [hX]; exact smooth_val hF0)
    (hh.comp measurable_subtype_coe) (fun x ξ => by
      have := hb x.1 x.2 ξ
      rw [hX]
      show ENNReal.ofReal (‖dbarDot n Subtype.val (fun x : ball c r => F0 x.1) x ξ‖ ^ 2) ≤
        h x.1 * ENNReal.ofReal (Levi n Subtype.val (fun x : ball c r => φ x.1) x ξ).re
      simp only [dbarDot, db_val hU]
      rw [levi_val hU]
      exact this)
  refine ⟨ext0 F, differentiableOn_extendByZero hU (hX ▸ hF), ?_⟩
  have hest' : wint n Subtype.val (fun x : ball c r => F0 x.1 - F x) (fun x : ball c r => φ x.1) ≤
      ∫⁻ x, h x.1 * ENNReal.ofReal (Real.exp (-φ x.1)) ∂vol n (Subtype.val : ball c r → V n) := by
    rw [hX] at hest; exact hest
  have h4 : ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - ext0 F v‖ ^ 2 * Real.exp (-φ v)) ≤
      ∫⁻ v in ball c r, h v * ENNReal.ofReal (Real.exp (-φ v)) := by
    rw [← lintegral_val hU, ← lintegral_val hU]
    simpa [wint, extendByZeroOnSubset_apply_coe] using hest'
  refine h4.trans (le_of_eq ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hU.measurableSet fun v _ => ?_
  rw [hhdef, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

end GlobalTheory.HormanderBall
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound : ∀ (n : ℕ) (c : V n) (r t : ℝ) (φ : V n → ℝ) (F0 : V n → ℂ), 0 < t → ContDiffOn ℝ ∞ φ (ball c r) → ContDiffOn ℝ ∞ F0 (ball c r) → (∀ v ∈ ball c r, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (φ w : ℂ)) v ξ).re) → ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball c r) ∧ ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - F v‖ ^ 2 * Real.exp (-φ v)) ≤ ENNReal.ofReal t⁻¹ * ∫⁻ v in ball c r, ENNReal.ofReal ((∑ j, ‖wdb n j F0 v‖ ^ 2) * Real.exp (-φ v)) := by
  atlas_forward_decl GlobalTheory.HormanderBall.hormander_ball
end
