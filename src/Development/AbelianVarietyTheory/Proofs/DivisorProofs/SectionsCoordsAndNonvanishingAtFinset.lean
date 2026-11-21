import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureLowerBoundOnCoverBalls
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAtlasBallPartitionCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoughHormanderEstimateCompactManifold
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.RegMaxA

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory

theorem quot_jets_det_ne_zero : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (p : V n) (w0 : V n → ℂ) (w : Fin n → V n → ℂ), DifferentiableAt ℂ w0 p → (∀ j, DifferentiableAt ℂ (w j) p) → ‖w0 p - 1‖ ≤ ε → ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε → (∀ j, ‖w j p‖ ≤ ε) → (∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε) → w0 p ≠ 0 ∧ (fderiv ℂ (fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n)) p).det ≠ 0 := by
  intro n
  refine ⟨1 / (4 * ((n : ℝ) + 1)), by positivity, ?_⟩
  intro p w0 w hw0 hw h0 hL0 hwp hLj
  set ε : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hε4 : ε ≤ 1 / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set a := w0 p with ha_def
  have ha_norm : 3 / 4 ≤ ‖a‖ := by
    have h1 : ‖(1:ℂ)‖ ≤ ‖a‖ + ‖a - 1‖ := by
      have := norm_sub_le a (a - 1)
      simpa using this
    simp at h1
    linarith
  have ha : a ≠ 0 := by
    intro h; rw [h] at ha_norm; simp at ha_norm; linarith
  refine ⟨ha, ?_⟩
  set L0 := fderiv ℂ w0 p with hL0_def
  have hL0' : ‖L0‖ ≤ ε := by
    have := hL0; rwa [fderiv_sub_const] at this
  have hproj : ∀ j : Fin n, HasFDerivAt (fun v : V n => v j - p j) (EuclideanSpace.proj (𝕜 := ℂ) j) p := by
    intro j
    have := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt (x := p)
    exact this.sub_const (p j)
  have hLj' : ∀ j : Fin n, ∀ ξ : V n, ‖fderiv ℂ (w j) p ξ - ξ j‖ ≤ ε * ‖ξ‖ := by
    intro j ξ
    have hd : fderiv ℂ (fun v : V n => w j v - (v j - p j)) p
        = fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j :=
      ((hw j).hasFDerivAt.sub (hproj j)).fderiv
    have := (fderiv ℂ (fun v : V n => w j v - (v j - p j)) p).le_opNorm ξ
    rw [hd] at this
    have h2 := hLj j
    rw [hd] at h2
    calc ‖fderiv ℂ (w j) p ξ - ξ j‖ = ‖(fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j) ξ‖ := by simp
      _ ≤ _ := this
      _ ≤ ε * ‖ξ‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  set F : V n → V n := fun v => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) with hF
  have hq : ∀ j : Fin n, HasFDerivAt (fun v => w j v / w0 v)
      (w j p • ((-(a ^ 2)⁻¹) • L0) + a⁻¹ • fderiv ℂ (w j) p) p := by
    intro j
    have hinv : HasFDerivAt (fun v => (w0 v)⁻¹) ((-(a ^ 2)⁻¹) • L0) p :=
      (hasDerivAt_inv ha).comp_hasFDerivAt p hw0.hasFDerivAt
    have := HasFDerivAt.mul (hw j).hasFDerivAt hinv
    have e : (fun v => w j v / w0 v) = (w j * fun v => (w0 v)⁻¹) := by
      funext v; simp [div_eq_mul_inv]
    rw [e]; exact this
  have hFd : DifferentiableAt ℂ F p := by
    rw [differentiableAt_piLp]
    intro j
    simpa [hF] using (hq j).differentiableAt
  set D := fderiv ℂ F p with hD
  have hDj : ∀ j : Fin n, ∀ ξ : V n, (D ξ) j = w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ := by
    intro j ξ
    have h1 : HasFDerivAt (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) ((EuclideanSpace.proj (𝕜 := ℂ) j).comp D) p :=
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt.comp p hFd.hasFDerivAt
    have h2 : (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) = fun v => w j v / w0 v := by
      funext v; simp [hF]
    rw [h2] at h1
    have := congrArg (fun T : V n →L[ℂ] ℂ => T ξ) (h1.unique (hq j))
    simpa using this
  have hinj : ∀ ξ : V n, D ξ = 0 → ξ = 0 := by
    intro ξ hξ
    have hcoord : ∀ j : Fin n, ‖ξ j‖ ≤ 2 * ε * ‖ξ‖ := by
      intro j
      have e := hDj j ξ
      rw [hξ] at e
      simp only [PiLp.zero_apply] at e
      have e2 : a * fderiv ℂ (w j) p ξ = w j p * L0 ξ := by
        have : a ^ 2 * (w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ) = 0 := by
          rw [← e]; ring
        field_simp at this
        linear_combination this
      have hL0ξ : ‖L0 ξ‖ ≤ ε * ‖ξ‖ := (L0.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hL0' (norm_nonneg _))
      have e3 : ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ ≤ ε * (ε * ‖ξ‖) := by
        rw [← norm_mul, e2, norm_mul]
        exact mul_le_mul (hwp j) hL0ξ (norm_nonneg _) hεpos.le
      have e4 : ‖fderiv ℂ (w j) p ξ‖ ≤ ε * ‖ξ‖ := by
        by_contra hc
        push_neg at hc
        have : (3/4) * (ε * ‖ξ‖) < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := by
          calc (3/4) * (ε * ‖ξ‖) ≤ ‖a‖ * (ε * ‖ξ‖) := mul_le_mul_of_nonneg_right ha_norm (by positivity)
            _ < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := mul_lt_mul_of_pos_left hc (by linarith)
        have : ε * (ε * ‖ξ‖) ≤ (3/4) * (ε * ‖ξ‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
      have e5 := hLj' j ξ
      have : ‖ξ j‖ ≤ ‖fderiv ℂ (w j) p ξ‖ + ‖fderiv ℂ (w j) p ξ - ξ j‖ := by
        have := norm_sub_le (fderiv ℂ (w j) p ξ) (fderiv ℂ (w j) p ξ - ξ j)
        simpa using this
      linarith
    have hsq : ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖ξ.ofLp i‖ ^ 2 ≤ ∑ _i : Fin n, (2 * ε * ‖ξ‖) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
        _ = (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by simp
    have hc : (n : ℝ) * (2 * ε) ^ 2 ≤ 1 / 4 := by
      rw [hε]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      rw [show (2 * (1 / (4 * ((n:ℝ) + 1)))) ^ 2 = 1 / (4 * ((n:ℝ)+1)^2) by field_simp; ring]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : ‖ξ‖ ^ 2 ≤ (1/4) * ‖ξ‖ ^ 2 := by
      calc ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := hsq
        _ = ((n : ℝ) * (2 * ε) ^ 2) * ‖ξ‖ ^ 2 := by ring
        _ ≤ (1/4) * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have : ‖ξ‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖ξ‖]
    simpa using this
  intro hdet
  have h := (LinearMap.det_eq_zero_iff_ker_ne_bot (f := (D : V n →ₗ[ℂ] V n))).1 hdet
  apply h
  rw [LinearMap.ker_eq_bot']
  intro m hm
  exact hinj m hm

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_jets_fderiv_det_ne_zero : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (p : V n) (w0 : V n → ℂ) (w : Fin n → V n → ℂ), DifferentiableAt ℂ w0 p → (∀ j, DifferentiableAt ℂ (w j) p) → ‖w0 p - 1‖ ≤ ε → ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε → (∀ j, ‖w j p‖ ≤ ε) → (∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε) → w0 p ≠ 0 ∧ (fderiv ℂ (fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n)) p).det ≠ 0 := by
  atlas_forward_decl GlobalTheory.quot_jets_det_ne_zero
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.TaylorLevi

theorem taylor_two {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : E → ℝ) (p : E)
    (hφ : ContDiffAt ℝ 2 φ p) :
    (fun v => φ v - φ p - fderiv ℝ φ p (v - p) - fderiv ℝ (fderiv ℝ φ) p (v - p) (v - p) / 2)
      =o[𝓝 p] (fun v => ‖v - p‖ ^ 2) := by
  set D := fderiv ℝ φ p
  set B := fderiv ℝ (fderiv ℝ φ) p
  have hB : HasFDerivAt (fderiv ℝ φ) B p :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hsymm : ∀ u w, B u w = B w u := fun u w =>
    (hφ.isSymmSndFDerivAt (by simp [minSmoothness])) u w
  have hdiff := eventually_differentiableAt_of_contDiffAt hφ
  have hlo := hB.isLittleO
  set g : E → ℝ := fun w => φ w - D (w - p) - 1 / 2 * B (w - p) (w - p)
  have hg : ∀ w, DifferentiableAt ℝ φ w → HasFDerivAt g (fderiv ℝ φ w - D - B (w - p)) w := by
    intro w hw
    have h1 : HasFDerivAt (fun x : E => x - p) (ContinuousLinearMap.id ℝ E) w :=
      (hasFDerivAt_id w).sub_const p
    have h2 : HasFDerivAt (fun y => B (y - p) (y - p)) _ w := B.hasFDerivAt_of_bilinear h1 h1
    have h3 := (hw.hasFDerivAt.sub (D.hasFDerivAt.comp w h1)).sub (HasFDerivAt.const_mul h2 (1 / 2 : ℝ))
    refine h3.congr_fderiv ?_
    ext u
    simp
    rw [hsymm u w, hsymm u p]
    ring
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h4 := (Asymptotics.isLittleO_iff.1 hlo) hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h4.and hdiff)
  filter_upwards [Metric.ball_mem_nhds p hδ] with v hv
  have hsub : closedBall p ‖v - p‖ ⊆ ball p δ := by
    apply closedBall_subset_ball
    rw [← dist_eq_norm]; exact mem_ball.1 hv
  have hmvt := (convex_closedBall p ‖v - p‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := g) (C := c * ‖v - p‖)
    (fun w hw => (hg w (hball w (hsub hw)).2).hasFDerivWithinAt)
    (fun w hw => by
      have hw' := hball w (hsub hw)
      have e1 : ‖fderiv ℝ φ w - D - B (w - p)‖ ≤ c * ‖w - p‖ := by
        simpa using hw'.1
      have e2 : ‖w - p‖ ≤ ‖v - p‖ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hw
      exact e1.trans (mul_le_mul_of_nonneg_left e2 hc.le))
    (mem_closedBall_self (norm_nonneg _)) (by rw [mem_closedBall, dist_eq_norm])
  have : g v - g p = φ v - φ p - D (v - p) - B (v - p) (v - p) / 2 := by
    simp only [g]; rw [sub_self]; simp; ring
  rw [this] at hmvt
  rw [norm_pow, norm_norm]
  calc _ ≤ c * ‖v - p‖ * ‖v - p‖ := hmvt
    _ = c * ‖v - p‖ ^ 2 := by ring

end GlobalTheory.TaylorLevi

namespace GlobalTheory.TaylorLevi

variable {n : ℕ}

noncomputable section

theorem rmVec_coord (h : V n) : rmVec (fun j => h j) = h := by
  ext i
  simp [rmVec, bas, EuclideanSpace.single_apply, Pi.single_apply]

def linCoef (D : V n →L[ℝ] ℝ) (j : Fin n) : ℂ :=
  (D (bas n j) : ℂ) - Complex.I * (D (Complex.I • bas n j) : ℂ)

def quadCoef (B : V n →L[ℝ] V n →L[ℝ] ℝ) (j k : Fin n) : ℂ :=
  ((B (bas n j) (bas n k) - B (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
    - Complex.I * ((B (Complex.I • bas n j) (bas n k) + B (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)

theorem lin_re (D : V n →L[ℝ] ℝ) (ξ : Fin n → ℂ) :
    (∑ j, linCoef D j * ξ j).re = D (rmVec ξ) := by
  simp only [rmVec, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rm_cplx_smul_eq]
  simp [linCoef, Complex.mul_re]
  ring

theorem quad_re (B : V n →L[ℝ] V n →L[ℝ] ℝ) (ξ : Fin n → ℂ) :
    (∑ j, ∑ k, quadCoef B j k * ξ j * ξ k).re =
      B (rmVec ξ) (rmVec ξ) - B (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec, rmVec, rm_bil_sum, rm_bil_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_bil_expand B (ξ j) (ξ k), rm_bil_expand B (Complex.I * ξ j) (Complex.I * ξ k)]
  simp [quadCoef, Complex.mul_re, Complex.mul_im]
  ring

end

end GlobalTheory.TaylorLevi

namespace GlobalTheory.TaylorLevi

theorem exists_holo_quadratic_add_levi : ∀ (n : ℕ) (φ : V n → ℝ) (p : V n), ContDiffAt ℝ 2 φ p →
    ∃ q : V n → ℂ, Differentiable ℂ q ∧
      (fun v : V n => φ v - 2 * (q v).re
        - (leviV n (fun w => ((φ w : ℝ) : ℂ)) p (fun j => (v - p) j)).re)
        =o[𝓝 p] (fun v : V n => ‖v - p‖ ^ 2) := by
  intro n φ p hφ
  set D := fderiv ℝ φ p
  set B := fderiv ℝ (fderiv ℝ φ) p
  refine ⟨fun v => (φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2
      + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8, ?_, ?_⟩
  · have hc : ∀ j, Differentiable ℂ (fun v : V n => (v - p) j) := fun j =>
      (EuclideanSpace.proj j : V n →L[ℂ] ℂ).differentiable.comp (differentiable_id.sub_const p)
    fun_prop
  · refine (taylor_two φ p hφ).congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards with v
    have hL := rm_levi_re_ofReal φ p hφ (fun j => (v - p) j)
    have hA := lin_re D (fun j => (v - p) j)
    have hQ := quad_re B (fun j => (v - p) j)
    rw [rmVec_coord] at hL hA hQ
    have hq : ((φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2
        + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8).re
        = φ p / 2 + (∑ j, linCoef D j * (v - p) j).re / 2
          + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k).re / 8 := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re]
    rw [hq, hA, hQ]
    linarith

end GlobalTheory.TaylorLevi
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holo_quadratic_add_levi_isLittleO : ∀ (n : ℕ) (φ : V n → ℝ) (p : V n), ContDiffAt ℝ 2 φ p → ∃ q : V n → ℂ, Differentiable ℂ q ∧ (fun v : V n => φ v - 2 * (q v).re - (leviV n (fun w => ((φ w : ℝ) : ℂ)) p (fun j => (v - p) j)).re) =o[𝓝 p] (fun v : V n => ‖v - p‖ ^ 2) := by
  atlas_forward_decl GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem leviV_re_le_sum_norm {n : ℕ} (g : V n → ℂ) (p ζ : V n) :
    (leviV n g p ζ.ofLp).re ≤
      (∑ j, ∑ k, ‖wd n j (wdb n k g) p‖) * ‖ζ‖ ^ 2 := by
  calc (leviV n g p ζ.ofLp).re ≤ ‖leviV n g p ζ.ofLp‖ := Complex.re_le_norm _
    _ ≤ ∑ j, ‖∑ k, wd n j (wdb n k g) p * ζ.ofLp j * (starRingEnd ℂ) (ζ.ofLp k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j, ∑ k, ‖wd n j (wdb n k g) p‖ * ‖ζ‖ ^ 2 := by
        gcongr with j _
        refine (norm_sum_le _ _).trans ?_
        gcongr with k _
        rw [norm_mul, norm_mul, Complex.norm_conj, sq, ← mul_assoc]
        have hj : ‖ζ.ofLp j‖ ≤ ‖ζ‖ := PiLp.norm_apply_le ζ j
        have hk : ‖ζ.ofLp k‖ ≤ ‖ζ‖ := PiLp.norm_apply_le ζ k
        gcongr
    _ = (∑ j, ∑ k, ‖wd n j (wdb n k g) p‖) * ‖ζ‖ ^ 2 := by
        simp only [Finset.sum_mul]

theorem psh_normal_frame : ∀ (n : ℕ) (O : Set (V n)) (φ : V n → ℝ) (p : V n), IsOpen O → p ∈ O → ContDiffOn ℝ ∞ φ O → (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => ((φ w : ℝ) : ℂ)) p ξ).re) → ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧ closedBall p ρ ⊆ O ∧ ∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ φ v - 2 * (q v).re ∧ φ v - 2 * (q v).re ≤ C * ‖v - p‖ ^ 2 := by
  intro n O φ p hO hp hφ hlevi
  set g : V n → ℂ := fun w => ((φ w : ℝ) : ℂ) with hg
  have hgs : ContDiffOn ℝ ∞ g O := Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  obtain ⟨m, hm, hmb⟩ := levi_pos_compact (g := g) hO hgs (K0 := {p}) isCompact_singleton
    (Set.singleton_subset_iff.2 hp) (fun u hu ζ hζ => by
      rw [Set.mem_singleton_iff.1 hu]
      refine hlevi _ ?_
      intro h0; apply hζ
      exact (WithLp.ofLp_eq_zero 2).1 h0)
  have hφ2 : ContDiffAt ℝ 2 φ p :=
    ((hφ.contDiffAt (hO.mem_nhds hp)).of_le (by norm_cast))
  obtain ⟨q, hq, ho⟩ := GlobalTheory.T.exists_holo_quadratic_add_levi_isLittleO n φ p hφ2
  set A : ℝ := ∑ j, ∑ k, ‖wd n j (wdb n k g) p‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _
  have hev := ho.def (half_pos hm)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨ε2, hε2, hε2O⟩ := Metric.isOpen_iff.1 hO p hp
  refine ⟨q, m / 2, A + m / 2, min ε ε2 / 2, hq, half_pos hm, by positivity,
    by positivity, ?_, ?_⟩
  · intro v hv
    apply hε2O
    rw [mem_closedBall] at hv
    rw [mem_ball]
    have : min ε ε2 / 2 < ε2 := by
      have := min_le_right ε ε2; linarith [lt_min hε hε2]
    linarith
  · intro v hv
    rw [mem_closedBall] at hv
    have hvε : dist v p < ε := by
      have := min_le_left ε ε2; linarith [lt_min hε hε2]
    have hR := hεb hvε
    rw [Real.norm_eq_abs, norm_pow, norm_norm] at hR
    have hlo := hmb p rfl (v - p)
    have hup := leviV_re_le_sum_norm g p (v - p)
    have habs := abs_le.1 hR
    change m * ‖v - p‖ ^ 2 ≤ (leviV n g p (fun j => (v - p) j)).re at hlo
    change (leviV n g p (fun j => (v - p) j)).re ≤ A * ‖v - p‖ ^ 2 at hup
    constructor <;> nlinarith [habs.1, habs.2, sq_nonneg ‖v - p‖]

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psh_normal_frame_quadratic_comparison : ∀ (n : ℕ) (O : Set (V n)) (φ : V n → ℝ) (p : V n), IsOpen O → p ∈ O → ContDiffOn ℝ ∞ φ O → (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => ((φ w : ℝ) : ℂ)) p ξ).re) → ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧ closedBall p ρ ⊆ O ∧ ∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ φ v - 2 * (q v).re ∧ φ v - 2 * (q v).re ≤ C * ‖v - p‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.psh_normal_frame
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem smooth_cutoff_mul_sec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (W : Set Y) (χ : Y → ℝ) (h : ι → Y → ℂ), IsOpen W → A.SmoothFn χ → tsupport χ ⊆ W → A.IsSecOn la W h → A.IsSSec la (fun i y => (χ y : ℂ) * h i y) := by
  intro n Y _ _ _ _ _ ι La _ A la W χ h hW hχ hsupp hh
  have hzero : ∀ y, y ∉ W → χ y = 0 := fun y hy =>
    Function.notMem_support.1 (fun hs => hy (hsupp (subset_tsupport χ hs)))
  refine ⟨fun i => ?_, fun i j y hi hj => ?_⟩
  · intro v hv
    refine ContDiffAt.contDiffWithinAt ?_
    set e := A.chart i
    have hvn : e.target ∈ 𝓝 v := e.open_target.mem_nhds hv
    have hχv : ContDiffAt ℝ ∞ (fun v => ((χ (e.symm v) : ℝ) : ℂ)) v :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp v ((hχ i).contDiffAt hvn)
    by_cases hy : e.symm v ∈ W
    · have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
      have hh' : ContDiffAt ℝ ∞ (h i ∘ e.symm) v :=
        hyq_contDiffAt_of_holo hU (hh.1 i) ⟨hv, hy⟩
      exact hχv.mul hh'
    · have hnt : e.symm v ∉ tsupport χ := fun ht => hy (hsupp ht)
      have hev : χ =ᶠ[𝓝 (e.symm v)] 0 := notMem_tsupport_iff_eventuallyEq.1 hnt
      have hev' : ∀ᶠ v' in 𝓝 v, χ (e.symm v') = 0 := (e.continuousAt_symm hv).eventually hev
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hev'] with v' hv'
      simp [hv']
  · by_cases hy : y ∈ W
    · show (χ y : ℂ) * h i y = A.g la i j y * ((χ y : ℂ) * h j y)
      rw [hh.2 i j y hy hi hj]; ring
    · show (χ y : ℂ) * h i y = A.g la i j y * ((χ y : ℂ) * h j y)
      simp [hzero y hy]

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothSection_cutoff_mul_holomorphic : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (W : Set Y) (χ : Y → ℝ) (h : ι → Y → ℂ), IsOpen W → A.SmoothFn χ → tsupport χ ⊆ W → A.IsSecOn la W h → A.IsSSec la (fun i y => (χ y : ℂ) * h i y) := by
  atlas_forward_decl GlobalTheory.smooth_cutoff_mul_sec
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.CutEnergy

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem wdb_bound (A : WeightedAtlas n Y ι La) (C : Cover A) (χ : Y → ℝ) (hχ : A.SmoothFn χ)
    (a : Fin C.m) : ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ closedBall (C.c a) (C.r a),
      (∑ j, ‖wdb n j (fun w => ((χ ((A.chart (C.idx a)).symm w) : ℝ) : ℂ)) v‖ ^ 2) ≤ K := by
  set e := A.chart (C.idx a)
  have hg : ContDiffOn ℝ ∞ (fun w => ((χ (e.symm w) : ℝ) : ℂ)) e.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ (C.idx a))
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ (fun w => ((χ (e.symm w) : ℝ) : ℂ))) e.target :=
    hg.fderiv_of_isOpen e.open_target (by simp)
  have hc : ContinuousOn (fun v => ∑ j, ‖wdb n j (fun w => ((χ (e.symm w) : ℝ) : ℂ)) v‖ ^ 2)
      e.target := by
    refine continuousOn_finset_sum _ fun j _ => ?_
    have : ContDiffOn ℝ ∞ (wdb n j (fun w => ((χ (e.symm w) : ℝ) : ℂ))) e.target :=
      ((hd.clm_apply contDiffOn_const).add
        (contDiffOn_const.mul (hd.clm_apply contDiffOn_const))).div_const 2
    exact (this.continuousOn.norm).pow 2
  obtain ⟨K, hK⟩ := (isCompact_closedBall (C.c a) (C.r a)).exists_bound_of_continuousOn
    (hc.mono (C.sub a))
  refine ⟨max K 0, le_max_right _ _, fun v hv => ?_⟩
  have := hK v hv
  exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _))

theorem pt_bound (A : WeightedAtlas n Y ι La) (C : Cover A) (χ : Y → ℝ) (hχ : A.SmoothFn χ)
    (a : Fin C.m) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ v ∈ closedBall (C.c a) (C.r a),
      (∑ j, ‖wdb n j (fun w => ((χ ((A.chart (C.idx a)).symm w) : ℝ) : ℂ)) v‖ ^ 2) ≤ K)
    (la : La) (W Z : Set Y) (h : ι → Y → ℂ) (hW : IsOpen W) (hsupp : tsupport χ ⊆ W)
    (hsec : A.IsSecOn (A.kap + la) W h)
    (hZ : ∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) (v : V n) (hv : v ∈ ball (C.c a) (C.r a)) :
    ENNReal.ofReal ((∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) (C.idx a) ∘
        (A.chart (C.idx a)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤
      ENNReal.ofReal K * ((Z ∩ W).indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y))
          ((A.chart (C.idx a)).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v)))) := by
  set i := C.idx a
  set e := A.chart i
  set y := e.symm v
  set g : V n → ℂ := fun w => ((χ (e.symm w) : ℝ) : ℂ)
  have hvt : v ∈ e.target := C.sub a (ball_subset_closedBall hv)
  have hys : y ∈ e.source := e.map_target hvt
  have hgs : ContDiffOn ℝ ∞ g e.target := Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ i)
  have hgd : DifferentiableAt ℝ g v :=
    (hgs.differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds hvt)

  have hzero : y ∉ Z ∩ W → ∀ j, wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v = 0 := by
    intro hy j
    by_cases hyW : y ∈ W
    · have hyZ : y ∉ Z := fun hz => hy ⟨hz, hyW⟩
      have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
      have hvU : v ∈ e.target ∩ e.symm ⁻¹' W := ⟨hvt, hyW⟩
      have hH : DifferentiableAt ℂ (h i ∘ e.symm) v :=
        (hsec.1 i).differentiableAt (hU.mem_nhds hvU)
      have hg0 : wdb n j g v = 0 := by
        have hev : g =ᶠ[𝓝 v] fun _ => ((χ y : ℝ) : ℂ) := by
          have := (e.continuousAt_symm hvt).eventually (hZ y hyZ)
          filter_upwards [this] with w hw
          simp only [g]; rw [hw]
        rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hev]
        exact wdb_of_differentiableAt (differentiableAt_const _)
      have hfun : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) = fun w => g w * (h i ∘ e.symm) w :=
        rfl
      rw [hfun, wdb_mul hgd (hH.restrictScalars ℝ), wdb_of_differentiableAt hH, hg0]
      ring
    · have hyt : y ∉ tsupport χ := fun ht => hyW (hsupp ht)
      have h0 := (notMem_tsupport_iff_eventuallyEq.mp hyt)
      have hev : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
        have := (e.continuousAt_symm hvt).eventually h0
        filter_upwards [this] with w hw
        simp only [Function.comp_apply, Pi.zero_apply] at hw ⊢
        rw [hw]; simp
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hev]
      exact wdb_of_differentiableAt (differentiableAt_const _)
  by_cases hy : y ∈ Z ∩ W
  · have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
    have hvU : v ∈ e.target ∩ e.symm ⁻¹' W := ⟨hvt, hy.2⟩
    have hH : DifferentiableAt ℂ (h i ∘ e.symm) v :=
      (hsec.1 i).differentiableAt (hU.mem_nhds hvU)
    have hfun : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) = fun w => g w * (h i ∘ e.symm) w :=
      rfl
    have hw : ∀ j, wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v = wdb n j g v * h i y := by
      intro j
      rw [hfun, wdb_mul hgd (hH.restrictScalars ℝ), wdb_of_differentiableAt hH]
      simp [y]
    have hsum : (∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v‖ ^ 2) =
        ‖h i y‖ ^ 2 * ∑ j, ‖wdb n j g v‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw j, norm_mul, mul_pow]; ring
    have hnsq := api_nsq_eq A hsec hys hy.2
    rw [A.ph_add _ _ i y hys] at hnsq
    have hexp : Real.exp (-A.ph la i y) =
        Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [Set.indicator_of_mem hy, ← ENNReal.ofReal_mul (by unfold WeightedAtlas.nsq; positivity),
      ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hsum, ← hnsq, hexp]
    have hS := hK v (ball_subset_closedBall hv)
    have h1 : 0 ≤ ‖h i y‖ ^ 2 * (Real.exp (-(A.ph A.kap i y + A.ph la i y)) *
        Real.exp (A.ph A.kap i y)) := by positivity
    calc ‖h i y‖ ^ 2 * (∑ j, ‖wdb n j g v‖ ^ 2) *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))
        = (∑ j, ‖wdb n j g v‖ ^ 2) * (‖h i y‖ ^ 2 *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))) := by ring
      _ ≤ K * (‖h i y‖ ^ 2 *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))) :=
          mul_le_mul_of_nonneg_right hS h1
      _ = K * (‖h i y‖ ^ 2 * Real.exp (-(A.ph A.kap i y + A.ph la i y)) *
          Real.exp (A.ph A.kap i y)) := by ring
  · have : (∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v‖ ^ 2) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hzero hy j]; simp
    rw [this, zero_mul, ENNReal.ofReal_zero]
    exact zero_le

end

end GlobalTheory.CutEnergy

namespace GlobalTheory.CutEnergy

theorem dbarEnergy_cutoff_mul_section_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (χ : Y → ℝ), A.SmoothFn χ → ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (W Z : Set Y) (h : ι → Y → ℂ), IsOpen W → tsupport χ ⊆ W → A.IsSecOn (A.kap + la) W h → MeasurableSet Z → (∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) → n1 C la (fun i y => (χ y : ℂ) * h i y) ≤ ENNReal.ofReal K * ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A C χ hχ
  choose K hK0 hK using fun a => wdb_bound A C χ hχ a
  refine ⟨∑ a, K a, Finset.sum_nonneg fun a _ => hK0 a, ?_⟩
  intro la W Z h hW hsupp hsec hZm hZ
  set G : Y → ℝ≥0∞ := (Z ∩ W).indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) with hGdef
  have hGm : Measurable G := by
    classical
    have h1 : Measurable (W.indicator fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) := by
      rw [← Set.piecewise_eq_indicator]
      exact ContinuousOn.measurable_piecewise
        (ENNReal.continuous_ofReal.comp_continuousOn (api_nsq_contOn A hW hsec))
        continuousOn_const hW.measurableSet
    have : G = Z.indicator (W.indicator fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) :=
      (Set.indicator_indicator _ _ _).symm
    rw [this]; exact h1.indicator hZm
  have hint : ∫⁻ y, G y ∂A.mu = ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu :=
    lintegral_indicator (hZm.inter hW.measurableSet) _
  rw [← hint, ENNReal.ofReal_sum_of_nonneg (fun a _ => hK0 a), Finset.sum_mul]
  unfold n1
  refine Finset.sum_le_sum fun a _ => ?_
  calc _ ≤ ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (K a) *
          (G ((A.chart (C.idx a)).symm v) *
            ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v)))) :=
        setLIntegral_mono' measurableSet_ball fun v hv =>
          pt_bound A C χ hχ a (K a) (hK0 a) (hK a) la W Z h hW hsupp hsec hZ v hv
    _ = ENNReal.ofReal (K a) * ∫⁻ v in ball (C.c a) (C.r a), G ((A.chart (C.idx a)).symm v) *
            ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
          gcongr
          exact A.aap_lintegral_chart_le _ G hGm _ (ball_subset_closedBall.trans (C.sub a))

end GlobalTheory.CutEnergy
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.n1_cutoff_mul_section_le_lintegral : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (χ : Y → ℝ), A.SmoothFn χ → ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (W Z : Set Y) (h : ι → Y → ℂ), IsOpen W → tsupport χ ⊆ W → A.IsSecOn (A.kap + la) W h → MeasurableSet Z → (∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) → n1 C la (fun i y => (χ y : ℂ) * h i y) ≤ ENNReal.ofReal K * ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu := by
  atlas_forward_decl GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem smooth_bump_chart_ball : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (i : ι) (p : V n) (ρ : ℝ), 0 < ρ → closedBall p ρ ⊆ (A.chart i).target → ∃ χ : Y → ℝ, A.SmoothFn χ ∧ tsupport χ ⊆ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball p (ρ / 2) → χ y = 1 := by
  intro n Y _ _ _ _ _ ι La _ A i p ρ hρ hK
  let b : ContDiffBump p := ⟨ρ / 2, 3 * ρ / 4, by linarith, by linarith⟩
  have hK0 : IsCompact (closedBall p (3 * ρ / 4)) := isCompact_closedBall p _
  have hK0t : closedBall p (3 * ρ / 4) ⊆ (A.chart i).target :=
    (closedBall_subset_closedBall (by linarith)).trans hK
  have hβs : ∀ u, (b : V n → ℝ) u ≠ 0 → u ∈ closedBall p (3 * ρ / 4) := by
    intro u hu
    have : u ∈ Function.support (b : V n → ℝ) := hu
    rw [b.support_eq] at this
    exact ball_subset_closedBall this
  refine ⟨A.chiC i b, A.chiC_smooth b.contDiff hβs hK0 hK0t, ?_, ?_⟩
  · have hC := (A.isCompact_chartImage hK0 hK0t).isClosed
    have hsup : Function.support (A.chiC i b) ⊆ (A.chart i).symm '' closedBall p (3 * ρ / 4) := by
      intro y hy
      by_contra h
      exact hy (A.chiC_eq_zero hβs h)
    refine (closure_minimal hsup hC).trans ?_
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨(A.chart i).map_target (hK0t hu), ?_⟩
    show A.chart i ((A.chart i).symm u) ∈ ball p ρ
    rw [(A.chart i).right_inv (hK0t hu)]
    exact closedBall_subset_ball (by linarith) hu
  · intro y hy hb
    rw [A.chiC_of_mem hy]
    exact b.one_of_mem_closedBall (ball_subset_closedBall hb)

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_bump_chart_ball_halfOne : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (i : ι) (p : V n) (ρ : ℝ), 0 < ρ → closedBall p ρ ⊆ (A.chart i).target → ∃ χ : Y → ℝ, A.SmoothFn χ ∧ tsupport χ ⊆ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball p (ρ / 2) → χ y = 1 := by
  atlas_forward_decl GlobalTheory.smooth_bump_chart_ball
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem peak_isSecOn {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (la : La) (i : ι) (W : Set Y) (hW : W ⊆ (A.chart i).source)
    (u : V n → ℂ) (hu : Differentiable ℂ u) :
    A.IsSecOn la W (fun j y => A.g la j i y * u (A.chart i y)) := by
  refine ⟨fun j => ?_, fun j l y hy hj hl => ?_⟩
  · have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' W ⊆ ovl A.chart j i :=
      fun v hv => ⟨hv.1, hW hv.2⟩
    have h1 := (A.holo_g la j i).mono hsub
    have h2 := hu.comp_differentiableOn ((A.holo_trans j i).mono hsub)
    exact h1.mul h2
  · show A.g la j i y * _ = A.g la j l y * (A.g la l i y * _)
    rw [A.g_cocycle la j l i y hj hl (hW hy)]; ring

theorem peak_section : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La) (i : ι) (p : V n) (ρ c : ℝ) (q f : V n → ℂ), 0 < ρ → 0 < c → closedBall p ρ ⊆ (A.chart i).target → Differentiable ℂ q → Differentiable ℂ f → (∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ A.ph H i ((A.chart i).symm v) - 2 * (q v).re) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ v ∈ ball p (ρ / 2), F0 i ((A.chart i).symm v) = f v * Complex.exp (k * q v)) ∧ (∀ j y, y ∉ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ → F0 j y = 0) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
  intro n Y _ _ _ _ _ ι La _ A C H G i p ρ c q f hρ hc hball hq hf hpeak
  obtain ⟨χ, hχs, hχsupp, hχ1⟩ := GlobalTheory.T.smooth_bump_chart_ball_halfOne n Y ι La A i p ρ hρ hball
  obtain ⟨K0, hK0, hcut⟩ := GlobalTheory.T.n1_cutoff_mul_section_le_lintegral n Y ι La A C χ hχs
  set W : Set Y := (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ with hWdef
  set Wi : Set Y := (A.chart i).source ∩ A.chart i ⁻¹' ball p (ρ / 2) with hWidef
  have hWo : IsOpen W := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hWio : IsOpen Wi := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hWs : W ⊆ (A.chart i).source := Set.inter_subset_left
  set Z : Set Y := W \ Wi with hZdef
  have hZm : MeasurableSet Z := hWo.measurableSet.diff hWio.measurableSet
  have hZloc : ∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hyi : y ∈ Wi := by
        by_contra h
        exact hy ⟨hyW, h⟩
      filter_upwards [hWio.mem_nhds hyi] with x hx
      rw [hχ1 x hx.1 hx.2, hχ1 y hyi.1 hyi.2]
    · have hns : y ∉ tsupport χ := fun h => hyW (hχsupp h)
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hns] with x hx
      rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hns]
  have hKc : IsCompact ((A.chart i).symm '' closedBall p ρ) :=
    (isCompact_closedBall p ρ).image_of_continuousOn ((A.chart i).continuousOn_symm.mono hball)
  have hWK : Z ∩ W ⊆ (A.chart i).symm '' closedBall p ρ := fun y hy =>
    ⟨A.chart i y, ball_subset_closedBall hy.2.2, (A.chart i).left_inv hy.2.1⟩
  have hfin : A.mu (Z ∩ W) ≠ ⊤ :=
    ((measure_mono hWK).trans_lt (ap_mu_compact A _ hKc)).ne
  have hcont : ContinuousOn (fun v => ‖f v‖ ^ 2 *
      Real.exp (-A.ph (A.kap + G) i ((A.chart i).symm v))) (closedBall p ρ) :=
    (hf.continuous.continuousOn.norm.pow 2).mul
      (((A.smooth_ph (A.kap + G) i).continuousOn.mono hball).neg.rexp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall p ρ).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p (mem_closedBall_self hρ.le))
  refine ⟨K0 * (M * (A.mu (Z ∩ W)).toReal), by positivity, fun k => ?_⟩
  have hu : Differentiable ℂ (fun v => f v * Complex.exp (k * q v)) :=
    hf.mul ((hq.const_mul _).cexp)
  have hsec := peak_isSecOn A (A.kap + (G + k • H)) i W hWs _ hu
  refine ⟨_, GlobalTheory.T.smoothSection_cutoff_mul_holomorphic n Y ι La A _ W χ _ hWo hχs hχsupp hsec, ?_, ?_, ?_⟩
  · intro v hv
    have hvt : v ∈ (A.chart i).target :=
      hball (ball_subset_closedBall (ball_subset_ball (by linarith) hv))
    have hs := (A.chart i).map_target hvt
    have hr := (A.chart i).right_inv hvt
    have h1 : χ ((A.chart i).symm v) = 1 := hχ1 _ hs (by rw [hr]; exact hv)
    simp only [h1, A.g_self _ i hs, hr]
    simp
  · intro j y hy
    have hns : y ∉ tsupport χ := fun h => hy (hχsupp h)
    simp [image_eq_zero_of_notMem_tsupport hns]
  · refine (hcut (G + k • H) W Z _ hWo hχsupp hsec hZm hZloc).trans ?_
    have hbd : ∀ y ∈ Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + (G + k • H))
        (fun j y => A.g (A.kap + (G + k • H)) j i y *
          (f (A.chart i y) * Complex.exp (k * q (A.chart i y)))) y) ≤
        ENNReal.ofReal (M * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      have hs : y ∈ (A.chart i).source := hy.2.1
      have hcb : A.chart i y ∈ closedBall p ρ := ball_subset_closedBall hy.2.2
      have hout : ρ / 2 ≤ ‖A.chart i y - p‖ := by
        by_contra h
        exact hy.1.2 ⟨hs, by simpa [mem_ball, dist_eq_norm] using not_le.1 h⟩
      rw [A.nsq_chart _ _ i hs (hsec.2 _ i y hy.2 (A.mem_pick y) hs)]
      have h1 := hM _ hcb
      have h2 := hpeak _ hcb
      rw [(A.chart i).left_inv hs] at h1 h2
      rw [Real.norm_of_nonneg (by positivity)] at h1
      have h3 : c * ρ ^ 2 / 4 ≤ c * ‖A.chart i y - p‖ ^ 2 := by
        have : (ρ / 2) ^ 2 ≤ ‖A.chart i y - p‖ ^ 2 := by gcongr
        nlinarith
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have e : ‖A.g (A.kap + (G + k • H)) i i y *
          (f (A.chart i y) * Complex.exp (k * q (A.chart i y)))‖ ^ 2 *
          Real.exp (-A.ph (A.kap + (G + k • H)) i y) =
          (‖f (A.chart i y)‖ ^ 2 * Real.exp (-A.ph (A.kap + G) i y)) *
          Real.exp (-(A.ph H i y - 2 * (q (A.chart i y)).re) * k) := by
        rw [A.g_self _ i hs, one_mul, norm_mul, Complex.norm_exp, ← add_assoc,
          A.ph_add _ (k • H) i y hs, A.aap_ph_nsmul H k i hs, mul_pow, ← Real.exp_nat_mul,
          mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        simp
        ring
      refine e.le.trans ?_
      refine mul_le_mul h1 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hM0
      nlinarith
    have hint := setLIntegral_mono' (μ := A.mu) (hZm.inter hWo.measurableSet) hbd
    rw [setLIntegral_const] at hint
    refine (mul_le_mul_right hint _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hK0, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    ring

end GlobalTheory.OTY
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_peak_section_small_dbar_energy : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La) (i : ι) (p : V n) (ρ c : ℝ) (q f : V n → ℂ), 0 < ρ → 0 < c → closedBall p ρ ⊆ (A.chart i).target → Differentiable ℂ q → Differentiable ℂ f → (∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ A.ph H i ((A.chart i).symm v) - 2 * (q v).re) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ v ∈ ball p (ρ / 2), F0 i ((A.chart i).symm v) = f v * Complex.exp (k * q v)) ∧ (∀ j y, y ∉ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ → F0 j y = 0) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
  atlas_forward_decl GlobalTheory.OTY.peak_section
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem isSSec_finset_sum_and_n1_le_card_mul_sum (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (C : Cover A) (la : La) (T : Finset Y) (F : Y → ι → Y → ℂ)
    (hF : ∀ P ∈ T, A.IsSSec (A.kap + la) (F P)) :
    A.IsSSec (A.kap + la) (fun i y => ∑ P ∈ T, F P i y) ∧
      n1 C la (fun i y => ∑ P ∈ T, F P i y) ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, n1 C la (F P) := by
  refine ⟨⟨fun i => ?_, fun i j y hi hj => ?_⟩, ?_⟩
  · exact ContDiffOn.sum (fun P hP => (hF P hP).1 i)
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun P hP => (hF P hP).2 i j y hi hj)
  ·
    have key : ∀ a : Fin C.m,
        (∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j ((fun y => ∑ P ∈ T, F P (C.idx a) y) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))))
        ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
      intro a
      set i := C.idx a with hi
      set e := A.chart i with he
      have hball : Metric.ball (C.c a) (C.r a) ⊆ e.target :=
        Metric.ball_subset_closedBall.trans (C.sub a)
      have hdiff : ∀ P ∈ T, ∀ v ∈ Metric.ball (C.c a) (C.r a),
          DifferentiableAt ℝ (F P i ∘ e.symm) v := fun P hP v hv =>
        ((hF P hP).1 i).differentiableOn (by simp) |>.differentiableAt
          (e.open_target.mem_nhds (hball hv))

      have hcont : ∀ P ∈ T, ContinuousOn (fun v => ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) *
            Real.exp (-A.ph la i (e.symm v)))) (Metric.ball (C.c a) (C.r a)) := by
        intro P hP
        have hfd : ContinuousOn (fderiv ℝ (F P i ∘ e.symm)) e.target :=
          ((hF P hP).1 i).continuousOn_fderiv_of_isOpen e.open_target (by simp)
        have hph : ContinuousOn (fun v => A.ph la i (e.symm v)) e.target :=
          (A.smooth_ph la i).continuousOn
        refine ENNReal.continuous_ofReal.comp_continuousOn ?_
        refine ContinuousOn.mul ?_ ((hph.mono hball).neg.rexp)
        refine continuousOn_finset_sum _ (fun j _ => ?_)
        refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
        unfold wdb
        refine ContinuousOn.div_const (ContinuousOn.add ?_ (continuousOn_const.mul ?_)) _
        · exact (hfd.clm_apply continuousOn_const).mono hball
        · exact (hfd.clm_apply continuousOn_const).mono hball
      have hpt : ∀ v ∈ Metric.ball (C.c a) (C.r a),
          ENNReal.ofReal ((∑ j, ‖wdb n j ((fun y => ∑ P ∈ T, F P i y) ∘ e.symm) v‖ ^ 2) *
            Real.exp (-A.ph la i (e.symm v)))
          ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, ENNReal.ofReal
            ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))) := by
        intro v hv
        have hfun : (fun y => ∑ P ∈ T, F P i y) ∘ e.symm = fun w => ∑ P ∈ T, (F P i ∘ e.symm) w := rfl
        rw [hfun]
        have hs : ∀ j, wdb n j (fun w => ∑ P ∈ T, (F P i ∘ e.symm) w) v
            = ∑ P ∈ T, wdb n j (F P i ∘ e.symm) v := fun j => wdb_sum T (fun P hP => hdiff P hP v hv)
        simp only [hs]
        have hE := Real.exp_pos (-A.ph la i (e.symm v))
        have hreal : (∑ j, ‖∑ P ∈ T, wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))
            ≤ (T.card : ℝ) * ∑ P ∈ T, (∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) *
              Real.exp (-A.ph la i (e.symm v)) := by
          rw [← Finset.sum_mul, ← mul_assoc, Finset.sum_comm, Finset.mul_sum]
          refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) hE.le
          calc ‖∑ P ∈ T, wdb n j (F P i ∘ e.symm) v‖ ^ 2
              ≤ (∑ P ∈ T, ‖wdb n j (F P i ∘ e.symm) v‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
            _ ≤ (T.card : ℝ) * ∑ P ∈ T, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2 :=
                sq_sum_le_card_mul_sum_sq
        refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun P _ => by positivity)]
      calc _ ≤ ∫⁻ v in Metric.ball (C.c a) (C.r a), (T.card : ℝ≥0∞) * ∑ P ∈ T, ENNReal.ofReal
            ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))) :=
            lintegral_mono_ae ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).2
              (Filter.Eventually.of_forall hpt))
        _ = _ := by
          rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
            lintegral_finset_sum' _ (fun P hP => (hcont P hP).aemeasurable
              Metric.isOpen_ball.measurableSet)]
    unfold n1
    calc _ ≤ ∑ a, (T.card : ℝ≥0∞) * ∑ P ∈ T, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) :=
          Finset.sum_le_sum fun a _ => key a
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end GlobalTheory.OTY
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finSum_smoothSection_dbarEnergy_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (T : Finset Y) (F : Y → ι → Y → ℂ), (∀ P ∈ T, A.IsSSec (A.kap + la) (F P)) → A.IsSSec (A.kap + la) (fun i y => ∑ P ∈ T, F P i y) ∧ n1 C la (fun i y => ∑ P ∈ T, F P i y) ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, n1 C la (F P) := by
  atlas_forward_decl GlobalTheory.OTY.isSSec_finset_sum_and_n1_le_card_mul_sum
end

section
namespace GlobalTheory.PositiveLowerBoundFinset

theorem pos_lower_bound_on_finset : ∀ {Y : Type} (T : Finset Y) (f : Y → ℝ),
    (∀ (P : Y), (0 : ℝ) < f P) → ∃ (r : ℝ), (0 : ℝ) < r ∧ ∀ P ∈ T, r ≤ f P := by
  intro Y T f hf
  rcases T.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x, -, hmin⟩ := T.exists_min_image f h
    exact ⟨f x, hf x, hmin⟩

end GlobalTheory.PositiveLowerBoundFinset
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem peakFin_exists_pos_le {Y : Type} (T : Finset Y) (f : Y → ℝ) (hf : ∀ P, 0 < f P) :
    ∃ r : ℝ, 0 < r ∧ ∀ P ∈ T, r ≤ f P := by
  first
  | exact @_root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset
  | exact _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset
  | (apply _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset ..)

theorem peak_sections_finite : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ (q : Y → V n → ℂ) (c Cq r0 : ℝ), 0 < c ∧ 0 < r0 ∧ (∀ P ∈ T, Differentiable ℂ (q P) ∧ closedBall (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target ∧ ∀ v ∈ closedBall (A.chart (A.pick P) P) r0, A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q P v).re ≤ Cq * ‖v - (A.chart (A.pick P) P)‖ ^ 2) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ P ∈ T, ∀ v ∈ ball (A.chart (A.pick P) P) r0, F0 (A.pick P) ((A.chart (A.pick P)).symm v) = p P v * Complex.exp (k * q P v)) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-c * k)) := by
  intro n Y _ _ _ _ _ ι La _ A C H hH T
  classical
  obtain ⟨U, hU, hdisj⟩ := T.finite_toSet.t2_separation
  have h7 : ∀ P : Y, ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧
      closedBall (A.chart (A.pick P) P) ρ ⊆
        (A.chart (A.pick P)).target ∩ (A.chart (A.pick P)).symm ⁻¹' U P ∧
      ∀ v ∈ closedBall (A.chart (A.pick P) P) ρ,
        c * ‖v - A.chart (A.pick P) P‖ ^ 2 ≤
          A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q v).re ∧
        A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q v).re ≤
          C * ‖v - A.chart (A.pick P) P‖ ^ 2 := by
    intro P
    refine GlobalTheory.T.psh_normal_frame_quadratic_comparison n _ (fun v => A.ph H (A.pick P) ((A.chart (A.pick P)).symm v)) _
      ((A.chart (A.pick P)).isOpen_inter_preimage_symm (hU P).2) ?_
      ((A.smooth_ph H (A.pick P)).mono Set.inter_subset_left) ?_
    · refine ⟨(A.chart (A.pick P)).map_source (A.mem_pick P), ?_⟩
      rw [Set.mem_preimage, (A.chart (A.pick P)).left_inv (A.mem_pick P)]
      exact (hU P).1
    · intro ξ hξ
      exact hH (A.pick P) P (A.mem_pick P) ξ hξ
  choose q c Cc ρ hq hc hC hρ hsub hb using h7
  obtain ⟨r0, hr0, hr0le⟩ := peakFin_exists_pos_le T (fun P => ρ P / 2)
    (fun P => half_pos (hρ P))
  obtain ⟨c0, hc0, hc0le⟩ := peakFin_exists_pos_le T (fun P => c P * ρ P ^ 2 / 4)
    (fun P => by have := hc P; have := hρ P; positivity)
  have hrρ : ∀ P ∈ T, r0 ≤ ρ P := fun P hP => by
    have h1 : r0 ≤ ρ P / 2 := hr0le P hP
    have := hρ P
    linarith
  refine ⟨q, c0, ∑ P ∈ T, Cc P, r0, hc0, hr0, fun P hP => ⟨hq P, ?_, ?_⟩, ?_⟩
  · exact ((closedBall_subset_closedBall (hrρ P hP)).trans (hsub P)).trans Set.inter_subset_left
  · intro v hv
    refine (hb P v (closedBall_subset_closedBall (hrρ P hP) hv)).2.trans ?_
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := Cc) (fun Q _ => (hC Q).le) hP) (by positivity)
  · intro G p hp
    have h9 := fun P : Y => GlobalTheory.T.exists_peak_section_small_dbar_energy n Y ι La A C H G (A.pick P) (A.chart (A.pick P) P)
      (ρ P) (c P) (q P) (p P) (hρ P) (hc P) ((hsub P).trans Set.inter_subset_left) (hq P) (hp P)
      (fun v hv => (hb P v hv).1)
    choose K hK F hF using h9
    have hKs : 0 ≤ ∑ P ∈ T, K P := Finset.sum_nonneg fun P _ => hK P
    refine ⟨(T.card : ℝ) * ∑ P ∈ T, K P, by positivity, fun k => ?_⟩
    obtain ⟨hs, hn⟩ := GlobalTheory.T.finSum_smoothSection_dbarEnergy_le n Y ι La A C (G + k • H) T (fun P => F P k)
      (fun P _ => (hF P k).1)
    refine ⟨_, hs, fun P hP v hv => ?_, hn.trans ?_⟩
    · have hv' : v ∈ ball (A.chart (A.pick P) P) (ρ P / 2) := ball_subset_ball (hr0le P hP) hv
      have hvU : (A.chart (A.pick P)).symm v ∈ U P :=
        (hsub P (ball_subset_closedBall (ball_subset_ball (hrρ P hP) hv))).2
      rw [← (hF P k).2.1 v hv']
      refine Finset.sum_eq_single_of_mem P hP (fun Q hQ hQP => ?_)
      refine (hF Q k).2.2.1 _ _ (fun hm => ?_)
      have h1 := (hsub Q (ball_subset_closedBall hm.2)).2
      rw [Set.mem_preimage, (A.chart (A.pick Q)).left_inv hm.1] at h1
      exact Set.disjoint_left.1 (hdisj (Finset.mem_coe.2 hQ) (Finset.mem_coe.2 hP) hQP) h1 hvU
    · have hle : ∑ P ∈ T, n1 C (G + k • H) (F P k) ≤
          ∑ P ∈ T, ENNReal.ofReal (K P * Real.exp (-c0 * k)) := by
        refine Finset.sum_le_sum fun P hP => (hF P k).2.2.2.trans ?_
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hK P))
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k))
        exact neg_le_neg (hc0le P hP)
      refine (mul_le_mul_right hle _).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg
          (fun P _ => mul_nonneg (hK P) (Real.exp_pos _).le), ← Finset.sum_mul, mul_assoc,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end GlobalTheory.OTY
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peak_sections_finite_weighted_atlas : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ (q : Y → V n → ℂ) (c Cq r0 : ℝ), 0 < c ∧ 0 < r0 ∧ (∀ P ∈ T, Differentiable ℂ (q P) ∧ closedBall (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target ∧ ∀ v ∈ closedBall (A.chart (A.pick P) P) r0, A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q P v).re ≤ Cq * ‖v - (A.chart (A.pick P) P)‖ ^ 2) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ P ∈ T, ∀ v ∈ ball (A.chart (A.pick P) P) r0, F0 (A.pick P) ((A.chart (A.pick P)).symm v) = p P v * Complex.exp (k * q P v)) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-c * k)) := by
  atlas_forward_decl GlobalTheory.OTY.peak_sections_finite
end

section
namespace GlobalTheory.FrechetDerivativeBound

theorem norm_fderiv_le_of_bounded_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E} {ρ R M : ℝ} (hρ : 0 < ρ) (hR : ρ < R) (u : E → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ := by
  have hp : p ∈ Metric.ball p R := Metric.mem_ball_self (hρ.trans hR)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p hp)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hM0 hρ.le) ?_
  intro v hv
  have hmem : ∀ t ∈ Metric.closedBall (0 : ℂ) ρ, p + t • v ∈ Metric.ball p R := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one]
    exact ht.trans_lt hR
  have hline : ∀ t : ℂ, HasDerivAt (fun s : ℂ => p + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hd : DifferentiableOn ℂ (fun t : ℂ => u (p + t • v)) (Metric.closedBall 0 ρ) :=
    hu.comp (fun t _ => (hline t).differentiableAt.differentiableWithinAt) hmem
  have hdc : DiffContOnCl ℂ (fun t : ℂ => u (p + t • v)) (Metric.ball 0 ρ) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball _ hρ.ne']
  have hup : DifferentiableAt ℂ u p := hu.differentiableAt (Metric.isOpen_ball.mem_nhds hp)
  have hder : HasDerivAt (fun t : ℂ => u (p + t • v)) (fderiv ℂ u p v) 0 := by
    have h1 : HasFDerivAt u (fderiv ℂ u p) (p + (0 : ℂ) • v) := by
      simpa using hup.hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hline 0)
  rw [← hder.deriv]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc
    (fun z hz => hM _ (hmem z (Metric.sphere_subset_closedBall hz)))

theorem norm_fderiv_le_of_bounded {n : ℕ} {p : ReciprocityTheory.L2DbarEstimates.V n} {ρ R M : ℝ}
    (hρ : (0 : ℝ) < ρ) (hR : ρ < R) (u : ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ :=
  norm_fderiv_le_of_bounded_gen hρ hR u hu hM

end GlobalTheory.FrechetDerivativeBound
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

theorem l2ball_sq_mul_vol_le {n : ℕ} {x : V n} {s : ℝ} (u : V n → ℂ)
    (hu : DifferentiableOn ℂ u (ball x s)) :
    ENNReal.ofReal (‖u x‖ ^ 2) * volume (ball (0 : V n) s) ≤
      ∫⁻ v in ball x s, ENNReal.ofReal (‖u v‖ ^ 2) := by
  have hu' : DifferentiableOn ℂ (fun y => u (x + y)) (ball 0 s) := by
    intro y hy
    have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    exact ((hu.differentiableAt (isOpen_ball.mem_nhds hxy)).comp y
      ((differentiable_const x).add differentiable_id y)).differentiableWithinAt
  have hρm : Measurable fun t : ℝ => (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) t :=
    measurable_const.indicator measurableSet_Iio
  have h := ReciprocityTheory.L2DbarEstimates.mv n s _ _ hu' hρm
    (fun t ht => Set.indicator_of_notMem (by simpa using ht) _)
  have e1 : ∀ y : V n, (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) ‖y‖ =
      (ball (0 : V n) s).indicator 1 y := by
    intro y
    by_cases hy : ‖y‖ < s
    · rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using hy)]; rfl
    · rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using hy)]
  simp only [add_zero, e1] at h
  rw [lintegral_indicator_one measurableSet_ball] at h
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_indicator measurableSet_ball,
    ← lintegral_add_left_eq_self (fun v => (ball x s).indicator (fun v => ENNReal.ofReal (‖u v‖ ^ 2)) v) x]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ ball (0 : V n) s
  · have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hxy]; simp
  · have hxy : x + y ∉ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hxy]; simp

theorem norm_fderiv_le_of_ball {n : ℕ} {p : V n} {ρ R M : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (u : V n → ℂ) (hu : DifferentiableOn ℂ u (ball p R)) (hM : ∀ x ∈ ball p R, ‖u x‖ ≤ M) :
    ‖fderiv ℂ u p‖ ≤ M / ρ := by
  first
  | exact @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | (apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded ..)

theorem l2_value_deriv_ball :
    ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : V n) (u : V n → ℂ),
      DifferentiableOn ℂ u (ball p r) →
        ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
          ENNReal.ofReal C * ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) := by
  intro n r hr
  set β : ℝ := (volume (ball (0 : V n) (r / 2))).toReal with hβdef
  have hβ : 0 < β := ENNReal.toReal_pos (measure_ball_pos volume _ (by linarith)).ne'
    measure_ball_lt_top.ne
  have hV : volume (ball (0 : V n) (r / 2)) = ENNReal.ofReal β :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  refine ⟨(1 + 16 / r ^ 2) / β, by positivity, fun p u hu => ?_⟩
  set I := ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) with hIdef
  by_cases hI : I = ⊤
  · rw [hI, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']; exact le_top
  set J := I.toReal with hJ
  have hI' : I = ENNReal.ofReal J := (ENNReal.ofReal_toReal hI).symm
  have hx : ∀ x ∈ ball p (r / 2), ‖u x‖ ^ 2 ≤ J / β := by
    intro x hx
    have hsub : ball x (r / 2) ⊆ ball p r := by
      apply ball_subset_ball'
      rw [mem_ball] at hx; linarith
    have h2 := (l2ball_sq_mul_vol_le u (hu.mono hsub)).trans (lintegral_mono_set hsub)
    rw [hV, ← ENNReal.ofReal_mul (sq_nonneg _), ← hIdef, hI'] at h2
    rw [le_div_iff₀ hβ]
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2
  set M := Real.sqrt (J / β) with hMdef
  have hJβ : 0 ≤ J / β := div_nonneg ENNReal.toReal_nonneg hβ.le
  have hMx : ∀ x ∈ ball p (r / 2), ‖u x‖ ≤ M := by
    intro x hx'
    have := Real.sqrt_le_sqrt (hx x hx')
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hD := norm_fderiv_le_of_ball (ρ := r / 4) (by positivity) (by linarith) u
    (hu.mono (ball_subset_ball (by linarith))) hMx
  have hD2 : ‖fderiv ℂ u p‖ ^ 2 ≤ 16 / r ^ 2 * (J / β) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hD 2
    refine this.trans (le_of_eq ?_)
    rw [div_pow, Real.sq_sqrt hJβ]; field_simp; ring
  have hp := hx p (mem_ball_self (by linarith))
  rw [hI', ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ J / β + 16 / r ^ 2 * (J / β) := add_le_add hp hD2
    _ = (1 + 16 / r ^ 2) / β * J := by ring

end

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_value_derivative_l2_ball : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : V n) (u : V n → ℂ), DifferentiableOn ℂ u (ball p r) → ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤ ENNReal.ofReal C * ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) := by
  atlas_forward_decl GlobalTheory.l2_value_deriv_ball
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.JetSmall

theorem ph_nsmul {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (H : La) (i : ι) (y : Y) (hy : y ∈ (A.chart i).source) (k : ℕ) :
    A.ph (k • H) i y = k * A.ph H i y := by
  induction k with
  | zero =>
    rw [zero_nsmul, Nat.cast_zero, zero_mul]
    have := A.ph_add 0 0 i y hy
    rw [add_zero] at this
    linarith
  | succ k ih =>
    rw [succ_nsmul, A.ph_add _ _ i y hy, ih]
    push_cast; ring

theorem main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H G : La) (i : ι) (p : V n) (r0 c Cq K : ℝ) (q : V n → ℂ), 0 < r0 → 0 < c → closedBall p r0 ⊆ (A.chart i).target → Differentiable ℂ q → (∀ v ∈ closedBall p r0, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ Cq * ‖v - p‖ ^ 2) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ D : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) D → DifferentiableOn ℂ (D i ∘ (A.chart i).symm) (ball p r0) → n0 A (G + k • H) D ≤ ENNReal.ofReal (K * Real.exp (-c * k)) → ‖D i ((A.chart i).symm p) * Complex.exp (-(k * q p))‖ ≤ ε ∧ ‖fderiv ℂ (fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v))) p‖ ≤ ε := by
  intro n Y _ _ _ _ _ ι La _ A H G i p r0 c Cq K q hr0 hc hsub hq hH ε hε

  set r : ℝ := min r0 (Real.sqrt (c / (2 * (|Cq| + 1)))) with hr
  have hCq1 : 0 < |Cq| + 1 := by positivity
  have hrpos : 0 < r := lt_min hr0 (Real.sqrt_pos.2 (by positivity))
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hr2 : r ^ 2 ≤ c / (2 * (|Cq| + 1)) := by
    have h1 : r ≤ Real.sqrt (c / (2 * (|Cq| + 1))) := min_le_right _ _
    have h2 := pow_le_pow_left₀ hrpos.le h1 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hsubr : closedBall p r ⊆ (A.chart i).target :=
    (closedBall_subset_closedBall hrr0).trans hsub
  have hball : ball p r ⊆ (A.chart i).target := ball_subset_closedBall.trans hsubr
  have hquad : ∀ v ∈ closedBall p r, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ c / 2 := by
    intro v hv
    have h := hH v (closedBall_subset_closedBall hrr0 hv)
    have hd : ‖v - p‖ ≤ r := by rw [← dist_eq_norm]; exact hv
    have hd2 : ‖v - p‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    have h3 : Cq * ‖v - p‖ ^ 2 ≤ |Cq| * ‖v - p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h4 : |Cq| * ‖v - p‖ ^ 2 ≤ |Cq| * (c / (2 * (|Cq| + 1))) :=
      mul_le_mul_of_nonneg_left (hd2.trans hr2) (abs_nonneg _)
    have h5 : |Cq| * (c / (2 * (|Cq| + 1))) ≤ c / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg Cq]
    linarith

  obtain ⟨M, hM⟩ := hyq_bdd (f := fun v => Real.exp (A.ph G i ((A.chart i).symm v))) (c := p) (r := r)
    ((A.smooth_ph G i).continuousOn.rexp.mono hsubr)
  have hM0 : 0 ≤ M := (Real.exp_pos _).le.trans (hM p (mem_closedBall_self hrpos.le))

  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.holomorphic_value_derivative_l2_ball n r hrpos

  have htend : Tendsto (fun k : ℕ => C * M * |K| * Real.exp (-(c / 2) * k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => -(c / 2) * (k : ℝ)) atTop atBot :=
      (tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (by linarith)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (C * M * |K|)
    simpa using h2
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 ((tendsto_order.1 htend).2 (ε ^ 2) (by positivity))
  refine ⟨k0, fun k hk D hD hDd hn0 => ?_⟩
  set u : V n → ℂ := fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v)) with hu
  have hud : DifferentiableOn ℂ u (ball p r) :=
    (hDd.mono (ball_subset_ball hrr0)).mul
      ((Complex.differentiable_exp.comp ((hq.const_mul (k : ℂ)).neg)).differentiableOn)
  have hest := hC p u hud

  set la : La := G + k • H
  set f : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y) with hf
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq _ D hD.2
      (fun j => (hD.1 j).continuousOn)).measurable

  have hpt : ∀ v ∈ ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤
      ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
        (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) := by
    intro v hv
    set y := (A.chart i).symm v
    have hy : y ∈ (A.chart i).source := (A.chart i).map_target (hball hv)
    have hns := hyq_nsq_chart A (A.kap + la) D i y hy (hD.2 i (A.pick y) y hy (A.mem_pick y))
    have hph : A.ph (A.kap + la) i y = A.ph A.kap i y + (A.ph G i y + k * A.ph H i y) := by
      rw [A.ph_add _ _ i y hy, A.ph_add _ _ i y hy, ph_nsmul A H i y hy]
    simp only [hf]
    rw [hns, hph, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hnu : ‖u v‖ ^ 2 = ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re)) := by
      simp only [hu, norm_mul, Complex.norm_exp, mul_pow]
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      simp [Complex.neg_re, Complex.mul_re]
      ring
    rw [hnu]
    have hq2 := hquad v (ball_subset_closedBall hv)
    have hMv := hM v (ball_subset_closedBall hv)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have key : Real.exp (-(2 * k * (q v).re)) ≤
        M * Real.exp (k * (c / 2)) * (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) *
          Real.exp (A.ph A.kap i y)) := by
      calc Real.exp (-(2 * k * (q v).re))
          ≤ Real.exp (A.ph G i y) * Real.exp (k * (c / 2)) *
              (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) *
                Real.exp (A.ph A.kap i y)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            apply Real.exp_le_exp.2
            nlinarith [mul_le_mul_of_nonneg_left hq2 hk0]
        _ ≤ _ := by gcongr
    calc ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re))
        ≤ ‖D i y‖ ^ 2 * (M * Real.exp (k * (c / 2)) *
          (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) * Real.exp (A.ph A.kap i y))) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring
  have hint : ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤
      ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D := by
    calc ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2)
        ≤ ∫⁻ v in ball p r, ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
            (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (M * Real.exp (k * (c / 2))) * ∫⁻ v in ball p r,
            f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D := by
          gcongr
          exact A.aap_lintegral_chart_le i f hfm _ hball

  have hall : ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
      ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by
    calc ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
            ENNReal.ofReal (|K| * Real.exp (-c * k))) := by
          refine hest.trans ?_
          gcongr
          refine hint.trans ?_
          gcongr
          exact hn0.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le))
      _ = ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
          congr 1
          have : Real.exp (k * (c / 2)) * Real.exp (-c * k) = Real.exp (-(c / 2) * k) := by
            rw [← Real.exp_add]; congr 1; ring
          calc C * (M * Real.exp (k * (c / 2)) * (|K| * Real.exp (-c * k)))
              = C * M * |K| * (Real.exp (k * (c / 2)) * Real.exp (-c * k)) := by ring
            _ = _ := by rw [this]
  have hsq : ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2 := by
    have hb := (hk0 k hk).le
    rcases (ENNReal.ofReal_le_ofReal_iff'.1 hall) with h | h
    · linarith
    · nlinarith [sq_nonneg ε]
  have h1 : ‖u p‖ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ‖fderiv ℂ u p‖]
  have h2 : ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ‖u p‖]
  exact ⟨by nlinarith [norm_nonneg (u p)], by nlinarith [norm_nonneg (fderiv ℂ u p)]⟩

end GlobalTheory.JetSmall
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peak_section_small_first_jet_normal_frame : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H G : La) (i : ι) (p : V n) (r0 c Cq K : ℝ) (q : V n → ℂ), 0 < r0 → 0 < c → closedBall p r0 ⊆ (A.chart i).target → Differentiable ℂ q → (∀ v ∈ closedBall p r0, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ Cq * ‖v - p‖ ^ 2) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ D : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) D → DifferentiableOn ℂ (D i ∘ (A.chart i).symm) (ball p r0) → n0 A (G + k • H) D ≤ ENNReal.ofReal (K * Real.exp (-c * k)) → ‖D i ((A.chart i).symm p) * Complex.exp (-(k * q p))‖ ≤ ε ∧ ‖fderiv ℂ (fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v))) p‖ ≤ ε := by
  atlas_forward_decl GlobalTheory.JetSmall.main
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem jets_approx_sections_of_positive : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ q : Y → V n → ℂ, (∀ P ∈ T, Differentiable ℂ (q P)) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + (G + k • H)) F ∧ ∀ P ∈ T, ‖F (A.pick P) P * Complex.exp (-(k * q P (A.chart (A.pick P) P))) - p P (A.chart (A.pick P) P)‖ ≤ ε ∧ ‖fderiv ℂ (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v) (A.chart (A.pick P) P)‖ ≤ ε := by
  intro n Y _ _ _ _ _ _ ι La _ A H hH T
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_atlasBallPartitionCover n Y ι La A
  obtain ⟨q, c, Cq, r0, hc, hr0, hqT, hrest⟩ := GlobalTheory.T.peak_sections_finite_weighted_atlas n Y ι La A C H hH T
  refine ⟨q, fun P hP => (hqT P hP).1, ?_⟩
  intro G p hp ε hε
  obtain ⟨K', t0, hK', hk6⟩ := GlobalTheory.T.rough_hormander_estimate_compact_manifold n Y ι La A C
  obtain ⟨k1, hk1⟩ := GlobalTheory.T.curvature_lower_bound_on_cover_balls n Y ι La A C H G hH t0
  obtain ⟨K, hK, hF0⟩ := hrest G p hp
  have hloc : ∀ P : Y, ∃ k0 : ℕ, P ∈ T → ∀ k ≥ k0, ∀ D : ι → Y → ℂ,
      A.IsSSec (A.kap + (G + k • H)) D →
      DifferentiableOn ℂ (D (A.pick P) ∘ (A.chart (A.pick P)).symm) (ball (A.chart (A.pick P) P) r0) →
      n0 A (G + k • H) D ≤ ENNReal.ofReal ((K' * K) * Real.exp (-c * k)) →
      ‖D (A.pick P) ((A.chart (A.pick P)).symm (A.chart (A.pick P) P)) *
          Complex.exp (-(k * q P (A.chart (A.pick P) P)))‖ ≤ ε ∧
      ‖fderiv ℂ (fun v => D (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)))
          (A.chart (A.pick P) P)‖ ≤ ε := by
    intro P
    by_cases hP : P ∈ T
    · obtain ⟨k0, hk0⟩ := GlobalTheory.T.peak_section_small_first_jet_normal_frame n Y ι La A H G (A.pick P) (A.chart (A.pick P) P) r0 c Cq
        (K' * K) (q P) hr0 hc (hqT P hP).2.1 (hqT P hP).1 (hqT P hP).2.2 ε hε
      exact ⟨k0, fun _ => hk0⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose k0 hk0 using hloc
  refine ⟨max k1 (T.sup k0), fun k hk => ?_⟩
  have hk1' : k1 ≤ k := le_trans (le_max_left _ _) hk
  obtain ⟨F0, hF0s, hF0b, hF0n⟩ := hF0 k
  obtain ⟨F, hFs, hFn⟩ := hk6 (G + k • H) t0 le_rfl (hk1 k hk1') F0 hF0s
  refine ⟨F, hFs, fun P hP => ?_⟩
  have hkP : k0 P ≤ k := le_trans (le_trans (Finset.le_sup hP) (le_max_right _ _)) hk
  have hDs : A.IsSSec (A.kap + (G + k • H)) (F0 - F) := by
    refine ⟨fun j => ?_, fun a b y ha hb => ?_⟩
    · have hd : DifferentiableOn ℂ (F j ∘ (A.chart j).symm) (A.chart j).target :=
        (hFs.1 j).mono fun _ hv => ⟨hv, trivial⟩
      have hF' : ContDiffOn ℝ ∞ (F j ∘ (A.chart j).symm) (A.chart j).target := fun v hv =>
        (hyq_contDiffAt_of_holo (A.chart j).open_target hd hv).contDiffWithinAt
      exact (hF0s.1 j).sub hF'
    · simp only [Pi.sub_apply]
      rw [hF0s.2 a b y ha hb, hFs.2 a b y trivial ha hb]
      ring
  have hb : ball (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target :=
    ball_subset_closedBall.trans (hqT P hP).2.1
  have hDd : DifferentiableOn ℂ ((F0 - F) (A.pick P) ∘ (A.chart (A.pick P)).symm)
      (ball (A.chart (A.pick P) P) r0) := by
    have hg : DifferentiableOn ℂ (fun v => p P v * Complex.exp (k * q P v) -
        F (A.pick P) ((A.chart (A.pick P)).symm v)) (ball (A.chart (A.pick P) P) r0) := by
      refine DifferentiableOn.sub ?_ ?_
      · exact ((hp P).mul (((hqT P hP).1.const_mul _).cexp)).differentiableOn
      · exact (hFs.1 (A.pick P)).mono fun v hv => ⟨hb hv, trivial⟩
    refine hg.congr fun v hv => ?_
    simp only [Function.comp_apply, Pi.sub_apply]
    rw [hF0b P hP v hv]
  have hDn : n0 A (G + k • H) (F0 - F) ≤ ENNReal.ofReal ((K' * K) * Real.exp (-c * k)) := by
    calc n0 A (G + k • H) (F0 - F) ≤ ENNReal.ofReal K' * n1 C (G + k • H) F0 := hFn
      _ ≤ ENNReal.ofReal K' * ENNReal.ofReal (K * Real.exp (-c * k)) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul hK', mul_assoc]
  obtain ⟨h1, h2⟩ := hk0 P hP k hkP (F0 - F) hDs hDd hDn
  have key : ∀ v ∈ ball (A.chart (A.pick P) P) r0,
      F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v =
        -((F0 - F) (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v))) := by
    intro v hv
    have h0 := hF0b P hP v hv
    have hE : Complex.exp (k * q P v) * Complex.exp (-(k * q P v)) = 1 := by
      rw [← Complex.exp_add]; simp
    simp only [Pi.sub_apply]
    rw [h0]
    linear_combination p P v * hE
  have hPx : (A.chart (A.pick P)).symm (A.chart (A.pick P) P) = P :=
    (A.chart (A.pick P)).left_inv (A.mem_pick P)
  have hx : A.chart (A.pick P) P ∈ ball (A.chart (A.pick P) P) r0 := mem_ball_self hr0
  refine ⟨?_, ?_⟩
  · have h3 := key _ hx
    rw [hPx] at h3 h1
    rw [h3, norm_neg]
    exact h1
  · have hev : (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v)
        =ᶠ[𝓝 (A.chart (A.pick P) P)]
        fun v => -((F0 - F) (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v))) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with v hv using key v hv
    rw [hev.fderiv_eq, fderiv_fun_neg, norm_neg]
    exact h2

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_approx_firstJets_positive : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ q : Y → V n → ℂ, (∀ P ∈ T, Differentiable ℂ (q P)) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + (G + k • H)) F ∧ ∀ P ∈ T, ‖F (A.pick P) P * Complex.exp (-(k * q P (A.chart (A.pick P) P))) - p P (A.chart (A.pick P) P)‖ ≤ ε ∧ ‖fderiv ℂ (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v) (A.chart (A.pick P) P)‖ ≤ ε := by
  atlas_forward_decl GlobalTheory.jets_approx_sections_of_positive
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem sections_coords_and_nonvanishing_at_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (T : Finset Y) (G : La), ∃ k0 : ℕ, ∀ k ≥ k0, ∃ (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (a : ι → Y → ℂ), A.IsSec (A.kap + k • H) t0 ∧ (∀ j, A.IsSec (A.kap + k • H) (t j)) ∧ A.IsSec (A.kap + (G + k • H)) a ∧ ∀ P ∈ T, t0 (A.pick P) P ≠ 0 ∧ A.IsCoordAt t0 t P ∧ a (A.pick P) P ≠ 0 := by
  intro n Y _ _ _ _ _ _ ι La _ A H hH T G
  obtain ⟨q, hq, hk9⟩ := GlobalTheory.T.exists_sections_approx_firstJets_positive n Y ι La A H hH T
  obtain ⟨ε, hε, hk10⟩ := GlobalTheory.T.quotient_jets_fderiv_det_ne_zero n
  obtain ⟨k0, hk0⟩ := hk9 0 (fun _ _ => 1) (fun _ => differentiable_const _) ε hε
  have hpj : ∀ j : Fin n, ∀ P : Y,
      Differentiable ℂ (fun v : V n => v j - (A.chart (A.pick P) P) j) := fun j P =>
    ((EuclideanSpace.proj (𝕜 := ℂ) j).differentiable).sub_const _
  choose kj hkj using fun j : Fin n =>
    hk9 0 (fun P v => v j - (A.chart (A.pick P) P) j) (hpj j) ε hε
  obtain ⟨ka, hka⟩ := hk9 G (fun _ _ => 1) (fun _ => differentiable_const _) (1/2) (by norm_num)
  refine ⟨max k0 (max ka (Finset.univ.sup kj)), fun k hk => ?_⟩
  have hk0' : k ≥ k0 := le_trans (le_max_left _ _) hk
  have hka' : k ≥ ka := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkj' : ∀ j, k ≥ kj j := fun j =>
    le_trans (le_trans (Finset.le_sup (f := kj) (Finset.mem_univ j))
      (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  obtain ⟨F0, hF0s, hF0⟩ := hk0 k hk0'
  choose Fj hFjs hFj using fun j => hkj j k (hkj' j)
  obtain ⟨Fa, hFas, hFa⟩ := hka k hka'
  rw [zero_add] at hF0s hFjs
  refine ⟨F0, Fj, Fa, hF0s, hFjs, hFas, fun P hP => ?_⟩
  set i := A.pick P with hi
  set p := A.chart i P with hp
  have hPs : P ∈ (A.chart i).source := A.mem_pick P
  have hpt : p ∈ (A.chart i).target := (A.chart i).map_source hPs
  have hsymm : (A.chart i).symm p = P := (A.chart i).left_inv hPs
  have hdiffF : ∀ F : ι → Y → ℂ, ∀ la, A.IsSec la F →
      DifferentiableAt ℂ (fun v => F i ((A.chart i).symm v)) p := by
    intro F la hF
    have h1 := hF.1 i
    have h2 : (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ = (A.chart i).target := by simp
    rw [h2] at h1
    exact h1.differentiableAt ((A.chart i).open_target.mem_nhds hpt)
  have hE : DifferentiableAt ℂ (fun v => Complex.exp (-((k : ℂ) * q P v))) p :=
    ((((hq P hP) p).const_mul (k : ℂ)).neg).cexp
  set w0 : V n → ℂ := fun v => F0 i ((A.chart i).symm v) * Complex.exp (-((k : ℂ) * q P v)) with hw0
  set w : Fin n → V n → ℂ := fun j v => Fj j i ((A.chart i).symm v) * Complex.exp (-((k : ℂ) * q P v)) with hw
  have hd0 : DifferentiableAt ℂ w0 p := (hdiffF F0 _ hF0s).mul hE
  have hdj : ∀ j, DifferentiableAt ℂ (w j) p := fun j => (hdiffF (Fj j) _ (hFjs j)).mul hE
  obtain ⟨h0a, h0b⟩ := hF0 P hP
  have e1 : ‖w0 p - 1‖ ≤ ε := by
    simp only [hw0, hsymm]; exact h0a
  have e2 : ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε := h0b
  have e3 : ∀ j, ‖w j p‖ ≤ ε := by
    intro j
    have := (hFj j P hP).1
    simp only [sub_self, sub_zero] at this
    simp only [hw, hsymm]; exact this
  have e4 : ∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε := fun j => (hFj j P hP).2
  obtain ⟨hne, hdet⟩ := hk10 p w0 w hd0 hdj e1 e2 e3 e4
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply hne
    simp only [hw0, hsymm, h0, zero_mul]
  · unfold WeightedAtlas.IsCoordAt
    have hfun : A.zLoc F0 Fj i = fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) := by
      funext v
      simp only [WeightedAtlas.zLoc, hw, hw0]
      congr 1
      funext j
      rw [mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
    rw [← hi, ← hp, hfun]
    exact hdet
  · intro h0
    have := (hFa P hP).1
    rw [h0, zero_mul, zero_sub, norm_neg, norm_one] at this
    norm_num at this

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_coords_nonvanishing_at_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (T : Finset Y) (G : La), ∃ k0 : ℕ, ∀ k ≥ k0, ∃ (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (a : ι → Y → ℂ), A.IsSec (A.kap + k • H) t0 ∧ (∀ j, A.IsSec (A.kap + k • H) (t j)) ∧ A.IsSec (A.kap + (G + k • H)) a ∧ ∀ P ∈ T, t0 (A.pick P) P ≠ 0 ∧ A.IsCoordAt t0 t P ∧ a (A.pick P) P ≠ 0 := by
  atlas_forward_decl GlobalTheory.sections_coords_and_nonvanishing_at_finset
end
