import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyFractionalIdealRealLatticeImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZLatticeFractionalIdealRealLatticeImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFractionalIdealRealLatticeImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDual
import Formalism.LatticeTheta.ThetaShiftInversion
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummand

section
section
noncomputable section

open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform

namespace GlobalTheory.HeckeTwo.HDecay

theorem fourier_decay_of_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hi : ∀ n : ℕ, Integrable (iteratedDeriv n f)) (N : ℕ) :
    ∃ C : ℝ, ∀ ν : ℝ, ‖𝓕 f ν‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  have hbound : ∀ (u : ℝ → ℂ) (ν : ℝ), ‖𝓕 u ν‖ ≤ ∫ t, ‖u t‖ := by
    intro u ν
    rw [Real.fourier_real_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext t
    simp [Circle.norm_smul]
  set A := ∫ t, ‖f t‖
  set B := ∫ t, ‖iteratedDeriv N f t‖
  refine ⟨2 ^ N * (A + B / (2 * Real.pi) ^ N), fun ν => ?_⟩
  have h1 : ‖𝓕 f ν‖ ≤ A := hbound f ν
  have h2 : (2 * Real.pi) ^ N * (|ν| ^ N * ‖𝓕 f ν‖) ≤ B := by
    have := hbound (iteratedDeriv N f) ν
    rw [Real.fourier_iteratedDeriv (N := ⊤) hf (fun n _ => hi n) le_top] at this
    have e : ‖(2 * (Real.pi : ℂ) * I * (ν : ℂ)) ^ N • 𝓕 f ν‖ = (2 * Real.pi) ^ N * (|ν| ^ N * ‖𝓕 f ν‖) := by
      rw [norm_smul, norm_pow]
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        abs_of_pos Real.pi_pos, mul_one]
      ring
    rw [e] at this
    exact this
  have hx : 0 ≤ |ν| := abs_nonneg ν
  have hq : 0 ≤ ‖𝓕 f ν‖ := norm_nonneg _
  have hpi : 0 < (2 * Real.pi) ^ N := by positivity
  have h3 : |ν| ^ N * ‖𝓕 f ν‖ ≤ B / (2 * Real.pi) ^ N := by
    rw [le_div_iff₀ hpi]; linarith
  have h4 : (1 + |ν|) ^ N ≤ 2 ^ N * (1 + |ν| ^ N) := by
    rcases le_total 1 |ν| with h | h
    · calc (1 + |ν|) ^ N ≤ (2 * |ν|) ^ N := by gcongr; linarith
        _ = 2 ^ N * |ν| ^ N := by rw [mul_pow]
        _ ≤ 2 ^ N * (1 + |ν| ^ N) := by gcongr; linarith
    · calc (1 + |ν|) ^ N ≤ (2 : ℝ) ^ N := by gcongr; linarith
        _ ≤ 2 ^ N * (1 + |ν| ^ N) := by
          have : 0 ≤ |ν| ^ N := by positivity
          nlinarith [pow_pos (two_pos : (0:ℝ) < 2) N]
  have hpos : 0 < (1 + |ν|) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖𝓕 f ν‖ * (1 + |ν|) ^ N ≤ ‖𝓕 f ν‖ * (2 ^ N * (1 + |ν| ^ N)) := by gcongr
    _ = 2 ^ N * (‖𝓕 f ν‖ + |ν| ^ N * ‖𝓕 f ν‖) := by ring
    _ ≤ 2 ^ N * (A + B / (2 * Real.pi) ^ N) := by gcongr

end GlobalTheory.HeckeTwo.HDecay

namespace GlobalTheory.HeckeTwo.HDecay

variable (σ : ℂ) (y : ℝ)

def gI (t : ℝ) : ℂ := ((t : ℂ) + (y : ℂ) * I)⁻¹

def hI (t : ℝ) : ℂ := ((t : ℂ) - (y : ℂ) * I)⁻¹

def eF (t : ℝ) : ℂ := Complex.exp (-σ * (Real.log (t ^ 2 + y ^ 2) : ℂ))

def wF (a b : ℕ) (t : ℝ) : ℂ := gI y t ^ (a + 2) * hI y t ^ b * eF σ y t

variable {y}

theorem add_I_ne (hy : y ≠ 0) (t : ℝ) : (t : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

theorem sub_I_ne (hy : y ≠ 0) (t : ℝ) : (t : ℂ) - (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

theorem sq_add_sq_pos (hy : y ≠ 0) (t : ℝ) : 0 < t ^ 2 + y ^ 2 := by
  have : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  positivity

theorem hasDerivAt_gI (hy : y ≠ 0) (t : ℝ) : HasDerivAt (gI y) (-(gI y t) ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) + (y : ℂ) * I) 1 t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).add_const ((y : ℂ) * I)
  refine (h1.inv (add_I_ne hy t)).congr_deriv ?_
  simp [gI, div_eq_mul_inv, inv_pow]

theorem hasDerivAt_hI (hy : y ≠ 0) (t : ℝ) : HasDerivAt (hI y) (-(hI y t) ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) - (y : ℂ) * I) 1 t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).sub_const ((y : ℂ) * I)
  refine (h1.inv (sub_I_ne hy t)).congr_deriv ?_
  simp [hI, div_eq_mul_inv, inv_pow]

theorem gI_add_hI (hy : y ≠ 0) (t : ℝ) :
    gI y t + hI y t = ((2 * t / (t ^ 2 + y ^ 2) : ℝ) : ℂ) := by
  have h1 := add_I_ne hy t
  have h2 := sub_I_ne hy t
  have h3 : ((t ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sq_add_sq_pos hy t).ne'
  have hprod : ((t : ℂ) + (y : ℂ) * I) * ((t : ℂ) - (y : ℂ) * I) = ((t ^ 2 + y ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  unfold gI hI
  rw [inv_add_inv h1 h2, hprod]
  push_cast
  ring

theorem hasDerivAt_eF (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (eF σ y) (-σ * (gI y t + hI y t) * eF σ y t) t := by
  have hpos := sq_add_sq_pos hy t
  have hL : HasDerivAt (fun s : ℝ => Real.log (s ^ 2 + y ^ 2)) (2 * t / (t ^ 2 + y ^ 2)) t := by
    have := ((hasDerivAt_pow 2 t).add_const (y ^ 2)).log hpos.ne'
    convert this using 1
    ring
  have hc := ((hL.ofReal_comp).const_mul (-σ)).cexp
  refine hc.congr_deriv ?_
  rw [gI_add_hI hy t]
  simp only [eF]
  ring

theorem hasDerivAt_wF (hy : y ≠ 0) (a b : ℕ) (t : ℝ) :
    HasDerivAt (wF σ y a b)
      (-((a : ℂ) + 2 + σ) * wF σ y (a + 1) b t - ((b : ℂ) + σ) * wF σ y a (b + 1) t) t := by
  have hg := (hasDerivAt_gI hy t).pow (a + 2)
  have hh : HasDerivAt (fun s => hI y s ^ b) (-(b : ℂ) * hI y t ^ (b + 1)) t := by
    rcases b with _ | b
    · simpa using hasDerivAt_const t (1 : ℂ)
    · refine ((hasDerivAt_hI hy t).pow (b + 1)).congr_deriv ?_
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  have := (hg.mul hh).mul (hasDerivAt_eF σ hy t)
  refine this.congr_deriv ?_
  have e : a + 2 - 1 = a + 1 := by omega
  simp only [wF, e, Pi.mul_apply, Pi.pow_apply]
  push_cast
  ring

end GlobalTheory.HeckeTwo.HDecay

namespace GlobalTheory.HeckeTwo.HDecay

variable (σ : ℂ) (y : ℝ)

def wSpan : Submodule ℂ (ℝ → ℂ) := Submodule.span ℂ (Set.range fun p : ℕ × ℕ => wF σ y p.1 p.2)

variable {σ y}

theorem wSpan_deriv (hy : y ≠ 0) {F : ℝ → ℂ} (hF : F ∈ wSpan σ y) :
    Differentiable ℝ F ∧ deriv F ∈ wSpan σ y := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hF
    refine ⟨fun t => (hasDerivAt_wF σ hy a b t).differentiableAt, ?_⟩
    have e : deriv (wF σ y a b) =
        (-((a : ℂ) + 2 + σ)) • wF σ y (a + 1) b - ((b : ℂ) + σ) • wF σ y a (b + 1) := by
      funext t
      rw [(hasDerivAt_wF σ hy a b t).deriv]
      simp
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a + 1, b), rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b + 1), rfl⟩))
  | zero =>
    refine ⟨differentiable_const 0, ?_⟩
    have e : deriv (0 : ℝ → ℂ) = 0 := by
      funext t
      exact deriv_const t 0
    rw [e]
    exact zero_mem _
  | add F G _ _ hF hG =>
    refine ⟨hF.1.add hG.1, ?_⟩
    have e : deriv (F + G) = deriv F + deriv G := by
      funext t
      exact deriv_add (hF.1 t) (hG.1 t)
    rw [e]
    exact add_mem hF.2 hG.2
  | smul c F _ hF =>
    refine ⟨hF.1.const_smul c, ?_⟩
    have e : deriv (c • F) = c • deriv F := by
      funext t
      exact deriv_const_smul c (hF.1 t)
    rw [e]
    exact Submodule.smul_mem _ c hF.2

theorem iteratedDeriv_mem (hy : y ≠ 0) (n : ℕ) : iteratedDeriv n (wF σ y 0 0) ∈ wSpan σ y := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    exact Submodule.subset_span ⟨(0, 0), rfl⟩
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (wSpan_deriv hy ih).2

theorem contDiff_wF (hy : y ≠ 0) : ContDiff ℝ ∞ (wF σ y 0 0) :=
  contDiff_of_differentiable_iteratedDeriv fun m _ => (wSpan_deriv hy (iteratedDeriv_mem hy m)).1

theorem wF_integrable (hy : y ≠ 0) (hσ : 0 < σ.re) (a b : ℕ) : Integrable (wF σ y a b) := by
  have hc : Continuous (wF σ y a b) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_wF σ hy a b t).continuousAt
  have hy2 : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  have hay : 0 < |y| := abs_pos.2 hy
  set K := (1 + (y ^ 2)⁻¹) * |y|⁻¹ ^ (a + b) * Real.exp (-σ.re * Real.log (y ^ 2)) with hK
  refine (integrable_inv_one_add_sq.const_mul K).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hpos := sq_add_sq_pos hy t
  have hnorm : ‖(t : ℂ) + (y : ℂ) * I‖ ^ 2 = t ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hnorm' : ‖(t : ℂ) - (y : ℂ) * I‖ ^ 2 = t ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg, Complex.normSq_add_mul_I]
    ring
  have him : |y| ≤ ‖(t : ℂ) + (y : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((t : ℂ) + (y : ℂ) * I)
    simpa using this
  have him' : |y| ≤ ‖(t : ℂ) - (y : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((t : ℂ) - (y : ℂ) * I)
    simpa using this
  have hg1 : ‖gI y t‖ ≤ |y|⁻¹ := by
    rw [gI, norm_inv]
    exact inv_anti₀ hay him
  have hh1 : ‖hI y t‖ ≤ |y|⁻¹ := by
    rw [hI, norm_inv]
    exact inv_anti₀ hay him'
  have hg2 : ‖gI y t‖ ^ 2 ≤ (1 + (y ^ 2)⁻¹) * (1 + t ^ 2)⁻¹ := by
    rw [gI, norm_inv, inv_pow, hnorm]
    have key : 1 + t ^ 2 ≤ (1 + (y ^ 2)⁻¹) * (t ^ 2 + y ^ 2) := by
      rw [add_mul, one_mul, inv_mul_eq_div, add_div, div_self hy2.ne']
      have : 0 ≤ t ^ 2 / y ^ 2 := by positivity
      nlinarith
    calc (t ^ 2 + y ^ 2)⁻¹ = (1 + (y ^ 2)⁻¹) * ((1 + (y ^ 2)⁻¹) * (t ^ 2 + y ^ 2))⁻¹ := by
          field_simp
      _ ≤ (1 + (y ^ 2)⁻¹) * (1 + t ^ 2)⁻¹ := by gcongr
  have hE : ‖eF σ y t‖ ≤ Real.exp (-σ.re * Real.log (y ^ 2)) := by
    rw [eF, Complex.norm_exp]
    apply Real.exp_le_exp.2
    have hre : (-σ * (Real.log (t ^ 2 + y ^ 2) : ℂ)).re = -σ.re * Real.log (t ^ 2 + y ^ 2) := by
      simp [Complex.mul_re]
    rw [hre]
    have hlog : Real.log (y ^ 2) ≤ Real.log (t ^ 2 + y ^ 2) :=
      Real.log_le_log hy2 (by nlinarith [sq_nonneg t])
    nlinarith
  calc ‖wF σ y a b t‖ = ‖gI y t‖ ^ 2 * ‖gI y t‖ ^ a * ‖hI y t‖ ^ b * ‖eF σ y t‖ := by
        simp only [wF, norm_mul, norm_pow]
        ring
    _ ≤ ((1 + (y ^ 2)⁻¹) * (1 + t ^ 2)⁻¹) * |y|⁻¹ ^ a * |y|⁻¹ ^ b *
          Real.exp (-σ.re * Real.log (y ^ 2)) := by gcongr
    _ = K * (1 + t ^ 2)⁻¹ := by
        rw [hK]
        ring

theorem wSpan_integrable (hy : y ≠ 0) (hσ : 0 < σ.re) {F : ℝ → ℂ} (hF : F ∈ wSpan σ y) :
    Integrable F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hF
    exact wF_integrable hy hσ a b
  | zero => exact integrable_zero _ _ _
  | add F G _ _ hF hG => exact hF.add hG
  | smul c F _ hF => exact hF.smul c

theorem phi_eq_wF (hy : y ≠ 0) (t : ℝ) : phi σ ((t : ℂ) + (y : ℂ) * I) = wF σ y 0 0 t := by
  have hz := add_I_ne hy t
  have hn : 0 < ‖(t : ℂ) + (y : ℂ) * I‖ := norm_pos_iff.2 hz
  simp only [phi, wF, gI, eF, pow_zero, mul_one, zero_add]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_log hn.le]
  congr 1
  have e : t ^ 2 + y ^ 2 = ‖(t : ℂ) + (y : ℂ) * I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [e, Real.log_pow]
  push_cast
  ring

theorem hTrans_eq_fourier (hy : y ≠ 0) (ν : ℝ) : hTrans σ ν y = 𝓕 (wF σ y 0 0) ν := by
  rw [Real.fourier_real_eq_integral_exp_smul, hTrans]
  congr 1
  funext t
  rw [phi_eq_wF hy t, smul_eq_mul, mul_comm (Complex.exp _)]
  congr 2
  push_cast
  ring

end GlobalTheory.HeckeTwo.HDecay

namespace GlobalTheory.HeckeTwo

theorem hTrans_rapid_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ,
    ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  intro σ hσ y hy N
  obtain ⟨C, hC⟩ := HDecay.fourier_decay_of_iteratedDeriv (HDecay.contDiff_wF hy)
    (fun n => HDecay.wSpan_integrable hy hσ (HDecay.iteratedDeriv_mem hy n)) N
  exact ⟨C, fun ν => by rw [HDecay.hTrans_eq_fourier hy ν]; exact hC ν⟩

end GlobalTheory.HeckeTwo
end
end

open NumberField Complex MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierTransform_rapid_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ, ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  atlas_forward_decl GlobalTheory.HeckeTwo.hTrans_rapid_decay
end

section
section
open NumberField Complex MeasureTheory

namespace GlobalTheory.HeckeTwo.PhiLine

theorem norm_line_sq (t y : ℝ) : ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = t ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp; ring

theorem abs_le_norm_line (t y : ℝ) : |y| ≤ ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ := by
  have := Complex.abs_im_le_norm ((t : ℂ) + (y : ℂ) * Complex.I)
  simpa using this

theorem line_ne_zero (t y : ℝ) (hy : y ≠ 0) : ((t : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

theorem norm_phi_le (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) (t : ℝ) :
    ‖GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      |y| ^ (-2 * σ.re) * (min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹ := by
  set w : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hw
  have hay : 0 < |y| := abs_pos.2 hy
  have hle : |y| ≤ ‖w‖ := abs_le_norm_line t y
  have hpos : 0 < ‖w‖ := lt_of_lt_of_le hay hle
  have hsq : ‖w‖ ^ 2 = t ^ 2 + y ^ 2 := norm_line_sq t y
  unfold GlobalTheory.HeckeTwo.phi
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-2 * σ).re = -2 * σ.re := by simp
  rw [hre]
  have h1 : ‖w‖ ^ (-2 * σ.re) ≤ |y| ^ (-2 * σ.re) :=
    Real.rpow_le_rpow_of_nonpos hay hle (by linarith)
  have hy2 : 0 < y ^ 2 := by positivity
  have hm : 0 < min 1 (y ^ 2) := lt_min one_pos hy2
  have h2 : ‖w‖⁻¹ ^ 2 ≤ (min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹ := by
    rw [inv_pow, hsq, ← mul_inv]
    apply inv_anti₀ (by positivity)
    have := min_le_left 1 (y ^ 2)
    have := min_le_right 1 (y ^ 2)
    nlinarith [sq_nonneg t]
  calc ‖w‖⁻¹ ^ 2 * ‖w‖ ^ (-2 * σ.re) ≤ ((min 1 (y ^ 2))⁻¹ * (1 + t ^ 2)⁻¹) * |y| ^ (-2 * σ.re) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = _ := by ring

theorem phi_line (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
      MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  have hw : Continuous (fun t : ℝ => ((t : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
  have hcont : Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
    unfold GlobalTheory.HeckeTwo.phi
    refine Continuous.mul ((hw.inv₀ fun t => line_ne_zero t y hy).pow 2) ?_
    refine Continuous.cpow (Complex.continuous_ofReal.comp hw.norm) continuous_const ?_
    intro t
    exact Complex.ofReal_mem_slitPlane.2
      (lt_of_lt_of_le (abs_pos.2 hy) (abs_le_norm_line t y))
  refine ⟨hcont, ?_⟩
  refine MeasureTheory.Integrable.mono' (integrable_inv_one_add_sq.const_mul
    (|y| ^ (-2 * σ.re) * (min 1 (y ^ 2))⁻¹)) hcont.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => norm_phi_le σ hσ y hy t

end GlobalTheory.HeckeTwo.PhiLine

theorem GlobalTheory.HeckeTwo.phi_line_continuous_integrable : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 →
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
      MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) :=
  fun σ hσ y hy => GlobalTheory.HeckeTwo.PhiLine.phi_line σ hσ y hy
end

open NumberField Complex MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwoKernelPhi_line_continuous_integrable : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧ MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  atlas_forward_decl GlobalTheory.HeckeTwo.phi_line_continuous_integrable
end

section
section
open NumberField Complex
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeTwo

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem norm_phi_le (σ w : ℂ) (hσ : 0 < σ.re) (c : ℝ) (hc : 0 < c) (hcw : c ≤ |w.im|) :
    ‖phi σ w‖ ≤ ‖w⁻¹ ^ 2‖ * c ^ (-2 * σ.re) := by
  have hw : 0 < ‖w‖ := lt_of_lt_of_le hc (hcw.trans (Complex.abs_im_le_norm w))
  unfold phi
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hre : (-2 * σ).re = -2 * σ.re := by simp
  rw [hre]
  exact Real.rpow_le_rpow_of_nonpos hc (hcw.trans (Complex.abs_im_le_norm w)) (by linarith)

theorem summable_latSum (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : Frac F) (σ : ℂ)
    (hσ : 0 < σ.re) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) (b : F) (hb : b ≠ 0) :
    Summable (fun a : {a : F // a ∈ latM 𝔞} =>
      ∏ τ : Emb F, phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := by
  classical
  have hM : latM 𝔞 ≠ 0 := by
    rw [latM_eq_dual]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero 𝔞)
  set z' : Emb F → ℂ := fun τ => ((τ b : ℝ) : ℂ) * z τ with hz'
  have hc : ∀ τ : Emb F, 0 < |τ b * (z τ).im| := fun τ =>
    abs_pos.2 (mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne')
  have him : ∀ τ : Emb F, (z' τ).im ≠ 0 := fun τ => by
    have := hc τ
    simp only [hz', Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact abs_pos.1 this
  have hs := GlobalTheory.LipschitzTR.summable_lhsTerm_ideal F (latM 𝔞) hM 2 le_rfl z' him
  have hs' : Summable (fun a : {a : F // a ∈ latM 𝔞} => GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm 2 z' a.1) := hs
  set C : ℝ := ∏ τ : Emb F, |τ b * (z τ).im| ^ (-2 * σ.re) with hC
  refine Summable.of_norm_bounded ((summable_norm_iff.2 hs').mul_left C) fun a => ?_
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm 2 z' a.1 =
      ∏ τ : Emb F, (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)⁻¹ ^ 2 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm
    rw [zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hz', inv_pow, add_comm]
  rw [hl, norm_prod, norm_prod, hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  rw [mul_comm (|τ b * (z τ).im| ^ (-2 * σ.re))]
  refine norm_phi_le σ _ hσ _ (hc τ) (le_of_eq ?_)
  simp

end GlobalTheory.HeckeTwo
end

open NumberField Complex
open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_heckeWeightTwoLatticeSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 → Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := by
  atlas_forward_decl GlobalTheory.HeckeTwo.summable_latSum
end

section
section
open MeasureTheory

theorem GlobalTheory.prod_rpow_decay_isBigO_cocompact : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by
  intro ι _ g b hb hg
  classical
  choose C hC using hg
  have hC0 : ∀ i, 0 ≤ C i := fun i => by
    have h := hC i 0
    simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  refine Asymptotics.IsBigO.of_bound ((∏ i, C i) * n ^ b) ?_
  have hev : ∀ᶠ v : EuclideanSpace ℝ ι in Filter.cocompact _, 0 < ‖v‖ :=
    tendsto_norm_cocompact_atTop.eventually (Filter.eventually_gt_atTop 0)
  filter_upwards [hev] with v hv
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : v = 0 := Subsingleton.elim _ _
    simp [this] at hv
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) Finset.univ_nonempty
  have hn1 : (1:ℝ) ≤ n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hnorm : ‖v‖ ≤ n * |v i₀| := by
    have h2 : ‖v‖ ^ 2 ≤ (n * |v i₀|) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖v.ofLp i‖ ^ 2 ≤ ∑ _i : ι, |v i₀| ^ 2 := Finset.sum_le_sum fun i _ => by
              rw [Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hi₀ i (Finset.mem_univ _)) 2
        _ = n * |v i₀| ^ 2 := by simp [hn]
        _ ≤ (n * |v i₀|) ^ 2 := by
              rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hnpos : 0 < n := by linarith
  have hpos : 0 < ‖v‖ / n := by positivity
  have hle : ‖v‖ / n ≤ 1 + |v i₀| := by
    rw [div_le_iff₀ hnpos]; nlinarith [abs_nonneg (v i₀)]
  have hw : (1 + |v i₀|) ^ (-b) ≤ n ^ b * ‖v‖ ^ (-b) := by
    calc (1 + |v i₀|) ^ (-b) ≤ (‖v‖ / n) ^ (-b) := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
      _ = n ^ b * ‖v‖ ^ (-b) := by
        rw [Real.div_rpow (norm_nonneg _) hnpos.le, Real.rpow_neg hnpos.le, div_inv_eq_mul, mul_comm]
  have hrest : ∏ i ∈ Finset.univ.erase i₀, ‖g i (v i)‖ ≤ ∏ i ∈ Finset.univ.erase i₀, C i :=
    Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hC i (v i)).trans
      (mul_le_of_le_one_right (hC0 i)
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (v i)]) (by linarith))))
  have h0 : ‖g i₀ (v i₀)‖ ≤ C i₀ * (n ^ b * ‖v‖ ^ (-b)) :=
    (hC i₀ _).trans (mul_le_mul_of_nonneg_left hw (hC0 i₀))
  have hsplitg := Finset.mul_prod_erase Finset.univ (fun i => ‖g i (v i)‖) (Finset.mem_univ i₀)
  have hsplitC := Finset.mul_prod_erase Finset.univ C (Finset.mem_univ i₀)
  rw [norm_prod, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← hsplitg, ← hsplitC]
  calc ‖g i₀ (v i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖g i (v i)‖
      ≤ C i₀ * (n ^ b * ‖v‖ ^ (-b)) * ∏ i ∈ Finset.univ.erase i₀, C i :=
        mul_le_mul h0 hrest (Finset.prod_nonneg fun i _ => norm_nonneg _)
          (mul_nonneg (hC0 i₀) (mul_nonneg (Real.rpow_nonneg hnpos.le _) (Real.rpow_nonneg (norm_nonneg _) _)))
    _ = C i₀ * (∏ i ∈ Finset.univ.erase i₀, C i) * n ^ b * ‖v‖ ^ (-b) := by ring
end

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_rpow_decay_isBigO_cocompact' : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by
  atlas_forward_decl GlobalTheory.prod_rpow_decay_isBigO_cocompact
end

section
section
open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.HeckeTwoPoisson

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.LipschitzTR

theorem hTrans_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ,
    ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := GlobalTheory.T.heckePhiFourierTransform_rapid_decay

theorem phi_line : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 →
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
    Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := GlobalTheory.T.heckeWeightTwoKernelPhi_line_continuous_integrable

theorem summable_lat : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 →
    Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} =>
      ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := GlobalTheory.T.summable_heckeWeightTwoLatticeSum

theorem prod_isBigO : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b →
    (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) →
    (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)]
      (fun v => ‖v‖ ^ (-b)) := GlobalTheory.T.prod_rpow_decay_isBigO_cocompact'

theorem fourier_prod (ι : Type) [Fintype ι] (f : ι → ℝ → ℂ) (x : EuclideanSpace ℝ ι) :
    𝓕 (fun ξ : EuclideanSpace ℝ ι => ∏ i, f i (ξ i)) x = ∏ i, 𝓕 (f i) (x i) := by
  simp only [Real.fourier_eq', Real.fourier_real_eq]
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum,
    Finset.sum_mul]

theorem remb_inj {F : Type} [Field F] [NumberField F] [IsTotallyReal F] : Function.Injective (remb F) := by
  intro a b h
  have hne : Nonempty (F →+* ℝ) := by
    rw [← Fintype.card_pos_iff, GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb]
    exact Module.finrank_pos
  have h1 := congrArg (fun v : RSp F => v (Classical.choice hne)) h
  simp only [remb_apply] at h1
  exact (Classical.choice hne).injective h1

theorem hTrans_eq_fourier (σ : ℂ) (y : ℝ) :
    (fun ν : ℝ => hTrans σ ν y) = 𝓕 (fun t : ℝ => phi σ ((t : ℂ) + (y : ℂ) * I)) := by
  funext ν
  rw [Real.fourier_real_eq]
  unfold hTrans
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, Real.fourierChar_apply]
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem continuous_hTrans (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun ν : ℝ => hTrans σ ν y) := by
  rw [hTrans_eq_fourier]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (phi_line σ hσ y hy).2

theorem fourier_mod (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) (c s : ℝ) :
    𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s =
      phi σ (((c - s : ℝ) : ℂ) + (y : ℂ) * I) := by
  set f : ℝ → ℂ := fun t => phi σ ((t : ℂ) + (y : ℂ) * I) with hf
  obtain ⟨hfc, hfi⟩ := phi_line σ hσ y hy
  have hH := hTrans_eq_fourier σ y
  have hFi : Integrable (𝓕 f) := by
    obtain ⟨C, hC⟩ := hTrans_decay σ hσ y hy 2
    have h2 : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
      integrable_one_add_norm (by simp)
    refine (h2.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · rw [← hH]; exact (continuous_hTrans σ hσ y hy).aestronglyMeasurable
    · have := hC t
      rw [← hH]
      simpa [Real.norm_eq_abs] using this
  have hinv : 𝓕⁻ (𝓕 f) = f := Continuous.fourierInv_fourier_eq hfc hfi hFi
  have hmod : 𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s =
      𝓕 (𝓕 f) (s - c) := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← hH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hmod]
  have h3 := congrFun hinv (-(s - c))
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h3
  rw [h3, hf]
  congr 2
  push_cast
  ring

theorem poisson : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ),
    0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 →
    Summable (fun ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)} => GlobalTheory.HeckeTwo.fTerm σ z b ν.1) ∧
    HasSum (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ))
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * ∑' ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)}, GlobalTheory.HeckeTwo.fTerm σ z b ν.1) := by
  intro F _ _ _ 𝔞 σ hσ z hz b hb
  classical
  set A : FractionalIdeal (𝓞 F)⁰ F := (𝔞 : FractionalIdeal (𝓞 F)⁰ F) with hA
  have hA0 : A ≠ 0 := 𝔞.ne_zero
  haveI : DiscreteTopology (latOf A) := discrete_latOf F A
  haveI : IsZLattice ℝ (latOf A) := isZLattice_latOf F A hA0
  set L := latOf A with hL
  have hdual : Formalism.H.dual L = latOf (latM 𝔞) := by
    rw [hL, dual_latOf_eq_latOf_traceDual F A hA0, latM_eq_dual]
  have hcov : ZLattice.covolume L = omegaFactor 𝔞 := by
    rw [hL, GlobalTheory.LipschitzCovol.covolume_latOf F A hA0, GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol, omegaFactor, dF, nrm,
      Real.sqrt_eq_rpow]
  obtain ⟨h1, h2⟩ := Formalism.H.dualIsLattice (RSp F) L
  haveI : DiscreteTopology (Formalism.H.dual L) := h1

  have hyτ : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  set g : Emb F → ℝ → ℂ := fun τ t =>
    Complex.exp (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ)) * hTrans σ t (τ b * (z τ).im) with hg
  set Ψ : RSp F → ℂ := fun v => ∏ τ, g τ (v τ) with hΨ
  have hΨν : ∀ ν : F, Ψ (remb F ν) = fTerm σ z b ν := by
    intro ν
    simp only [hΨ, hg, remb_apply, fTerm]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 3
    push_cast
    ring
  have hgn : ∀ τ t, ‖g τ t‖ = ‖hTrans σ t (τ b * (z τ).im)‖ := by
    intro τ t
    simp only [hg, norm_mul]
    rw [show (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ)) =
      ((2 * Real.pi * (t * (τ b * (z τ).re)) : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hΨc : Continuous Ψ := by
    refine continuous_finset_prod _ fun τ _ => ?_
    refine Continuous.comp (g := g τ) ?_ ((EuclideanSpace.proj τ : RSp F →L[ℝ] ℝ).continuous)
    exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ))).mul
      (continuous_hTrans σ hσ _ (hyτ τ))
  set N : ℕ := Module.finrank ℝ (RSp F) + 1 with hN
  have hbN : (Module.finrank ℝ (RSp F) : ℝ) < (N : ℝ) := by rw [hN]; push_cast; linarith
  have hΨO : Ψ =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-(N : ℝ)) :=
    prod_isBigO (Emb F) g N (Nat.cast_nonneg _) fun τ => by
      obtain ⟨C, hC⟩ := hTrans_decay σ hσ _ (hyτ τ) N
      exact ⟨C, fun t => (hgn τ t).symm ▸ hC t⟩
  obtain ⟨hint, hsumx, hGc, hGper⟩ := Formalism.H.poisson_periodization (RSp F) L Ψ hΨc (N : ℝ) hbN hΨO
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hD := ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) (volume : Measure (RSp F))
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  have hcoef : ∀ μ : Formalism.H.dual L, (∫ y in D, (∑' l : L, Ψ ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) = 𝓕 Ψ μ :=
    fun μ => Formalism.H.unfolding_fourier_coefficient (RSp F) L Ψ hint D hD μ μ.2

  have hFΨ : ∀ a : F, 𝓕 Ψ (remb F (-a)) = ∏ τ : Emb F, phi σ (((τ a : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ) := by
    intro a
    rw [hΨ, fourier_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [remb_apply, hg]
    simp only
    rw [fourier_mod σ hσ _ (hyτ τ)]
    congr 1
    apply Complex.ext <;> simp <;> ring
  have hDmem : ∀ x, x ∈ Formalism.H.dual L ↔ ∃ a ∈ latM 𝔞, remb F a = x := by
    intro x; rw [hdual]; exact mem_latOf _ x
  have hLmem : ∀ x, x ∈ L ↔ ∃ ν ∈ A, remb F ν = x := by
    intro x; rw [hL]; exact mem_latOf _ x
  let eM : {a : F // a ∈ latM 𝔞} ≃ Formalism.H.dual L := Equiv.ofBijective
    (fun a => ⟨remb F (-a.1), (hDmem _).2 ⟨-a.1, (latM 𝔞 : Submodule (𝓞 F) F).neg_mem a.2, rfl⟩⟩)
    ⟨fun a a' h => Subtype.ext (neg_injective (remb_inj (congrArg Subtype.val h))), fun μ => by
      obtain ⟨a, ha, h⟩ := (hDmem μ).1 μ.2
      exact ⟨⟨-a, (latM 𝔞 : Submodule (𝓞 F) F).neg_mem ha⟩, Subtype.ext (by simp [h])⟩⟩
  let eD : {ν : F // ν ∈ A} ≃ L := Equiv.ofBijective
    (fun ν => ⟨remb F ν.1, (hLmem _).2 ⟨ν.1, ν.2, rfl⟩⟩)
    ⟨fun ν ν' h => Subtype.ext (remb_inj (congrArg Subtype.val h)), fun μ => by
      obtain ⟨ν, hν, h⟩ := (hLmem μ).1 μ.2
      exact ⟨⟨ν, hν⟩, Subtype.ext h⟩⟩
  have hsL := summable_lat F 𝔞 σ hσ z hz b hb
  have hsumc : Summable (fun μ : Formalism.H.dual L => ∫ y in D, (∑' l : L, Ψ ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) := by
    simp only [hcoef]
    rw [← eM.summable_iff]
    exact hsL.congr fun a => (hFΨ a.1).symm
  have H4 := Formalism.H.lattice_fourier_series (RSp F) L (fun x => ∑' l : L, Ψ ((l : RSp F) + x))
    hGc hGper D hD hsumc 0
  simp only [hcoef, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    add_zero] at H4
  rw [← eM.hasSum_iff] at H4
  have hs0 : Summable (fun l : L => Ψ (l : RSp F)) := by simpa using hsumx 0
  have hsF : Summable (fun ν : {ν : F // ν ∈ A} => fTerm σ z b ν.1) := by
    rw [← eD.summable_iff] at hs0
    exact hs0.congr fun ν => hΨν ν.1
  have hR : ∑' l : L, Ψ (l : RSp F) = ∑' ν : {ν : F // ν ∈ A}, fTerm σ z b ν.1 := by
    rw [← eD.tsum_eq]
    exact tsum_congr fun ν => hΨν ν.1
  refine ⟨hsF, ?_⟩
  have hc0 : (ZLattice.covolume L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ZLattice.covolume_ne_zero L volume)
  have H5 := H4.mul_left (ZLattice.covolume L : ℂ)
  rw [hR] at H5
  rw [← hcov]
  refine H5.congr_fun fun a => ?_
  have key : ∀ a : {a : F // a ∈ latM 𝔞}, 𝓕 Ψ ((eM a : RSp F)) = ∏ τ : Emb F, phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ) :=
    fun a => hFΨ a.1
  simp only [Function.comp_apply, key]
  rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end GlobalTheory.HeckeTwoPoisson
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwo_poisson_summation_fractionalIdeal : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 → Summable (fun ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)} => GlobalTheory.HeckeTwo.fTerm σ z b ν.1) ∧ HasSum (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * ∑' ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)}, GlobalTheory.HeckeTwo.fTerm σ z b ν.1) := by
  atlas_forward_decl GlobalTheory.HeckeTwoPoisson.poisson
end
