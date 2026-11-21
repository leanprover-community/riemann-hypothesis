import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableRealWhittakerInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableUnipotentFourierIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveIntegralBoundOfParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStA
import BuildAid.ForwardExisting

section
noncomputable section

open MeasureTheory Set Filter

namespace GlobalTheory.CompanionTheory.TwoByTwoMajorant


def phi (σ w : ℝ) : ℝ := |w| ^ (1 - σ) / (1 + |w|) ^ 2

def aa (σ x : ℝ) : ℝ := |x| ^ (σ - 2) / (1 + |x|) ^ 2

def bb (p : ℝ) : ℝ := 1 / (1 + |p|) ^ 2

def G0 (σ x p y u : ℝ) : ℝ := aa σ x * bb p * phi σ (u - y * p / x)

theorem phi_nonneg (σ w : ℝ) : 0 ≤ phi σ w := by unfold phi; positivity
theorem aa_nonneg (σ x : ℝ) : 0 ≤ aa σ x := by unfold aa; positivity
theorem bb_nonneg (p : ℝ) : 0 ≤ bb p := by unfold bb; positivity
theorem majorant_integrand_nonneg (σ x p y u : ℝ) : 0 ≤ G0 σ x p y u :=
  mul_nonneg (mul_nonneg (aa_nonneg _ _) (bb_nonneg _)) (phi_nonneg _ _)

theorem core {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 4 ≤ N) {x p y u n : ℝ}
    (hx : x ≠ 0) (hyx : |y| ≤ |x|) (hxn : |x| ≤ n) (hpn : |p| ≤ n) :
    |x * u - p * y| ^ (-1 - σ) * (x ^ 2 + y ^ 2) ^ ((2 * σ - 1) / 2) /
      ((1 + n) ^ N * (1 + (x ^ 2 + y ^ 2) ^ ((1 : ℝ) / 2) / |x * u - p * y|) ^ N)
      ≤ 2 * G0 σ x p y u := by
  have hG := majorant_integrand_nonneg σ x p y u
  by_cases hD : x * u - p * y = 0
  · rw [hD, abs_zero, Real.zero_rpow (by linarith)]
    simpa using hG
  set w : ℝ := u - y * p / x with hw
  have hDw : x * u - p * y = x * w := by
    rw [hw]; field_simp
  have hw0 : w ≠ 0 := by
    intro h; apply hD; rw [hDw, h, mul_zero]
  set A : ℝ := |x| with hA
  set W : ℝ := |w| with hW
  have hA0 : 0 < A := abs_pos.2 hx
  have hW0 : 0 < W := abs_pos.2 hw0
  have hDabs : |x * u - p * y| = A * W := by rw [hDw, abs_mul]
  have hsq : x ^ 2 = A ^ 2 := (sq_abs x).symm
  have hysq : y ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) hyx 2
  set R : ℝ := x ^ 2 + y ^ 2 with hR
  have hRlo : A ^ 2 ≤ R := by rw [hR, hsq]; nlinarith [sq_nonneg y]
  have hRhi : R ≤ 2 * A ^ 2 := by rw [hR, hsq]; linarith
  have hA2 : 0 < A ^ 2 := by positivity
  have hR0 : 0 < R := lt_of_lt_of_le hA2 hRlo

  have t1 : R ^ ((2 * σ - 1) / 2) ≤ 2 * A ^ (2 * σ - 1) := by
    have hρ1 : 1 ≤ R / A ^ 2 := (one_le_div hA2).2 hRlo
    have hρ2 : R / A ^ 2 ≤ 2 := (div_le_iff₀ hA2).2 hRhi
    have hsplit : R = A ^ 2 * (R / A ^ 2) := by field_simp
    have hA2e : (A ^ 2) ^ ((2 * σ - 1) / 2) = A ^ (2 * σ - 1) := by
      rw [← Real.rpow_natCast A 2, ← Real.rpow_mul hA0.le]
      congr 1
      push_cast
      ring
    have hρe : (R / A ^ 2) ^ ((2 * σ - 1) / 2) ≤ 2 := by
      calc (R / A ^ 2) ^ ((2 * σ - 1) / 2) ≤ (R / A ^ 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hρ1 (by linarith)
        _ = R / A ^ 2 := Real.rpow_one _
        _ ≤ 2 := hρ2
    calc R ^ ((2 * σ - 1) / 2) = (A ^ 2 * (R / A ^ 2)) ^ ((2 * σ - 1) / 2) := by rw [← hsplit]
      _ = A ^ (2 * σ - 1) * (R / A ^ 2) ^ ((2 * σ - 1) / 2) := by
          rw [Real.mul_rpow hA2.le (by positivity), hA2e]
      _ ≤ A ^ (2 * σ - 1) * 2 := by
          exact mul_le_mul_of_nonneg_left hρe (by positivity)
      _ = 2 * A ^ (2 * σ - 1) := by ring

  have t2 : A ≤ R ^ ((1 : ℝ) / 2) := by
    have : (A ^ 2) ^ ((1 : ℝ) / 2) = A := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hA0.le]
    calc A = (A ^ 2) ^ ((1 : ℝ) / 2) := this.symm
      _ ≤ R ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow hA2.le hRlo (by norm_num)
  have hn0 : 0 ≤ n := le_trans hA0.le hxn

  have t3 : ((1 + W) / W) ^ 2 ≤ (1 + R ^ ((1 : ℝ) / 2) / (A * W)) ^ N := by
    have hb : (1 + W) / W ≤ 1 + R ^ ((1 : ℝ) / 2) / (A * W) := by
      have e1 : (1 + W) / W = 1 + A / (A * W) := by
        field_simp
        ring
      rw [e1]
      have : A / (A * W) ≤ R ^ ((1 : ℝ) / 2) / (A * W) :=
        div_le_div_of_nonneg_right t2 (by positivity)
      linarith
    have hb1 : 1 ≤ 1 + R ^ ((1 : ℝ) / 2) / (A * W) := by
      have : 0 ≤ R ^ ((1 : ℝ) / 2) / (A * W) := by positivity
      linarith
    calc ((1 + W) / W) ^ 2 ≤ (1 + R ^ ((1 : ℝ) / 2) / (A * W)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hb 2
      _ ≤ (1 + R ^ ((1 : ℝ) / 2) / (A * W)) ^ N :=
          pow_le_pow_right₀ hb1 (by omega)
  have t4 : (1 + A) ^ 2 * (1 + |p|) ^ 2 ≤ (1 + n) ^ N := by
    have e1 : (1 + A) ^ 2 ≤ (1 + n) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have e2 : (1 + |p|) ^ 2 ≤ (1 + n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc (1 + A) ^ 2 * (1 + |p|) ^ 2 ≤ (1 + n) ^ 2 * (1 + n) ^ 2 :=
          mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = (1 + n) ^ 4 := by ring
      _ ≤ (1 + n) ^ N := pow_le_pow_right₀ (by linarith) hN
  rw [hDabs]
  have hP : (A * W) ^ (-1 - σ) * R ^ ((2 * σ - 1) / 2)
      ≤ (A ^ (-1 - σ) * W ^ (-1 - σ)) * (2 * A ^ (2 * σ - 1)) := by
    rw [Real.mul_rpow hA0.le hW0.le]
    exact mul_le_mul_of_nonneg_left t1 (by positivity)
  have hQ : ((1 + A) ^ 2 * (1 + |p|) ^ 2) * ((1 + W) / W) ^ 2
      ≤ (1 + n) ^ N * (1 + R ^ ((1 : ℝ) / 2) / (A * W)) ^ N :=
    mul_le_mul t4 t3 (by positivity) (by positivity)
  refine (div_le_div₀ (by positivity) hP (by positivity) hQ).trans (le_of_eq ?_)
  have eA : A ^ (σ - 2) = A ^ (-1 - σ) * A ^ (2 * σ - 1) := by
    rw [← Real.rpow_add hA0]; congr 1; ring
  have eW : W ^ (1 - σ) = W ^ (-1 - σ) * W ^ 2 := by
    rw [← Real.rpow_natCast W 2, ← Real.rpow_add hW0]; congr 1; push_cast; ring
  unfold G0 aa bb phi
  rw [← hw, ← hA, ← hW, eA, eW]
  field_simp

def Gi (σ : ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  if |q.2.1| ≤ |q.1.1| then G0 σ q.1.1 q.1.2 q.2.1 q.2.2 else 0





def coord : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.finTwoArrow (α := Fin 2 → ℝ)).trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow)

theorem coord_mp : MeasurePreserving coord volume volume :=
  (volume_preserving_finTwoArrow (Fin 2 → ℝ)).trans
    ((volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ))

theorem coord_apply (h : Fin 2 → Fin 2 → ℝ) :
    coord h = ((h 0 0, h 0 1), (h 1 0, h 1 1)) := rfl


end GlobalTheory.CompanionTheory.TwoByTwoMajorant
end
end

section
section
open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.PowerKernel

noncomputable def dens (σ : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  |y|⁻¹ * (|y| ^ (σ - 1) / (1 + |y⁻¹| * 1) ^ N)

theorem measurable_dens (σ : ℝ) (N : ℕ) : Measurable (dens σ N) := by
  unfold dens
  have h1 : Measurable fun y : ℝ => |y| := by fun_prop
  have h2 : Measurable fun y : ℝ => |y| ^ (σ - 1) := h1.pow_const _
  have h3 : Measurable fun y : ℝ => (1 + |y⁻¹| * 1) ^ N := by fun_prop
  exact (h1.inv).mul (h2.div h3)

theorem dens_nonneg (σ : ℝ) (N : ℕ) (y : ℝ) : 0 ≤ dens σ N y := by
  unfold dens
  positivity

theorem dens_neg (σ : ℝ) (N : ℕ) (y : ℝ) : dens σ N (-y) = dens σ N y := by
  simp [dens, inv_neg, abs_neg]

theorem dens_le_small (σ : ℝ) {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (hy : 0 < y) :
    dens σ N y ≤ y ^ (σ - 1) := by
  have hyi : 0 < y⁻¹ := inv_pos.2 hy
  have hp : 0 < y ^ (σ - 1) := Real.rpow_pos_of_pos hy _
  have hb : y⁻¹ ≤ (1 + y⁻¹) ^ N := by
    calc y⁻¹ ≤ 1 + y⁻¹ := by linarith
      _ = (1 + y⁻¹) ^ 1 := (pow_one _).symm
      _ ≤ (1 + y⁻¹) ^ N := pow_le_pow_right₀ (by linarith) hN
  have hD : 0 < (1 + y⁻¹) ^ N := by positivity
  simp only [dens, abs_of_pos hy, abs_of_pos hyi, mul_one]
  rw [← mul_div_assoc, div_le_iff₀ hD, mul_comm]
  exact mul_le_mul_of_nonneg_left hb hp.le

theorem dens_le_large (σ : ℝ) (N : ℕ) {y : ℝ} (hy : 0 < y) :
    dens σ N y ≤ y ^ (σ - 2) := by
  have hyi : 0 < y⁻¹ := inv_pos.2 hy
  have hp : 0 < y ^ (σ - 1) := Real.rpow_pos_of_pos hy _
  have hb : 1 ≤ (1 + y⁻¹) ^ N := one_le_pow₀ (by linarith)
  have he : y ^ (σ - 2) = y⁻¹ * y ^ (σ - 1) := by
    rw [show σ - 2 = -1 + (σ - 1) by ring, Real.rpow_add hy, Real.rpow_neg_one]
  simp only [dens, abs_of_pos hy, abs_of_pos hyi, mul_one]
  rw [he]
  exact mul_le_mul_of_nonneg_left (div_le_self hp.le hb) hyi.le

theorem dens_integrableOn {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (dens σ N) (Ioi 0) := by
  have hA : IntegrableOn (dens σ N) (Ioc 0 1) := by
    have hi : IntegrableOn (fun y : ℝ => y ^ (σ - 1)) (Ioc 0 1) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := σ - 1) (by linarith)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    refine Integrable.mono' hi (measurable_dens σ N).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_of_nonneg (dens_nonneg σ N y)]
    exact dens_le_small σ hN hy.1
  have hB : IntegrableOn (dens σ N) (Ioi 1) := by
    have hi : IntegrableOn (fun y : ℝ => y ^ (σ - 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine Integrable.mono' hi (measurable_dens σ N).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_of_nonneg (dens_nonneg σ N y)]
    exact dens_le_large σ N (lt_trans zero_lt_one hy)
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  exact hA.union hB

theorem dens_integrable {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (dens σ N) := by
  have hI : Integrable ((Ioi (0 : ℝ)).indicator (dens σ N)) :=
    (dens_integrableOn h0 h1 hN).integrable_indicator measurableSet_Ioi
  have hJ : Integrable fun x : ℝ => (Ioi (0 : ℝ)).indicator (dens σ N) (-x) := hI.comp_neg
  refine (hI.add hJ).congr (Filter.Eventually.of_forall fun x => ?_)
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h2 : x ∉ Ioi (0 : ℝ) := by simp [hx.le]
    have h3 : -x ∈ Ioi (0 : ℝ) := by simpa using hx
    simp [Set.indicator_of_notMem h2, Set.indicator_of_mem h3, dens_neg]
  · subst hx
    simp [dens]
  · have h2 : x ∈ Ioi (0 : ℝ) := hx
    have h3 : -x ∉ Ioi (0 : ℝ) := by simp [hx.le]
    simp [Set.indicator_of_mem h2, Set.indicator_of_notMem h3]

theorem kernel_one_integrable {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun t : ℝˣ => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N) Ad3.mulR := by
  have key : Integrable (fun x : ℝ => |x|⁻¹ •
      (((|x| ^ (σ - 1) / (1 + |x⁻¹| * 1) ^ N : ℝ)) : ℂ)) volume := by
    refine ((dens_integrable h0 h1 hN).ofReal (𝕜 := ℂ)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp [dens, Complex.real_smul]
  exact ((GlobalTheory.CompanionTheory.RealTateConv.integrable_mulR_iff
    (fun x : ℝ => (((|x| ^ (σ - 1) / (1 + |x⁻¹| * 1) ^ N : ℝ)) : ℂ))).2 key).re

theorem kernel_scale (σ : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q) (t : ℝˣ) :
    |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)| ^ (σ - 1) /
        (1 + |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)⁻¹| * q) ^ N =
      q ^ (σ - 1) * (|(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N) := by
  have h1 : |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)| = |(t : ℝ)| * q := by
    simp [abs_mul, abs_of_pos hq]
  have h2 : |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)⁻¹| * q = |(t : ℝ)⁻¹| * 1 := by
    simp only [Units.val_mul, Units.val_mk0, mul_inv, abs_mul, abs_inv, abs_of_pos hq]
    field_simp
  rw [h1, h2, Real.mul_rpow (abs_nonneg _) hq.le]
  ring

theorem kernel_integral_le :
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 1 ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℝˣ => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N) Ad3.mulR ∧
    ∫ t : ℝˣ, |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N ∂Ad3.mulR ≤ K * q ^ (σ - 1) := by
  intro σ h0 h1 N hN
  refine ⟨∫ t : ℝˣ, |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N ∂Ad3.mulR, fun q hq => ?_⟩
  set u : ℝˣ := Units.mk0 q hq.ne' with hu
  set f : ℝˣ → ℝ := fun t => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N with hf
  have hcomp : (fun t : ℝˣ => f (t * u)) = fun t : ℝˣ =>
      q ^ (σ - 1) * (|(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N) := by
    funext t
    exact kernel_scale σ N hq t
  have hint : Integrable (fun t : ℝˣ => f (t * u)) Ad3.mulR := by
    rw [hcomp]
    exact (kernel_one_integrable h0 h1 hN).const_mul _
  have hfi : Integrable f Ad3.mulR := by
    have := hint.comp_mul_right u⁻¹
    simpa using this
  refine ⟨hfi, le_of_eq ?_⟩
  rw [← integral_mul_right_eq_self f u, hcomp, integral_const_mul, mul_comm]

end GlobalTheory.CompanionTheory.PowerKernel
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mult_integral_power_bound : ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 1 ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℝˣ => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N) Ad3.mulR ∧
    ∫ t : ℝˣ, |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N ∂Ad3.mulR ≤ K * q ^ (σ - 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PowerKernel.kernel_integral_le
end

section
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Shear

theorem slice_integrable (g : ℝ → ℝ) (hgi : Integrable g) {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    Integrable (fun y : ℝ => g (α * y - c)) := by
  have h1 : Integrable (fun t : ℝ => g (t - c)) := hgi.comp_sub_right c
  exact h1.comp_mul_left' hα

theorem slice_integral (g : ℝ → ℝ) {α : ℝ} (c : ℝ) :
    ∫ y : ℝ, g (α * y - c) = |α⁻¹| * ∫ x, g x := by
  have h1 := Measure.integral_comp_mul_left (fun t : ℝ => g (t - c)) α
  have h2 : ∫ t : ℝ, g (t - c) = ∫ x, g x := integral_sub_right_eq_self g c
  rw [h1, h2, smul_eq_mul]

theorem one_sided (g φ : ℝ → ℝ) (hg : Measurable g) (hφ : Measurable φ)
    (hgi : Integrable g) (hφi : Integrable φ)
    (hg0 : ∀ x, 0 ≤ g x) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (α β : ℝ) (hα : α ≠ 0) :
    Integrable (fun p : ℝ × ℝ => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)) ∧
    ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)
      ≤ (∫ x, g x) * (∫ x, φ x) / |α| := by
  set F : ℝ × ℝ → ℝ := fun p => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2) with hF
  have hFm : Measurable F := by
    apply Measurable.mul
    · exact hg.comp (by fun_prop)
    · exact (hφ.comp measurable_fst).mul (hφ.comp measurable_snd)
  have hF0 : ∀ p, 0 ≤ F p := fun p =>
    mul_nonneg (hg0 _) (mul_nonneg (hφ0 _) (hφ0 _))
  set C : ℝ := |α⁻¹| * ∫ x, g x with hC

  have hdom : ∀ x y, F (x, y) ≤ φ x * g (α * y - β * x) := by
    intro x y
    have h1 : φ x * φ y ≤ φ x := by
      have := mul_le_mul_of_nonneg_left (hφ1 y) (hφ0 x)
      simpa using this
    have := mul_le_mul_of_nonneg_left h1 (hg0 (α * y - β * x))
    simpa [hF, mul_comm] using this
  have hslice : ∀ x, Integrable (fun y => F (x, y)) := by
    intro x
    refine Integrable.mono' ((slice_integrable g hgi hα (β * x)).const_mul (φ x))
      (hFm.comp measurable_prodMk_left).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
    exact hdom x y
  have hbound : ∀ x, ∫ y, F (x, y) ≤ φ x * C := by
    intro x
    have h1 : ∫ y, F (x, y) ≤ ∫ y, φ x * g (α * y - β * x) :=
      integral_mono (hslice x) ((slice_integrable g hgi hα (β * x)).const_mul (φ x))
        (fun y => hdom x y)
    rw [integral_const_mul, slice_integral] at h1
    exact h1
  have hnn : ∀ x, 0 ≤ ∫ y, F (x, y) := fun x => integral_nonneg (fun y => hF0 _)
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, F (x, y)) volume :=
    (hFm.stronglyMeasurable.integral_prod_right (ν := volume)).aestronglyMeasurable
  have hint : Integrable (fun x => ∫ y, F (x, y)) := by
    refine Integrable.mono' (hφi.mul_const C) hmeas ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
    exact hbound x
  have hFi : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hslice, ?_⟩
    have : (fun x => ∫ y, ‖F (x, y)‖) = fun x => ∫ y, F (x, y) := by
      funext x
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      simp only [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
    rw [this]
    exact hint
  refine ⟨hFi, ?_⟩
  have hval : ∫ p : ℝ × ℝ, F p = ∫ x, ∫ y, F (x, y) := integral_prod F hFi
  have hle : ∫ x, ∫ y, F (x, y) ≤ ∫ x, φ x * C :=
    integral_mono hint (hφi.mul_const C) hbound
  rw [integral_mul_const] at hle
  have hCe : (∫ x, φ x) * C = (∫ x, g x) * (∫ x, φ x) / |α| := by
    rw [hC, abs_inv]
    field_simp
  rw [hval]
  linarith

theorem integral_shear_le (g φ : ℝ → ℝ) (hg : Measurable g) (hφ : Measurable φ)
    (hgi : Integrable g) (hφi : Integrable φ)
    (hg0 : ∀ x, 0 ≤ g x) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    Integrable (fun p : ℝ × ℝ => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)) ∧
    ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)
      ≤ (∫ x, g x) * (∫ x, φ x) / max |α| |β| := by
  obtain ⟨hI, hA⟩ := one_sided g φ hg hφ hgi hφi hg0 hφ0 hφ1 α β hα
  obtain ⟨hI', hB'⟩ := one_sided g φ hg hφ hgi hφi hg0 hφ0 hφ1 (-β) (-α) (neg_ne_zero.mpr hβ)
  refine ⟨hI, ?_⟩
  have hsw : ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)
      = ∫ p : ℝ × ℝ, g (-β * p.2 - -α * p.1) * (φ p.1 * φ p.2) := by
    have h := integral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun p : ℝ × ℝ => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2))
    rw [Measure.volume_eq_prod, ← h]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Prod.fst_swap, Prod.snd_swap]
    have : α * p.1 - β * p.2 = -β * p.2 - -α * p.1 := by ring
    rw [this, mul_comm (φ p.2)]
  have hB : ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)
      ≤ (∫ x, g x) * (∫ x, φ x) / |β| := by
    rw [hsw]
    simpa [abs_neg] using hB'
  rcases max_cases |α| |β| with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact hA
  · rw [h]; exact hB

end GlobalTheory.CompanionTheory.Shear
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_double_integral_bound : ∀ (g φ : ℝ → ℝ), Measurable g → Measurable φ → Integrable g → Integrable φ →
    (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ φ x) → (∀ x, φ x ≤ 1) → ∀ α β : ℝ, α ≠ 0 → β ≠ 0 →
    Integrable (fun p : ℝ × ℝ => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)) ∧
    ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2) ≤ (∫ x, g x) * (∫ x, φ x) / max |α| |β| := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Shear.integral_shear_le
end

section
section
noncomputable section

open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.PerUInt.Outer

theorem integrable_rpow_abs_mul_phi (τ : ℝ) (hτ : 0 ≤ τ) (h1 : τ < 1) :
    Integrable (fun x : ℝ => |x| ^ (-τ) * phi x) := by
  have hI : IntegrableOn (fun x : ℝ => x ^ (-τ)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = indicator (Ioc 0 1) (fun x : ℝ => x ^ (-τ)) := ⟨_, rfl⟩
  have hG : Integrable G := hGdef ▸ hI.integrable_indicator measurableSet_Ioc
  have hG' : Integrable (fun x => G (-x)) := hG.comp_neg
  have hGn : ∀ y, 0 ≤ G y := by
    intro y
    rw [hGdef]
    refine indicator_nonneg (fun x hx => Real.rpow_nonneg hx.1.le _) y
  have hD : Integrable (fun x => G x + G (-x) + phi x) := (hG.add hG').add integrable_phi
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by
    simpa [ae_iff] using (measure_singleton (0 : ℝ) : volume {(0 : ℝ)} = 0)
  refine hD.mono' ((continuous_abs.measurable.pow_const (-τ)).mul measurable_phi).aestronglyMeasurable ?_
  filter_upwards [h0] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg x) _) (phi_nonneg x))]
  have hp0 := phi_nonneg x
  have hp1 := phi_le_one x
  have hr0 : 0 ≤ |x| ^ (-τ) := Real.rpow_nonneg (abs_nonneg x) _
  have hGx := hGn x
  have hGnx := hGn (-x)
  by_cases hx1 : |x| ≤ 1
  · have hle : |x| ^ (-τ) * phi x ≤ |x| ^ (-τ) := mul_le_of_le_one_right hr0 hp1
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have hm : -x ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, by rwa [abs_of_neg hneg] at hx1⟩
      have : G (-x) = |x| ^ (-τ) := by
        rw [hGdef, indicator_of_mem hm, abs_of_neg hneg]
      linarith
    · have hm : x ∈ Ioc (0 : ℝ) 1 := ⟨hpos, by rwa [abs_of_pos hpos] at hx1⟩
      have : G x = |x| ^ (-τ) := by
        rw [hGdef, indicator_of_mem hm, abs_of_pos hpos]
      linarith
  · have hge : 1 ≤ |x| := (not_le.1 hx1).le
    have h2 : |x| ^ (-τ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hge (by linarith)
    have h3 : |x| ^ (-τ) * phi x ≤ phi x := mul_le_of_le_one_left hp0 h2
    linarith

theorem rpow_anti {x y r : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hr : r ≤ 0) : y ^ r ≤ x ^ r :=
  Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hr (mem_Ioi.2 hx) (mem_Ioi.2 (hx.trans_le hxy)) hxy

theorem rpow_bound (σ a b : ℝ) (hσ : 0 < σ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a ^ 2 + b ^ 2) ^ (-1 - σ / 2) * ((a ^ 2 + b ^ 2) / max |a| |b|) ≤
      |a| ^ (-((1 + σ) / 2)) * |b| ^ (-((1 + σ) / 2)) := by
  have hA : 0 < |a| := abs_pos.2 ha
  have hB : 0 < |b| := abs_pos.2 hb
  have hma : |a| ≤ max |a| |b| := le_max_left _ _
  have hmb : |b| ≤ max |a| |b| := le_max_right _ _
  have hc : (max |a| |b|) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases max_choice |a| |b| with h | h
    · rw [h, sq_abs]; nlinarith [sq_nonneg b]
    · rw [h, sq_abs]; nlinarith [sq_nonneg a]
  generalize max |a| |b| = m at hma hmb hc ⊢
  generalize a ^ 2 + b ^ 2 = c at hc ⊢
  have hm : 0 < m := lt_of_lt_of_le hA hma
  have hm2 : 0 < m ^ 2 := pow_pos hm 2
  have hc0 : 0 < c := lt_of_lt_of_le hm2 hc
  have e1 : c ^ (-1 - σ / 2) * (c / m) = c ^ (-(σ / 2)) / m := by
    have h : c ^ (-(σ / 2)) = c ^ (-1 - σ / 2) * c := by
      rw [show -(σ / 2) = (-1 - σ / 2) + 1 by ring, Real.rpow_add hc0, Real.rpow_one]
    rw [h]
    ring
  have e2 : c ^ (-(σ / 2)) ≤ (m ^ 2) ^ (-(σ / 2)) :=
    rpow_anti hm2 hc (by linarith)
  have e3 : (m ^ 2) ^ (-(σ / 2)) / m = m ^ (-((1 + σ) / 2)) * m ^ (-((1 + σ) / 2)) := by
    rw [← Real.rpow_natCast m 2, ← Real.rpow_mul hm.le, ← Real.rpow_add hm,
      ← Real.rpow_sub_one hm.ne']
    congr 1
    push_cast
    ring
  have e4 : m ^ (-((1 + σ) / 2)) ≤ |a| ^ (-((1 + σ) / 2)) :=
    rpow_anti hA hma (by linarith)
  have e5 : m ^ (-((1 + σ) / 2)) ≤ |b| ^ (-((1 + σ) / 2)) :=
    rpow_anti hB hmb (by linarith)
  have hmr : 0 ≤ m ^ (-((1 + σ) / 2)) := Real.rpow_nonneg hm.le _
  calc c ^ (-1 - σ / 2) * (c / m) = c ^ (-(σ / 2)) / m := e1
    _ ≤ (m ^ 2) ^ (-(σ / 2)) / m := div_le_div_of_nonneg_right e2 hm.le
    _ = m ^ (-((1 + σ) / 2)) * m ^ (-((1 + σ) / 2)) := e3
    _ ≤ |a| ^ (-((1 + σ) / 2)) * |b| ^ (-((1 + σ) / 2)) :=
      mul_le_mul e4 e5 hmr (Real.rpow_nonneg hA.le _)

theorem integrable_firstColumn : ∀ σ : ℝ, 0 < σ → σ < 1 → Integrable (fun p : ℝ × ℝ =>
    (p.1 ^ 2 + p.2 ^ 2) ^ (-1 - σ / 2) * ((p.1 ^ 2 + p.2 ^ 2) / max |p.1| |p.2|) *
      (phi p.1 * phi p.2)) := by
  intro σ h0 h1
  have hg := integrable_rpow_abs_mul_phi ((1 + σ) / 2) (by linarith) (by linarith)
  have hP : Integrable (fun p : ℝ × ℝ =>
      (|p.1| ^ (-((1 + σ) / 2)) * phi p.1) * (|p.2| ^ (-((1 + σ) / 2)) * phi p.2)) := by
    rw [Measure.volume_eq_prod]
    exact hg.mul_prod hg
  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
    simpa [ae_iff] using (measure_singleton (0 : ℝ) : volume {(0 : ℝ)} = 0)
  have hne1 : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hne
  have hne2 : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae hne
  have hc : Measurable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) :=
    (measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)
  have hmx : Measurable (fun p : ℝ × ℝ => max |p.1| |p.2|) :=
    (continuous_abs.measurable.comp measurable_fst).max
      (continuous_abs.measurable.comp measurable_snd)
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      (p.1 ^ 2 + p.2 ^ 2) ^ (-1 - σ / 2) * ((p.1 ^ 2 + p.2 ^ 2) / max |p.1| |p.2|) *
        (phi p.1 * phi p.2)) :=
    ((hc.pow_const _).mul (hc.div hmx)).mul
      ((measurable_phi.comp measurable_fst).mul (measurable_phi.comp measurable_snd))
  refine hP.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [hne1, hne2] with p hp1 hp2
  have hc0 : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
  have hm0 : 0 ≤ max |p.1| |p.2| := le_max_of_le_left (abs_nonneg _)
  have hph : 0 ≤ phi p.1 * phi p.2 := mul_nonneg (phi_nonneg _) (phi_nonneg _)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hc0 _) (div_nonneg hc0 hm0)) hph)]
  calc _ ≤ (|p.1| ^ (-((1 + σ) / 2)) * |p.2| ^ (-((1 + σ) / 2))) * (phi p.1 * phi p.2) :=
        mul_le_mul_of_nonneg_right (rpow_bound σ p.1 p.2 h0 hp1 hp2) hph
    _ = _ := by ring

end GlobalTheory.CompanionTheory.PerUInt.Outer
end
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_radial_cutoff_weight : ∀ σ : ℝ, 0 < σ → σ < 1 → Integrable (fun p : ℝ × ℝ =>
    (p.1 ^ 2 + p.2 ^ 2) ^ (-1 - σ / 2) * ((p.1 ^ 2 + p.2 ^ 2) / max |p.1| |p.2|) *
      (GlobalTheory.CompanionTheory.PerUInt.phi p.1 * GlobalTheory.CompanionTheory.PerUInt.phi p.2)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerUInt.Outer.integrable_firstColumn
end

section
section
noncomputable section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.PerUInt

theorem inv_pow_le_phi_prod (h : Ad3.LR.M22) (N : ℕ) (hN : 8 ≤ N) :
    1 / (1 + ‖h‖) ^ N ≤ phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)) := by
  have entry : ∀ i j, 1 + |h i j| ≤ 1 + ‖h‖ := by
    intro i j
    have h1 : ‖h i j‖ ≤ ‖h i‖ := norm_le_pi_norm (h i) j
    have h2 : ‖h i‖ ≤ ‖h‖ := norm_le_pi_norm h i
    have h3 : |h i j| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using h1.trans h2
    linarith
  have ht : 1 ≤ 1 + ‖h‖ := by linarith [norm_nonneg h]
  have sq : ∀ i j, (1 + |h i j|) ^ 2 ≤ (1 + ‖h‖) ^ 2 := fun i j =>
    pow_le_pow_left₀ (by positivity) (entry i j) 2
  have hP : (1 + |h 0 0|) ^ 2 * (1 + |h 1 0|) ^ 2 * ((1 + |h 0 1|) ^ 2 * (1 + |h 1 1|) ^ 2) ≤
      (1 + ‖h‖) ^ N := by
    calc (1 + |h 0 0|) ^ 2 * (1 + |h 1 0|) ^ 2 * ((1 + |h 0 1|) ^ 2 * (1 + |h 1 1|) ^ 2)
        ≤ (1 + ‖h‖) ^ 2 * (1 + ‖h‖) ^ 2 * ((1 + ‖h‖) ^ 2 * (1 + ‖h‖) ^ 2) := by
          have a := sq 0 0
          have b := sq 1 0
          have c := sq 0 1
          have d := sq 1 1
          gcongr
      _ = (1 + ‖h‖) ^ 8 := by ring
      _ ≤ (1 + ‖h‖) ^ N := pow_le_pow_right₀ ht hN
  have hphi : phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)) =
      ((1 + |h 0 0|) ^ 2 * (1 + |h 1 0|) ^ 2 * ((1 + |h 0 1|) ^ 2 * (1 + |h 1 1|) ^ 2))⁻¹ := by
    simp only [phi, mul_inv]
  rw [hphi, one_div]
  exact inv_anti₀ (by positivity) hP

theorem kernel_exponents (k : ℕ) (σ Y c E : ℝ) (hY : 0 < Y) (hc : 0 < c) :
    (Y ^ ((2 * (k : ℝ) - 1) / 2) * E) * (Y * c) ^ (-(3 : ℝ) / 2) *
        ((c / 2) ^ ((1 : ℝ) / 2) / (Y * c)) ^ (σ - 1) =
      2 ^ ((1 - σ) / 2) * (Y ^ ((k : ℝ) - 1 - σ) * E * c ^ (-1 - σ / 2)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hw : 0 < (c / 2) ^ ((1 : ℝ) / 2) / (Y * c) := by positivity
  have hlog : Real.log ((c / 2) ^ ((1 : ℝ) / 2) / (Y * c)) =
      (Real.log c - Real.log 2) / 2 - (Real.log Y + Real.log c) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_div hc.ne' h2.ne', Real.log_mul hY.ne' hc.ne']
    ring
  rw [Real.rpow_def_of_pos hY, Real.rpow_def_of_pos (mul_pos hY hc), Real.rpow_def_of_pos hw,
    Real.rpow_def_of_pos h2, Real.rpow_def_of_pos hY, Real.rpow_def_of_pos hc, hlog,
    Real.log_mul hY.ne' hc.ne']
  have e : ∀ a b c' : ℝ, Real.exp a * E * Real.exp b * Real.exp c' =
      Real.exp (a + b + c') * E := by
    intro a b c'
    rw [Real.exp_add, Real.exp_add]
    ring
  have e' : ∀ a b c' : ℝ, Real.exp a * (Real.exp b * E * Real.exp c') =
      Real.exp (a + b + c') * E := by
    intro a b c'
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [e, e']
  congr 2
  ring

theorem norm_Wm_inv (k : ℕ) (h : Ad3.LR.M22) (hD : 0 < (Matrix.of h).det)
    (hc : 0 < h 0 0 ^ 2 + h 1 0 ^ 2) :
    ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ =
      ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) ^ ((2 * (k : ℝ) - 1) / 2) *
        Real.exp (-(2 * Real.pi * ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)))) := by
  obtain ⟨e0, e1⟩ := GlobalTheory.CompanionTheory.PrimalInt.inv_row h hD.ne'
  have hdet : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hone : Ad3.LR.C.d2 1 = 1 := by
    simp [Ad3.LR.C.d2, Matrix.one_fin_two]
  have hW := GlobalTheory.CompanionTheory.AbsWm.norm_Wm k (Matrix.of h)⁻¹ 1 (by
    rw [one_mul, hdet]
    exact inv_pos.2 hD)
  rw [hone, one_mul, one_mul] at hW
  have hNR : Complex.normSq (GlobalTheory.CompanionTheory.WmFE.jj (Matrix.of h)⁻¹) =
      (h 0 0 ^ 2 + h 1 0 ^ 2) / (Matrix.of h).det ^ 2 := by
    have : Complex.normSq (GlobalTheory.CompanionTheory.WmFE.jj (Matrix.of h)⁻¹) =
        ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 +
          ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 := by
      simp [GlobalTheory.CompanionTheory.WmFE.jj, Complex.normSq_apply]
      ring
    rw [this, e0, e1]
    field_simp
    ring
  rw [hW, hNR, hdet]
  generalize (Matrix.of h).det = D at hD
  generalize h 0 0 ^ 2 + h 1 0 ^ 2 = c at hc
  have hY : D⁻¹ = D / c * (c / D ^ 2) := by
    field_simp
  have hE : 2 * Real.pi * D⁻¹ / (c / D ^ 2) = 2 * Real.pi * (D / c) := by
    field_simp
  have hYp : 0 < D / c := by positivity
  have hNp : 0 < c / D ^ 2 := by positivity
  rw [hE]
  congr 1
  rw [hY, Real.mul_rpow hYp.le hNp.le, mul_assoc, ← Real.rpow_add hNp]
  simp

theorem pointwise_gamma_bound : ∀ (k : ℕ), 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 8 ≤ N →
    ∃ C : ℝ, ∀ h : Ad3.LR.M22, (Matrix.of h).det ≠ 0 →
    ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) * ‖Ad3.LR.B.eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N ≤
      C * (GlobalTheory.CompanionTheory.PerUInt.gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) *
        (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 0) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 0) * (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 1) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 1)))) := by
  intro k _ σ _ h1 N hN
  refine ⟨2 ^ ((1 - σ) / 2), fun h hd => ?_⟩
  have hC : (0 : ℝ) ≤ 2 ^ ((1 - σ) / 2) := by positivity
  have hΦ : 0 ≤ phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)) :=
    mul_nonneg (mul_nonneg (phi_nonneg _) (phi_nonneg _)) (mul_nonneg (phi_nonneg _) (phi_nonneg _))
  have hc0 : 0 ≤ h 0 0 ^ 2 + h 1 0 ^ 2 := by positivity
  rcases lt_or_gt_of_ne hd with hneg | hD
  · have hdet : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    have hW : Ad3.LR.Wm k (Matrix.of h)⁻¹ = 0 := by
      have : ¬ 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det := by
        rw [hdet]
        exact not_lt.2 (inv_lt_zero.2 hneg).le
      unfold Ad3.LR.Wm
      exact if_neg this
    rw [hW]
    simp only [norm_zero, zero_mul, zero_div]
    exact mul_nonneg hC (mul_nonneg (mul_nonneg (gk_nonneg _ _ _) (Real.rpow_nonneg hc0 _)) hΦ)
  · have hc : 0 < h 0 0 ^ 2 + h 1 0 ^ 2 := by
      rcases hc0.lt_or_eq with hp | hz
      · exact hp
      · exfalso
        have ha : h 0 0 = 0 := by nlinarith [sq_nonneg (h 0 0), sq_nonneg (h 1 0)]
        have hb : h 1 0 = 0 := by nlinarith [sq_nonneg (h 0 0), sq_nonneg (h 1 0)]
        apply hd
        simp [Matrix.det_fin_two, ha, hb]
    obtain ⟨e0, e1⟩ := GlobalTheory.CompanionTheory.PrimalInt.inv_row h hd
    have b0 : |((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0| ≤ ‖Ad3.LR.B.eta h‖ := by
      simpa [Ad3.LR.B.eta] using norm_le_pi_norm (Ad3.LR.B.eta h) 0
    have b1 : |((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1| ≤ ‖Ad3.LR.B.eta h‖ := by
      simpa [Ad3.LR.B.eta] using norm_le_pi_norm (Ad3.LR.B.eta h) 1
    rw [e0, abs_div, abs_neg, abs_of_pos hD, div_le_iff₀ hD] at b0
    rw [e1, abs_div, abs_of_pos hD, div_le_iff₀ hD] at b1
    have hw : ((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det ≤
        ‖Ad3.LR.B.eta h‖ := by
      rw [div_le_iff₀ hD, ← Real.sqrt_eq_rpow]
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      have s0 : h 1 0 ^ 2 ≤ (‖Ad3.LR.B.eta h‖ * (Matrix.of h).det) ^ 2 := by
        rw [← sq_abs (h 1 0)]
        exact pow_le_pow_left₀ (abs_nonneg _) b0 2
      have s1 : h 0 0 ^ 2 ≤ (‖Ad3.LR.B.eta h‖ * (Matrix.of h).det) ^ 2 := by
        rw [← sq_abs (h 0 0)]
        exact pow_le_pow_left₀ (abs_nonneg _) b1 2
      linarith
    have hwpos : 0 < ((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det := by
      positivity
    have hE : ‖Ad3.LR.B.eta h‖ ^ (σ - 1) ≤
        (((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det) ^ (σ - 1) :=
      Real.rpow_le_rpow_of_nonpos hwpos hw (by linarith)
    have hdec := inv_pow_le_phi_prod h N hN
    have hYp : 0 < (Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2) := div_pos hD hc
    have hDY : (Matrix.of h).det =
        (Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2) * (h 0 0 ^ 2 + h 1 0 ^ 2) := by
      field_simp
    have hker := kernel_exponents k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2))
      (h 0 0 ^ 2 + h 1 0 ^ 2)
      (Real.exp (-(2 * Real.pi * ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2))))) hYp hc
    rw [← hDY] at hker
    have hgk : gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) =
        ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) ^ ((k : ℝ) - 1 - σ) *
          Real.exp (-(2 * Real.pi * ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)))) := by
      simp [gk, hYp]
    rw [abs_of_pos hD]
    calc ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * (Matrix.of h).det ^ (-(3 : ℝ) / 2) *
          ‖Ad3.LR.B.eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N
        = (‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * (Matrix.of h).det ^ (-(3 : ℝ) / 2) *
            ‖Ad3.LR.B.eta h‖ ^ (σ - 1)) * (1 / (1 + ‖h‖) ^ N) := by ring
      _ ≤ (‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * (Matrix.of h).det ^ (-(3 : ℝ) / 2) *
            (((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det) ^ (σ - 1)) *
            (phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hE (by positivity)) hdec (by positivity)
            (by positivity)
      _ = _ := by
          rw [norm_Wm_inv k h hD hc, hker, hgk]
          ring

end GlobalTheory.CompanionTheory.PerUInt
end
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_integrand_majorant : ∀ (k : ℕ), 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 8 ≤ N → ∃ C : ℝ, ∀ h : Ad3.LR.M22, (Matrix.of h).det ≠ 0 →
    ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) * ‖Ad3.LR.B.eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N ≤
      C * (GlobalTheory.CompanionTheory.PerUInt.gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) *
        (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 0) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 0) * (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 1) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 1)))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerUInt.pointwise_gamma_bound
end

section
noncomputable section

open MeasureTheory
open Ad3 Ad3.LR Ad3.LR.C Ad3.LR.B

namespace GlobalTheory.CompanionTheory.PerUInt

def rtEquiv (g : GL (Fin 3) ℝ) : M23 ≃L[ℝ] M23 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X => Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ))
      invFun := fun X => Matrix.of.symm (Matrix.of X * ((g⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ))
      map_add' := fun X Y => by
        show Matrix.of.symm ((Matrix.of X + Matrix.of Y) * (g : Matrix (Fin 3) (Fin 3) ℝ)) = _
        rw [Matrix.add_mul]
        rfl
      map_smul' := fun c X => by
        show Matrix.of.symm ((c • Matrix.of X) * (g : Matrix (Fin 3) (Fin 3) ℝ)) = _
        rw [Matrix.smul_mul]
        rfl
      left_inv := fun X => by
        simp [Matrix.mul_assoc]
      right_inv := fun X => by
        simp [Matrix.mul_assoc] }

def rtS (g : GL (Fin 3) ℝ) (Φ : Sw) : Sw :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rtEquiv g) Φ

theorem rtS_apply (g : GL (Fin 3) ℝ) (Φ : Sw) : ⇑(rtS g Φ) = B.rt g ⇑Φ := by
  funext X
  simp [rtS, B.rt, rtEquiv]

theorem measurable_innB (Ψ : M23 → ℂ) (hΨ : Continuous Ψ) :
    Measurable (fun p : ℝˣ × M22 => innB Ψ p.2 (p.1 : ℝ)⁻¹) := by
  have hv : Continuous (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => psiR (-(((p.1.1 : ℝ))⁻¹ * p.2 1))) := by
    unfold psiR
    have : Continuous (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => ((p.1.1⁻¹ : ℝˣ) : ℝ)) :=
      Units.continuous_val.comp (continuous_inv.comp (continuous_fst.comp continuous_fst))
    have h2 : (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => ((p.1.1 : ℝ))⁻¹) = fun p => ((p.1.1⁻¹ : ℝˣ) : ℝ) := by
      funext p; simp
    rw [show (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => Complex.exp (-2 * Real.pi * Complex.I * ((-(((p.1.1 : ℝ))⁻¹ * p.2 1) : ℝ) : ℂ)))
      = fun p => Complex.exp (-2 * Real.pi * Complex.I * ((-(((p.1.1⁻¹ : ℝˣ) : ℝ) * p.2 1) : ℝ) : ℂ)) by funext p; simp]
    fun_prop
  have hm : Continuous (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) =>
      Ψ (Matrix.of.symm (Matrix.of p.1.2 * blk p.2))) :=
    hΨ.comp (GlobalTheory.CompanionTheory.GodementInt.continuous_mul_blk.comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  exact ((hm.mul hv).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

def domF (σ : ℝ) (g : ℝ → ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  g ((z.1.1 * z.2.2 - z.2.1 * z.1.2) / (z.1.1 ^ 2 + z.1.2 ^ 2)) * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ (-1 - σ / 2) *
    (phi z.1.1 * phi z.1.2 * (phi z.2.1 * phi z.2.2))

theorem measurable_domF (σ : ℝ) (g : ℝ → ℝ) (hgm : Measurable g) : Measurable (domF σ g) := by
  unfold domF
  refine ((hgm.comp ?_).mul ?_).mul ?_
  · fun_prop
  · fun_prop
  · have := measurable_phi
    fun_prop

theorem domF_nonneg (σ : ℝ) (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (z) : 0 ≤ domF σ g z :=
  mul_nonneg (mul_nonneg (hg0 _) (Real.rpow_nonneg (by positivity) _))
    (mul_nonneg (mul_nonneg (phi_nonneg _) (phi_nonneg _)) (mul_nonneg (phi_nonneg _) (phi_nonneg _)))

theorem ae_ne_zero : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have h1 : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 := Measure.quasiMeasurePreserving_fst.ae h0
  have h2 : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := Measure.quasiMeasurePreserving_snd.ae h0
  filter_upwards [h1, h2] with p a b using ⟨a, b⟩

theorem domF_slice (σ : ℝ) (g : ℝ → ℝ) (w : ℝ × ℝ) (hw : w.1 ^ 2 + w.2 ^ 2 ≠ 0) (v : ℝ × ℝ) :
    domF σ g (w, v) = ((w.1 ^ 2 + w.2 ^ 2) ^ (-1 - σ / 2) * (phi w.1 * phi w.2)) *
      (g ((w.1 / (w.1 ^ 2 + w.2 ^ 2)) * v.2 - (w.2 / (w.1 ^ 2 + w.2 ^ 2)) * v.1) * (phi v.1 * phi v.2)) := by
  have e : (w.1 * v.2 - v.1 * w.2) / (w.1 ^ 2 + w.2 ^ 2) =
      (w.1 / (w.1 ^ 2 + w.2 ^ 2)) * v.2 - (w.2 / (w.1 ^ 2 + w.2 ^ 2)) * v.1 := by
    field_simp
  simp only [domF, e]
  ring

theorem integrable_domF (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g)
    (hg0 : ∀ x, 0 ≤ g x) : Integrable (domF σ g) := by
  have hsh := GlobalTheory.T.weighted_double_integral_bound g phi hgm measurable_phi hg integrable_phi hg0 phi_nonneg phi_le_one
  have hout := GlobalTheory.T.integrable_radial_cutoff_weight σ h0 h1
  have hm := measurable_domF σ g hgm
  have hc2 : ∀ w : ℝ × ℝ, w.1 ≠ 0 → 0 < w.1 ^ 2 + w.2 ^ 2 := fun w hw => by positivity
  have hαβ : ∀ w : ℝ × ℝ, w.1 ≠ 0 → w.2 ≠ 0 → w.1 / (w.1 ^ 2 + w.2 ^ 2) ≠ 0 ∧ w.2 / (w.1 ^ 2 + w.2 ^ 2) ≠ 0 :=
    fun w a b => ⟨div_ne_zero a (hc2 w a).ne', div_ne_zero b (hc2 w a).ne'⟩
  rw [Measure.volume_eq_prod, integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_ne_zero] with w hw
    obtain ⟨a, b⟩ := hw
    obtain ⟨i1, -⟩ := hsh _ _ (hαβ w a b).1 (hαβ w a b).2
    have := i1.const_mul ((w.1 ^ 2 + w.2 ^ 2) ^ (-1 - σ / 2) * (phi w.1 * phi w.2))
    refine this.congr (ae_of_all _ fun v => ?_)
    exact (domF_slice σ g w (hc2 w a).ne' v).symm
  · refine Integrable.mono' (hout.const_mul ((∫ x, g x) * (∫ x, phi x))) ?_ ?_
    · exact (hm.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    · filter_upwards [ae_ne_zero] with w hw
      obtain ⟨a, b⟩ := hw
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have hc := hc2 w a
      set c := w.1 ^ 2 + w.2 ^ 2 with hcdef
      obtain ⟨-, i2⟩ := hsh _ _ (hαβ w a b).1 (hαβ w a b).2
      have hmax : max |w.1 / c| |w.2 / c| = max |w.1| |w.2| / c := by
        rw [abs_div, abs_div, abs_of_pos hc, max_div_div_right hc.le]
      have hmpos : 0 < max |w.1| |w.2| := lt_max_of_lt_left (abs_pos.2 a)
      have hP : 0 ≤ c ^ (-1 - σ / 2) * (phi w.1 * phi w.2) :=
        mul_nonneg (Real.rpow_nonneg hc.le _) (mul_nonneg (phi_nonneg _) (phi_nonneg _))
      have hfn : ∀ v : ℝ × ℝ, ‖domF σ g (w, v)‖ = (c ^ (-1 - σ / 2) * (phi w.1 * phi w.2)) *
          (g ((w.1 / c) * v.2 - (w.2 / c) * v.1) * (phi v.1 * phi v.2)) := fun v => by
        rw [Real.norm_of_nonneg (domF_nonneg σ g hg0 _), domF_slice σ g w hc.ne' v]
      simp only [hfn]
      rw [integral_const_mul]
      calc _ ≤ (c ^ (-1 - σ / 2) * (phi w.1 * phi w.2)) *
            ((∫ x, g x) * (∫ x, phi x) / max |w.1 / c| |w.2 / c|) :=
            mul_le_mul_of_nonneg_left i2 hP
        _ = _ := by
            rw [hmax]
            field_simp

theorem transpose_mp : MeasurePreserving (fun (h : M22) (k i : Fin 2) => h i k) volume volume :=
  ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℝ)

theorem mdom (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g)
    (hg0 : ∀ x, 0 ≤ g x) :
    Integrable (fun h : M22 => g ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) *
      (phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)))) := by
  have hD := integrable_domF σ h0 h1 g hgm hg hg0
  have hmp := GlobalTheory.CompanionTheory.TwoByTwoMajorant.coord_mp.comp transpose_mp
  have := (hmp.integrable_comp hD.aestronglyMeasurable).2 hD
  refine this.congr (ae_of_all _ fun h => ?_)
  simp [domF, GlobalTheory.CompanionTheory.TwoByTwoMajorant.coord_apply, Matrix.det_fin_two]

theorem measurable_eta_norm : Measurable (fun h : M22 => ‖eta h‖) := by
  refine Measurable.norm (measurable_pi_lambda _ fun j => ?_)
  exact GlobalTheory.CompanionTheory.GodementWeight.measurable_inv_entry 1 j

theorem gint : ∀ k : ℕ, 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    Integrable (fun h : M22 => ‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) *
      ‖eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N) := by
  intro k hk σ h0 h1
  refine ⟨8, fun N hN => ?_⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.period_integrand_majorant k hk σ h0 h1 N hN
  have hD := mdom σ h0 h1 (gk k σ) (measurable_gk k σ) (integrable_gk k (by omega) σ h1) (gk_nonneg k σ)
  have hdet := GlobalTheory.CompanionTheory.GodementWeight.measurable_det_of
  have hm : Measurable (fun h : M22 => ‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) *
      ‖eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N) := by
    refine Measurable.div (Measurable.mul (Measurable.mul
      (GlobalTheory.CompanionTheory.GodementWeight.measurable_Wm_inv k).norm (hdet.abs.pow_const _))
      (measurable_eta_norm.pow_const _)) ?_
    fun_prop
  refine Integrable.mono' (hD.const_mul |C|) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)
  have hnn : 0 ≤ gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) *
      (phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1))) :=
    mul_nonneg (mul_nonneg (gk_nonneg _ _ _) (Real.rpow_nonneg (by positivity) _))
      (mul_nonneg (mul_nonneg (phi_nonneg _) (phi_nonneg _)) (mul_nonneg (phi_nonneg _) (phi_nonneg _)))
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hd : (Matrix.of h).det = 0
  · have hinv : (Matrix.of h)⁻¹ = 0 := by
      apply Matrix.nonsing_inv_apply_not_isUnit
      rw [hd]
      simp
    have : ‖Wm k (Matrix.of h)⁻¹‖ = 0 := by simp [hinv, Wm]
    rw [this]
    simpa using mul_nonneg (abs_nonneg C) hnn
  · refine (hC h hd).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self C) hnn

theorem eta_ne_zero (h : M22) (hd : (Matrix.of h).det ≠ 0) : 0 < ‖eta h‖ := by
  rw [norm_pos_iff]
  intro he
  have e0 : (Matrix.of h)⁻¹ 1 0 = 0 := congrFun he 0
  have e1 : (Matrix.of h)⁻¹ 1 1 = 0 := congrFun he 1
  have hm : (Matrix.of h)⁻¹ * Matrix.of h = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hd)
  have := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, e0, e1] at this

theorem norm_integrand (k : ℕ) (Ψ : M23 → ℂ) (δ : Bool) (s : ℂ) (t : ℝˣ) (h : M22) :
    ‖chR δ s t * sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) *
      (Wm k (Matrix.of h)⁻¹ * sg (Matrix.of h).det * ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        innB Ψ h (t : ℝ)⁻¹)‖ =
      |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) *
        ‖innB Ψ h (t : ℝ)⁻¹‖) := by
  have ht : 0 < |(t : ℝ)| := abs_pos.2 t.ne_zero
  have h1 : |(t : ℝ)| ^ (s.re - 1) = |(t : ℝ)| ^ s.re * |(t : ℝ)|⁻¹ := by
    rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]
  simp only [norm_mul, GlobalTheory.CompanionTheory.PrimalInt.norm_sg, GlobalTheory.CompanionTheory.PrimalInt.norm_chR, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (Matrix.of h).det) _),
    abs_inv, abs_abs, h1]
  ring

theorem main : IbpBound → UnipotentJointIntegrability := by
  intro hIbp k hk Φ δ s hs0 hs1 u
  obtain ⟨N₀, hG⟩ := gint k hk s.re hs0 hs1
  obtain ⟨K, hK⟩ := GlobalTheory.T.mult_integral_power_bound s.re hs0 hs1 (N₀ + 1) (by omega)
  have hGN := hG (N₀ + 1) (by omega)
  obtain ⟨C₁, hC₁⟩ := hIbp (N₀ + 1)
  set N := N₀ + 1 with hNdef
  set Ψ : Sw := rtS (cyc u) Φ with hΨdef
  have hΨ : B.rt (cyc u) ⇑Φ = ⇑Ψ := (rtS_apply _ _).symm
  rw [hΨ]
  set B : ℝ := 2 ^ (N + 8) * (Finset.Iic ((N + 8, N) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Ψ with hBdef
  have hB : ∀ n ≤ N, ∀ X : M23, (1 + ‖X‖) ^ (N + 8) * ‖iteratedFDeriv ℝ n (⇑Ψ) X‖ ≤ B :=
    fun n hn X => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N + 8, N)) le_rfl hn Ψ X
  have hInn : ∀ (h : M22) (t : ℝˣ), (Matrix.of h).det ≠ 0 →
      ‖innB (⇑Ψ) h (t : ℝ)⁻¹‖ ≤ |C₁ * B| * |(Matrix.of h).det|⁻¹ /
        ((1 + ‖h‖) ^ N * (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N) := by
    intro h t hd
    refine (hC₁ (⇑Ψ) B (Ψ.smooth ⊤) hB h _ hd).trans ?_
    gcongr
    exact le_abs_self _
  have hmeas : Measurable (fun p : ℝˣ × M22 => chR δ s p.1 * sg p.1 * (((|(p.1 : ℝ)|)⁻¹ : ℝ) : ℂ) *
      (Wm k (Matrix.of p.2)⁻¹ * sg (Matrix.of p.2).det * ((|(Matrix.of p.2).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        innB (⇑Ψ) p.2 (p.1 : ℝ)⁻¹)) := by
    have hv : Measurable (fun p : ℝˣ × M22 => ((p.1 : ℝˣ) : ℝ)) :=
      GlobalTheory.CompanionTheory.PrimalInt.measurable_val.comp measurable_fst
    refine (((((GlobalTheory.CompanionTheory.PrimalInt.measurable_chR δ s).comp measurable_fst).mul
      (GlobalTheory.CompanionTheory.GodementWeight.measurable_sg hv)).mul ?_).mul
      (((GlobalTheory.CompanionTheory.GodementWeight.measurable_weight k).comp measurable_snd).mul
        (measurable_innB _ Ψ.continuous)))
    exact Complex.measurable_ofReal.comp (hv.abs.inv)
  have hW0 : ∀ h : M22, (Matrix.of h).det = 0 → Wm k (Matrix.of h)⁻¹ = 0 := by
    intro h hd
    have hinv : (Matrix.of h)⁻¹ = 0 := by
      apply Matrix.nonsing_inv_apply_not_isUnit
      rw [hd]
      simp
    simp [hinv, Wm]
  have hnorm := fun (t : ℝˣ) (h : M22) => norm_integrand k (⇑Ψ) δ s t h

  have hpt : ∀ (h : M22) (t : ℝˣ), (Matrix.of h).det ≠ 0 →
      |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) *
        ‖innB (⇑Ψ) h (t : ℝ)⁻¹‖) ≤
      (|C₁ * B| * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) / (1 + ‖h‖) ^ N)) *
        (|(t : ℝ)| ^ (s.re - 1) / (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N) := by
    intro h t hd
    have hA : 0 < |(Matrix.of h).det| := abs_pos.2 hd
    have h32 : |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) =
        |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) * |(Matrix.of h).det|⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hA]
      norm_num
    have hb := hInn h t hd
    have hc : 0 ≤ |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2)) := by
      positivity
    calc _ = |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2)) *
          ‖innB (⇑Ψ) h (t : ℝ)⁻¹‖ := by ring
      _ ≤ |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2)) *
          (|C₁ * B| * |(Matrix.of h).det|⁻¹ /
            ((1 + ‖h‖) ^ N * (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N)) := mul_le_mul_of_nonneg_left hb hc
      _ = _ := by
        rw [h32]
        field_simp
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun h => ?_, ?_⟩
  · by_cases hd : (Matrix.of h).det = 0
    · simp only [hW0 h hd, zero_mul, mul_zero]
      exact integrable_zero _ _ _
    · refine Integrable.mono' (((hK _ (eta_ne_zero h hd)).1).const_mul
        (|C₁ * B| * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) / (1 + ‖h‖) ^ N))) ?_ ?_
      · exact (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun t => by
          have := hpt h t hd
          rw [← hnorm t h] at this
          exact this
  · refine Integrable.mono' (hGN.const_mul (|C₁ * B| * |K|)) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := mulR)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun h => ?_
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      by_cases hd : (Matrix.of h).det = 0
      · simp only [hW0 h hd, zero_mul, mul_zero, norm_zero, integral_zero, norm_zero]
        simp
      · have hq := eta_ne_zero h hd
        obtain ⟨i1, i2⟩ := hK _ hq
        set E : ℝ := ‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) / (1 + ‖h‖) ^ N with hE
        have hE0 : 0 ≤ E := by positivity
        have hqp : 0 ≤ ‖eta h‖ ^ (s.re - 1) := Real.rpow_nonneg hq.le _
        calc ∫ t : ℝˣ, ‖_‖ ∂mulR ≤ ∫ t : ℝˣ, (|C₁ * B| * E) *
              (|(t : ℝ)| ^ (s.re - 1) / (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N) ∂mulR := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
                (i1.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
              have := hpt h t hd
              rw [← hnorm t h] at this
              exact this
          _ = (|C₁ * B| * E) * ∫ t : ℝˣ, |(t : ℝ)| ^ (s.re - 1) / (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N ∂mulR :=
              integral_const_mul _ _
          _ ≤ (|C₁ * B| * E) * (K * ‖eta h‖ ^ (s.re - 1)) := by gcongr
          _ ≤ (|C₁ * B| * E) * (|K| * ‖eta h‖ ^ (s.re - 1)) := by
              gcongr
              exact le_abs_self _
          _ = _ := by
              rw [hE]
              ring

end GlobalTheory.CompanionTheory.PerUInt
end
end
