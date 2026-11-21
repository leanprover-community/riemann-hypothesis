import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable

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
