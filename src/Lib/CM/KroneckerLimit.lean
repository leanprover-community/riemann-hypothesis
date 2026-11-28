module

import Mathlib.Algebra.Ring.IsFormallyReal
import TauCeti.NumberTheory.ModularForms.DedekindEta.LimitFormula
public import Lib.CM.Sigma.Basic

/-!
# Kronecker's first limit formula

`New.kronecker_limit` computes the first two terms at `s = 1` of the Epstein zeta function of a
lattice in `ℂ`, in terms of its area and of the discriminant `g₂³ - 27 g₃²`. The Epstein function is
not continued analytically: only real `s` with `1 < s < 2` occur, and a right derivative at `1`.

The lattice is written as `a (ℤ τ + ℤ)` (`exists_lattice_eq_mul_tau`), and the statement is deduced
from Tau Ceti's limit formula `UpperHalfPlane.tendsto_epsteinZeta_sub` for `ℤ τ + ℤ`. Its constant
involves `UpperHalfPlane.logPeriod τ = log (4 π Im τ |η(τ)|⁴)`, which is
`log (area / π) + log |g₂³ - 27 g₃²| / 6` by `g₂_pow_three_sub_g₃_sq_eq_discriminant`.

Notions from other files:
* `PeriodPair.area`: The area |Im(ω̄₁ω₂)| of the fundamental parallelogram spanned by the periods
  ω₁, ω₂ of a period pair.

## Relation to the literature

Known result: Kronecker's first limit formula. Here the real limit from the right is stated for any
lattice with the discriminant. In Tau Ceti's proof rows are compared with integrals by the mean
value theorem. Source: C. L. Siegel, Lectures on Advanced Analytic Number Theory (1961), Chapter I,
Theorem 1; for a proof of this shape, F. Chamizo, A simple evaluation of a theta value, the
Kronecker limit formula and a formula of Ramanujan, Ramanujan J. (2022), Prop. 3.1.
-/

@[expose] public section

open Complex Nat Equiv MeasureTheory Set Real Function Periodic ModularForm Filter Topology

/-- If the lattice of `L` is `a (ℤ τ + ℤ)`, enumerated by `e`, then the logarithmic period of `τ` is
`log A - log π + log |g₂³ - 27 g₃²| / 6`, `A` being the area of `L`. This uses
`g₂³ - 27 g₃² = (2 π / a)^12 * q * ∏ (1 - q^(j+1))^24` and `|q| = exp (-2 π Im τ)`. -/
private lemma New.logPeriod_eq_of_eq_mul_tau {L : PeriodPair} {a : ℂ} {τ : UpperHalfPlane}
    {e : ℤ × ℤ ≃ L.lattice} (hL : ∀ p : ℤ × ℤ, (e p : ℂ) = a * (p.1 * τ + p.2)) (ha : a ≠ 0)
    (h_area : L.area = ‖a‖ ^ 2 * τ.im) :
    UpperHalfPlane.logPeriod τ =
      Real.log L.area - Real.log π + Real.log ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ / 6 := by
  have hy := τ.im_pos
  let P : ℂ := ∏' j : ℕ, (1 - eta_q j (τ : ℂ))
  have hP : P ≠ 0 := eta_tprod_ne_zero hy
  have h_disc : Real.log ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ =
      12 * (Real.log 2 + Real.log π - Real.log ‖a‖) - 2 * π * τ.im + 24 * Real.log ‖P‖ := by
    rw [g₂_pow_three_sub_g₃_sq_eq_discriminant hL]
    norm_num [discriminant, ModularForm.eta, P, hP, norm_exp, qParam, Real.log_mul, log_div, ha]
    ring
  rw [UpperHalfPlane.logPeriod_eq_log_tprod, h_disc, h_area,
    Real.log_mul (by positivity) hy.ne', Real.log_pow, Real.log_mul (by norm_num) pi_ne_zero,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- If the lattice of `L` is `a (ℤ τ + ℤ)`, enumerated by `e`, the factor `‖a‖ ^ 2` cancels between
`‖e p‖ ^ 2` and the area: `‖e p‖ ^ 2 / k / A = (k Im τ / |p₁ τ + p₂|²)⁻¹`. -/
private lemma New.norm_sq_div_area_eq_inv {L : PeriodPair} {a : ℂ} {τ : UpperHalfPlane}
    {e : ℤ × ℤ ≃ L.lattice} (hL : ∀ p : ℤ × ℤ, (e p : ℂ) = a * (p.1 * τ + p.2)) (ha : a ≠ 0)
    (h_area : L.area = ‖a‖ ^ 2 * τ.im) {k : ℝ} (hk : k ≠ 0) (p : ℤ × ℤ) :
    ‖(e p : ℂ)‖ ^ 2 / k / L.area = (k * (τ.im / ‖(p.1 : ℂ) * τ + p.2‖ ^ 2))⁻¹ := by
  rw [hL, norm_mul, mul_pow, h_area]
  by_cases hw : ‖(p.1 : ℂ) * τ + p.2‖ = 0
  · simp [hw]
  field_simp

/-- **Kronecker's first limit formula.** Let `L` be a lattice of area `A` and discriminant
`Δ = g₂³ - 27 g₃²`, and let `k > 0`. There is a real function `F` with (a) `F 1 = π k`, (b) right
derivative `F 1 * (2 γ - log (A / (k π²)) - (log |Δ|) / 6)` at `1`, `γ` being Euler's constant, and
(c) `F s = (s - 1) ∑ (|l|² / (k A))^(-s)` for `1 < s < 2`. The sum is over all `l` in the lattice;
the term `l = 0` is `0`, since `0 ^ (-s) = 0` in Lean. For `k = 1` this is the expansion
`∑ (|l|² / A)^(-s) = π / (s - 1) + π (2 γ - log (A |Δ|^(1/6) / π²)) + o(1)` as `s` decreases to
`1`. -/
lemma New.kronecker_limit (L : PeriodPair) (k : ℝ) (hk : 0 < k) :
    ∃ F : ℝ → ℝ,
      -- (a) the value at 1
      F 1 = π * k ∧
      -- (b) the right derivative at 1
      HasDerivWithinAt F
        (F 1 *
          (2 * eulerMascheroniConstant - Real.log (PeriodPair.area L / k / π ^ 2) -
            Real.log ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ / 6))
        (Ioi 1) 1 ∧
      -- (c) the series for 1 < s < 2
      ∀ s ∈ Ioo 1 2,
        HasSum (fun l : L.lattice ↦ (s - 1) * (‖l.val‖ ^ 2 / k / L.area) ^ (-s)) (F s) := by
  obtain ⟨a, τ, e, hL, ha, h_area⟩ := exists_lattice_eq_mul_tau L
  have hA : 0 < L.area := area_pos L
  let E := UpperHalfPlane.epsteinZeta τ
  have h_period := logPeriod_eq_of_eq_mul_tau hL ha h_area
  let F : ℝ → ℝ := Function.update (fun s ↦ k ^ s * ((s - 1) * E s)) 1 (π * k)
  have hF (s : ℝ) (hs : 1 < s) : F s = k ^ s * ((s - 1) * E s) :=
    Function.update_of_ne hs.ne' _ _
  have hF_one : F 1 = π * k := Function.update_self _ _ _
  refine ⟨F, hF_one, ?_, fun s hs ↦ e.hasSum_iff.1 ?_⟩
  · -- the slope of `F` at `1` is `k ^ s (E s - π / (s - 1)) + π (k ^ s - k) / (s - 1)`
    have hk_deriv : HasDerivAt (fun s : ℝ ↦ k ^ s) (Real.log k * 1 * k ^ (1 : ℝ)) 1 :=
      (hasDerivAt_id (1 : ℝ)).const_rpow hk
    have h_lim := ((hk_deriv.continuousAt.continuousWithinAt (s := Ioi 1)).tendsto.mul
      (UpperHalfPlane.tendsto_epsteinZeta_sub τ)).add
      (((hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hk_deriv.hasDerivWithinAt).const_mul π)
    have h_eq : (fun s ↦ k ^ s * (E s - π / (s - 1)) + π * slope (fun s : ℝ ↦ k ^ s) 1 s)
        =ᶠ[𝓝[>] 1] slope F 1 := by
      filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      simp only [slope_def_field, hF s hs, hF_one, rpow_one]
      field [sub_ne_zero.2 hs.ne']
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
    convert h_lim.congr' h_eq using 2
    rw [hF_one, h_period, Real.log_div (by positivity) (by positivity),
      Real.log_div hA.ne' hk.ne', Real.log_pow, rpow_one]
    ring
  · -- the factor `‖a‖ ^ 2` cancels between `‖l‖ ^ 2` and the area
    rw [hF s hs.1, show k ^ s * ((s - 1) * E s) = (s - 1) * k ^ s * E s by ring]
    refine ((UpperHalfPlane.hasSum_epsteinZeta τ hs.1).mul_left ((s - 1) * k ^ s)).congr_fun
      fun p ↦ ?_
    change (s - 1) * (‖(e p : ℂ)‖ ^ 2 / k / L.area) ^ (-s) = _
    rw [norm_sq_div_area_eq_inv hL ha h_area hk.ne', rpow_neg (by positivity),
      Real.inv_rpow (by positivity), inv_inv, Real.mul_rpow hk.le (by positivity)]
    ring
