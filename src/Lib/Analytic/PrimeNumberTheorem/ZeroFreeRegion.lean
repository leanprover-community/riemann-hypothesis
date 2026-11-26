module

public import Lib.Analytic.PrimeNumberTheorem.LFunctionGrowth
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ZeroFreeRegion

/-!
# A zero-free region for Dirichlet L-functions

For a Dirichlet character `χ` and large `l`, `entireL χ` has no zero with `re s ≥ 1 - l⁻²⁵` and
`|s| ≤ e^l`, and its logarithmic derivative is at most `2 l²⁵` there. This file delegates the
zero-free region bounds for `regularL` and `entireL` to
`TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ZeroFreeRegion`.

## Relation to the literature

Known result: the classical zero-free region, in the crude form with a power of the logarithm that
the 3-4-1 inequality gives directly. Source: Montgomery and Vaughan, Multiplicative Number Theory I,
2007, ch. 11.
-/

@[expose] public section

open Complex Real Filter Topology

namespace New

variable {N : ℕ} [NeZero N]

private lemma entireL_eq_tauCeti (χ : DirichletCharacter ℂ N) :
    entireL χ = χ.entireLFunction := by
  by_cases hχ : χ = 1
  · subst hχ; simp [entireL]
  · simp [entireL, hχ, DirichletCharacter.entireLFunction_of_ne_one]

private lemma regularL_eq_tauCeti (χ : DirichletCharacter ℂ N) :
    regularL χ = χ.regularizedLFunction := by
  ext s
  by_cases hχ : χ = 1
  · subst hχ; simp [regularL, entireL_eq_tauCeti]
  · simp [regularL, hχ, entireL_eq_tauCeti, DirichletCharacter.regularizedLFunction_of_ne_one,
      DirichletCharacter.entireLFunction_of_ne_one]

/-- For all sufficiently small real `r`, `regularL χ` has absolute value at least `r` within
distance `r` of `1`. -/
lemma eventually_le_norm_regularL (χ : DirichletCharacter ℂ N) :
    ∀ᶠ r : ℝ in 𝓝 0, ∀ s : ℂ, ‖s - 1‖ ≤ r → r ≤ ‖regularL χ s‖ := by
  simpa only [regularL_eq_tauCeti] using χ.eventually_le_norm_regularizedLFunction

/-- Lower bound from the 3-4-1 inequality: `η³ ≤ 256 l⁷ |regularL χ s|⁴` on `re s ≥ 1 + η`,
`|s| ≤ 3 e^l / 2`, if `χ²` is not principal or `|s - 1| ≥ 1 / l`. -/
lemma pow_three_le_mul_norm_regularL_pow (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}
    (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l) {η : ℝ} (hη : 0 < η) (hη_le : η ≤ 1)
    (h_far : χ ^ 2 = 1 → 1 / l ≤ ‖s - 1‖) (h_re : 1 + η ≤ s.re)
    (h_norm : ‖s‖ ≤ 3 / 2 * rexp l) :
    η ^ 3 ≤ 256 * l ^ 7 * ‖regularL χ s‖ ^ 4 := by
  simpa only [regularL_eq_tauCeti] using
    χ.pow_three_le_mul_norm_regularizedLFunction_pow hl hN hη hη_le h_far h_re h_norm

/-- Lower bound `12 / l²² ≤ |regularL χ s|` on `re s ≥ 1 + l⁻²⁵` and `|s| ≤ 3 e^l / 2`. -/
lemma div_pow_le_norm_regularL (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}
    (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_near : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖regularL χ z‖)
    (h_re : 1 + 1 / l ^ 25 ≤ s.re) (h_norm : ‖s‖ ≤ 3 / 2 * rexp l) :
    12 / l ^ 22 ≤ ‖regularL χ s‖ := by
  rw [regularL_eq_tauCeti] at h_near ⊢
  exact χ.div_pow_le_norm_regularizedLFunction hl hN h_near h_re h_norm

/-- Nonvanishing and logarithmic derivative bound `|logDeriv (regularL χ) s| ≤ l²⁵` on
`re s ≥ 1 - l⁻²⁵` and `|s| ≤ e^l`. -/
lemma norm_logDeriv_regularL_le (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}
    (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_near : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖regularL χ z‖)
    (h_re : 1 - 1 / l ^ 25 ≤ s.re) (h_norm : ‖s‖ ≤ rexp l) :
    regularL χ s ≠ 0 ∧ ‖logDeriv (regularL χ) s‖ ≤ l ^ 25 := by
  rw [regularL_eq_tauCeti] at h_near ⊢
  exact χ.regularizedLFunction_ne_zero_and_norm_logDeriv_le hl hN h_near h_re h_norm

/-- Nonvanishing and logarithmic derivative bound `|logDeriv (entireL χ) s| ≤ 2 l²⁵` on
`re s ≥ 1 - l⁻²⁵` and `|s| ≤ e^l`. -/
lemma norm_logDeriv_entireL_le (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}
    (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_near : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖regularL χ z‖)
    (h_re : 1 - 1 / l ^ 25 ≤ s.re) (h_norm : ‖s‖ ≤ rexp l) :
    entireL χ s ≠ 0 ∧ ‖logDeriv (entireL χ) s‖ ≤ 2 * l ^ 25 := by
  rw [regularL_eq_tauCeti] at h_near
  rw [entireL_eq_tauCeti]
  exact χ.entireLFunction_ne_zero_and_norm_logDeriv_le hl hN h_near h_re h_norm

/-- **Zero-free region** for a fixed character: for all large `l`, on `re s ≥ 1 - l⁻²⁵`,
`|s| ≤ e^l` the function `entireL χ` does not vanish and its logarithmic derivative is at most
`2 l²⁵`. -/
theorem eventually_norm_logDeriv_entireL_le (χ : DirichletCharacter ℂ N) :
    ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ 25 ≤ s.re → ‖s‖ ≤ rexp l →
      entireL χ s ≠ 0 ∧ ‖logDeriv (entireL χ) s‖ ≤ 2 * l ^ 25 := by
  simpa only [entireL_eq_tauCeti] using χ.eventually_entireLFunction_ne_zero_and_norm_logDeriv_le

end New
