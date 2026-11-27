module

import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.NumberTheory.DirichletCharacter.LFunction.GrowthNearOne
public import Lib.General.NumberTheory.ImaginaryQuadraticField

/-!
# Growth of Dirichlet L-functions near the line `re s = 1`

Let `χ` be a character modulo `N`, and let `𝖿_χ(s)` (`regularL χ s`) be `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. The three-lines theorem and Cauchy estimates from Tau Ceti give
`|𝖿_χ(s)| ≤ l²` for `re s ≥ 1 - 1 / l`, `|s| ≤ 3 e^l` and `|𝖿_χ'(s)| ≤ 2 l³` for
`re s ≥ 1 - 1 / (2 l)`, `|s| ≤ 2 e^l`, whenever `l ≥ 10¹⁰` and `N ≤ e^l`.

Notions from other files:
* `entireL χ`: the entire function equal to `L(s, χ)` if `χ` is not principal, and to the
  continuation of `(s - 1) L(s, χ)` if it is.

## Relation to the literature

Known result: the bound `L(s, χ) ≪ log (N |s|)` near `re s = 1` and away from the pole. It is proved
here for `𝖿_χ` and with a square in place of the first power. Source: Montgomery and Vaughan,
Multiplicative Number Theory I, 2007, Lemma 10.15.
-/

@[expose] public section

noncomputable section

open Complex Real DirichletCharacter
open scoped Classical

namespace New

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}

omit [NeZero N] in
/-- If `re s ≥ 1 + 1 / A` with `A > 0`, then `|L(s, χ)| ≤ 1 + A`, since the Dirichlet series of
`χ` is dominated by `ζ(re s)`. -/
lemma norm_LSeries_char_le {A : ℝ} (hA : 0 < A) (hs : 1 + 1 / A ≤ s.re) :
    ‖LSeries (fun n : ℕ ↦ χ n) s‖ ≤ 1 + A :=
  χ.norm_LSeries_le_one_add hA hs

/-- `𝖿_χ(s)` is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal. The entire function `entireL χ`
has the factor `s - 1` in that case; dividing by `s` keeps the size of `L(s, χ)` for large `|s|`. -/
def regularL (s : ℂ) : ℂ := entireL χ s / if χ = 1 then s else 1

private lemma regularL_eq_regularizedLFunction : regularL χ = χ.regularizedLFunction := by
  ext s
  obtain rfl | hχ := eq_or_ne χ 1
  · simp [regularL, entireL, DirichletCharacter.entireLFunction_one]
  · simp [regularL, entireL, hχ, DirichletCharacter.regularizedLFunction_of_ne_one]

/-- `𝖿_χ` (`regularL χ`: `L(s, χ)`, times `(s - 1) / s` if `χ` is principal) is holomorphic in
`re s > 0`. -/
lemma differentiableAt_regularL (hs : 0 < s.re) : DifferentiableAt ℂ (regularL χ) s :=
  regularL_eq_regularizedLFunction χ ▸
    χ.differentiableAt_regularizedLFunction (.inl (ne_zero_of_re_pos hs))

/-- In `re s > 1` the regularised function `𝖿_χ` (`regularL χ`) is `L(s, χ) (s - δ) / s`, with
`δ = 1` if `χ` is principal and `δ = 0` otherwise. -/
lemma regularL_eq (hs : 1 < s.re) :
    regularL χ s = LSeries (fun n : ℕ ↦ χ n) s / s * (s - if χ = 1 then 1 else 0) := by
  convert regularL_eq_regularizedLFunction χ ▸ χ.regularizedLFunction_eq_LSeries hs

/-- For `l ≥ 1` and `re s > 1`, at distance at least `1 / l` from `1` if `χ` is principal, we have
`|L(s, χ)| ≤ 2 l |𝖿_χ(s)|`, where `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times `(s - 1) / s` if `χ` is
principal. -/
lemma norm_LSeries_le_mul_norm_regularL (hs : 1 < s.re) (hl : 1 ≤ l)
    (h_far : χ = 1 → 1 / l ≤ ‖s - 1‖) :
    ‖LSeries (fun n : ℕ ↦ χ n) s‖ ≤ 2 * l * ‖regularL χ s‖ :=
  regularL_eq_regularizedLFunction χ ▸ χ.norm_LSeries_le_mul_norm_regularizedLFunction hs hl h_far

/-- If `l ≥ 10¹⁰` and the modulus `N` is at most `e^l`, then `|𝖿_χ(s)| ≤ l²` for
`re s ≥ 1 - 1 / l` and `|s| ≤ 3 e^l`. Here `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. -/
lemma norm_regularL_le_sq (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l) (h_re : 1 - 1 / l ≤ s.re)
    (h_norm : ‖s‖ ≤ 3 * rexp l) : ‖regularL χ s‖ ≤ l ^ 2 :=
  regularL_eq_regularizedLFunction χ ▸ χ.norm_regularizedLFunction_le_sq hl hN h_re h_norm

/-- Cauchy's estimate: if `l ≥ 10¹⁰` and the modulus `N` is at most `e^l`, then `|𝖿_χ'(s)| ≤ 2 l³`
for `re s ≥ 1 - 1 / (2 l)` and `|s| ≤ 2 e^l`. Here `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. -/
lemma norm_deriv_regularL_le (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l) (h_re : 1 - 1 / l / 2 ≤ s.re)
    (h_norm : ‖s‖ ≤ 2 * rexp l) : ‖deriv (regularL χ) s‖ ≤ 2 * l ^ 3 :=
  regularL_eq_regularizedLFunction χ ▸ χ.norm_deriv_regularizedLFunction_le hl hN h_re h_norm

end New

end
