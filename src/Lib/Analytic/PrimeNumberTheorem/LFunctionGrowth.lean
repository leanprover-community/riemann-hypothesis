module

public import Lib.Analytic.EntireLFunction
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds

/-!
# Growth of Dirichlet L-functions near the line `re s = 1`

Let `χ` be a character modulo `N`, and let `𝖿_χ(s)` (`regularL χ s`) be `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. The right-half-plane bound from Tau Ceti gives
`|𝖿_χ(s)| ≤ 8 N |s|` in `re s ≥ 1 / 2`, and the three-lines theorem improves this to
`|𝖿_χ(s)| ≤ l²` for `re s ≥ 1 - 1 / l` and `|s| ≤ 3 e^l`, whenever `l ≥ 10¹⁰` and `N ≤ e^l`.

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

open Complex Real Set Filter Topology MeasureTheory Metric Asymptotics DirichletCharacter
  HadamardThreeLines
open scoped Classical

namespace New

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}

omit [NeZero N] in
/-- If `re s ≥ 1 + 1 / A` with `A > 0`, then `|L(s, χ)| ≤ 1 + A`, since the Dirichlet series of
`χ` is dominated by `ζ(re s)`. -/
lemma norm_LSeries_char_le {A : ℝ} (hA : 0 < A) (hs : 1 + 1 / A ≤ s.re) :
    ‖LSeries (fun n : ℕ ↦ χ n) s‖ ≤ 1 + A := by
  have hs_one : 1 < s.re := by linarith [one_div_pos.2 hA]
  have h_summable : Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ s.re :=
    Real.summable_one_div_nat_rpow.2 hs_one
  have term_le (n : ℕ) : ‖LSeries.term (χ ·) s n‖ ≤ 1 / (n : ℝ) ^ s.re := by
    rw [LSeries.norm_term_eq]
    split_ifs
    · positivity
    · exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  -- `ζ(σ) - 1 / (σ - 1) = 1 - σ T` with `T ≥ 0`
  have zeta_le : ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s.re ≤ 1 + 1 / (s.re - 1) := by
    have h_nonneg : 0 ≤ s.re * ZetaAsymptotics.termTSum s.re :=
      mul_nonneg (by linarith) (tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg _ _)
    linarith [ZetaAsymptotics.zeta_limit_aux1 hs_one]
  calc
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := tsum_of_norm_bounded h_summable.hasSum term_le
    _ = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s.re := by
      rw [h_summable.tsum_eq_zero_add]
      simp [Real.zero_rpow (one_pos.trans hs_one).ne']
    _ ≤ 1 + 1 / (s.re - 1) := zeta_le
    _ ≤ 1 + A := by linarith [(one_div_le hA (sub_pos.2 hs_one)).1 (by linarith)]

/-- `𝖿_χ(s)` is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal. The entire function `entireL χ`
has the factor `s - 1` in that case; dividing by `s` keeps the size of `L(s, χ)` for large `|s|`. -/
def regularL (s : ℂ) : ℂ := entireL χ s / if χ = 1 then s else 1

/-- `𝖿_χ` (`regularL χ`: `L(s, χ)`, times `(s - 1) / s` if `χ` is principal) is holomorphic in
`re s > 0`. -/
lemma differentiableAt_regularL (hs : 0 < s.re) : DifferentiableAt ℂ (regularL χ) s := by
  have h_denom_diff : DifferentiableAt ℂ (fun z : ℂ ↦ if χ = 1 then z else 1) s := by
    split_ifs <;> fun_prop
  have h_denom_ne : (if χ = 1 then s else 1) ≠ 0 := by
    split_ifs
    exacts [ne_zero_of_re_pos hs, one_ne_zero]
  exact (analyticAt_entireL χ s).differentiableAt.div h_denom_diff h_denom_ne

/-- In `re s > 1` the regularised function `𝖿_χ` (`regularL χ`) is `L(s, χ) (s - δ) / s`, with
`δ = 1` if `χ` is principal and `δ = 0` otherwise. -/
lemma regularL_eq (hs : 1 < s.re) :
    regularL χ s = LSeries (fun n : ℕ ↦ χ n) s / s * (s - if χ = 1 then 1 else 0) := by
  have hs_zero : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  rw [regularL, entireL, ← χ.LFunction_eq_LSeries hs]
  split_ifs with hχ
  · rw [hχ, LFunctionTrivChar₁, Function.update_of_ne (ne_of_apply_ne re hs.ne')]
    ring
  · field

/-- `|s - δ| ≤ |s|` in `re s ≥ 1 / 2`, where `δ` is `1` or `0` as the proposition `p` holds or
not (in the uses, `p` says that a character is principal). -/
lemma norm_sub_ite_le {p : Prop} [Decidable p] (hs : 1 / 2 ≤ s.re) :
    ‖s - if p then 1 else 0‖ ≤ ‖s‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  split_ifs
  · simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, one_re, one_im]
    -- For `δ = 1` this is `(re s - 1)² ≤ (re s)²`.
    linarith
  · simp

/-- Linear growth bound: `|𝖿_χ(s)| ≤ 8 N |s|` in `re s ≥ 1 / 2`, where `𝖿_χ` (`regularL χ`) is
`L(s, χ)`, times `(s - 1) / s` if `χ` is principal, and `N` is the modulus of `χ`. -/
lemma norm_regularL_le_linear (hs : 1 / 2 ≤ s.re) : ‖regularL χ s‖ ≤ 8 * N * ‖s‖ := by
  have bound_ne {z : ℂ} (hz : 1 / 2 ≤ z.re) (hz1 : z ≠ 1) :
      ‖regularL χ z‖ ≤ 8 * N * ‖z‖ := by
    have hz_pos : 0 < z.re := by linarith
    have hz_norm : 1 / 2 ≤ ‖z‖ := hz.trans (re_le_norm z)
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    by_cases hχ : χ = 1
    · have h_eq : regularL χ z = (z - 1) / z * χ.LFunction z := by
        simp [regularL, entireL, hχ, LFunctionTrivChar₁, Function.update_of_ne hz1]
        ring
      have h_sub : ‖z - 1‖ ≤ ‖z‖ := by simpa using norm_sub_ite_le (p := True) hz
      have h_inv : ‖z - 1‖ / ‖z‖ * (‖z - 1‖⁻¹ + 1 + ‖z‖ / z.re) ≤ 8 * ‖z‖ := by
        have hz1_pos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
        have h1_le : 1 / ‖z‖ ≤ 4 * ‖z‖ := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        have h2_le : ‖z - 1‖ / ‖z‖ ≤ 2 * ‖z‖ := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        have h3_le : ‖z - 1‖ / z.re ≤ 2 * ‖z‖ := by
          rw [div_le_iff₀ hz_pos]
          nlinarith
        calc
          ‖z - 1‖ / ‖z‖ * (‖z - 1‖⁻¹ + 1 + ‖z‖ / z.re)
              = 1 / ‖z‖ + ‖z - 1‖ / ‖z‖ + ‖z - 1‖ / z.re := by
            field_simp [hz1_pos.ne', (show (0 : ℝ) < ‖z‖ by linarith).ne', hz_pos.ne']
          _ ≤ 8 * ‖z‖ := by linarith
      calc
        ‖regularL χ z‖ = ‖z - 1‖ / ‖z‖ * ‖χ.LFunction z‖ := by rw [h_eq, norm_mul, norm_div]
        _ ≤ ‖z - 1‖ / ‖z‖ * (N * (‖z - 1‖⁻¹ + 1 + ‖z‖ / z.re)) := by
          gcongr
          exact χ.norm_LFunction_le hz_pos (.inl hz1)
        _ = N * (‖z - 1‖ / ‖z‖ * (‖z - 1‖⁻¹ + 1 + ‖z‖ / z.re)) := by ring
        _ ≤ N * (8 * ‖z‖) := by gcongr
        _ = 8 * N * ‖z‖ := by ring
    · have h_eq : regularL χ z = χ.LFunction z := by simp [regularL, entireL, hχ]
      calc
        ‖regularL χ z‖ = ‖χ.LFunction z‖ := by rw [h_eq]
        _ ≤ N * ‖z‖ / z.re := χ.norm_LFunction_le_level_mul_norm_div_re hχ hz_pos
        _ ≤ N * ‖z‖ / (1 / 2) := by gcongr
        _ ≤ 8 * N * ‖z‖ := by nlinarith [norm_nonneg z]
  -- Extend the estimate from the punctured open half-plane by continuity.
  have hs_closure : s ∈ closure ({z : ℂ | 1 / 2 < z.re} ∩ {1}ᶜ) :=
    closure_minimal
      ((dense_compl_singleton (1 : ℂ)).open_subset_closure_inter (isOpen_re_gt (1 / 2)))
      isClosed_closure (by simpa only [closure_setOfPred_lt_re, Set.mem_ofPred_eq] using hs)
  exact ContinuousWithinAt.closure_le (g := fun z : ℂ ↦ 8 * N * ‖z‖) hs_closure
    (differentiableAt_regularL χ (by linarith)).continuousAt.norm.continuousWithinAt
    (by fun_prop) (fun z hz ↦ bound_ne (le_of_lt hz.1) hz.2)

/-- For `l ≥ 1` and `re s > 1`, at distance at least `1 / l` from `1` if `χ` is principal, we have
`|L(s, χ)| ≤ 2 l |𝖿_χ(s)|`, where `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times `(s - 1) / s` if `χ` is
principal. -/
lemma norm_LSeries_le_mul_norm_regularL (hs : 1 < s.re) (hl : 1 ≤ l)
    (h_far : χ = 1 → 1 / l ≤ ‖s - 1‖) :
    ‖LSeries (fun n : ℕ ↦ χ n) s‖ ≤ 2 * l * ‖regularL χ s‖ := by
  have hs_norm : 1 < ‖s‖ := hs.trans_le (re_le_norm s)
  have norm_le : ‖s‖ ≤ 2 * l * ‖s - if χ = 1 then 1 else 0‖ := by
    split_ifs with hχ
    · have h_one : 1 ≤ ‖s - 1‖ * l := (div_le_iff₀ (by linarith)).1 (h_far hχ)
      nlinarith [norm_nonneg (s - 1), norm_le_norm_sub_add s 1, norm_one (α := ℂ)]
    · simpa using le_mul_of_one_le_left (norm_nonneg s) (by linarith : 1 ≤ 2 * l)
  calc
    ‖LSeries (χ ·) s‖ = ‖LSeries (χ ·) s‖ / ‖s‖ * ‖s‖ := by field
    _ ≤ ‖LSeries (χ ·) s‖ / ‖s‖ * (2 * l * ‖s - if χ = 1 then 1 else 0‖) := by gcongr
    _ = 2 * l * ‖regularL χ s‖ := by simp [regularL_eq χ hs]; ring

/-- If `l ≥ 10¹⁰` and the modulus `N` is at most `e^l`, then `|𝖿_χ(s)| ≤ l²` for
`re s ≥ 1 - 1 / l` and `|s| ≤ 3 e^l`. Here `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. -/
lemma norm_regularL_le_sq (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l) (h_re : 1 - 1 / l ≤ s.re)
    (h_norm : ‖s‖ ≤ 3 * rexp l) : ‖regularL χ s‖ ≤ l ^ 2 := by
  -- Apply the three-lines theorem to `g(z) = 𝖿_χ(z) / (z - s + 2)` on the strip
  -- `a ≤ re z ≤ a + 1 / 3` whose right edge lies at `re s + 2 / l ≥ 1 + 1 / l`. The left edge,
  -- where `|g| ≤ e^(3 l)`, has the weight `6 / l` at `s`. The denominator makes `g` bounded; it
  -- has modulus at least `1` on the strip and is `2` at `s`.
  have inv_pos : 0 < 1 / l := by positivity
  have inv_le : 1 / l ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have exp_ge : l + 1 ≤ rexp l := add_one_le_exp l
  set a : ℝ := s.re + 2 * (1 / l) - 1 / 3 with ha
  let g (z : ℂ) : ℂ := regularL χ z / (z - (s - 2))
  have denom_ge (z : ℂ) (hz : a ≤ z.re) : 1 ≤ ‖z - (s - 2)‖ :=
    le_trans (by simp; linarith) (re_le_norm _)
  have g_le_exp_cube (z : ℂ) (hz : a ≤ z.re) : ‖g z‖ ≤ rexp l ^ 3 := by
    have h_denom : 1 ≤ ‖z - (s - 2)‖ := denom_ge z hz
    have hz_norm : ‖z‖ ≤ 4 * rexp l * ‖z - (s - 2)‖ := by
      nlinarith [norm_le_norm_sub_add z (s - 2), norm_sub_le s 2, Complex.norm_two]
    rw [norm_div, div_le_iff₀ (by linarith)]
    calc
      ‖regularL χ z‖ ≤ 8 * N * ‖z‖ := norm_regularL_le_linear χ (by linarith)
      _ ≤ 8 * rexp l * (4 * rexp l * ‖z - (s - 2)‖) := by gcongr
      _ = 32 * rexp l ^ 2 * ‖z - (s - 2)‖ := by ring
      _ ≤ rexp l ^ 3 * ‖z - (s - 2)‖ := by
        gcongr
        nlinarith [sq_nonneg (rexp l), mul_le_mul exp_ge exp_ge]
  have right_edge (z : ℂ) (hz : z.re = a + 1 / 3) : ‖g z‖ ≤ 1 + l := by
    have hz_norm : 0 < ‖z‖ := by linarith [re_le_norm z]
    calc
      ‖g z‖ ≤ ‖regularL χ z‖ :=
        (norm_div _ _).trans_le (div_le_self (norm_nonneg _) (denom_ge z (by linarith)))
      _ ≤ ‖LSeries (χ ·) z‖ / ‖z‖ * ‖z‖ := by
        rw [regularL_eq χ (by linarith), norm_mul, norm_div]
        gcongr
        exact norm_sub_ite_le (by linarith)
      _ = ‖LSeries (χ ·) z‖ := div_mul_cancel₀ _ hz_norm.ne'
      _ ≤ 1 + l := by
        have h_re_right : 1 + 1 / l ≤ z.re := by linarith
        exact norm_LSeries_char_le χ (by linarith) h_re_right
  have g_diff : DiffContOnCl ℂ g (verticalStrip a (a + 1 / 3)) := by
    refine DifferentiableOn.diffContOnCl fun z hz ↦ ?_
    rw [verticalStrip, closure_preimage_re, closure_Ioo (by linarith)] at hz
    obtain ⟨hz_left, -⟩ : a ≤ z.re ∧ z.re ≤ a + 1 / 3 := hz
    have hz_pos : 0 < z.re := by linarith
    have h_denom : z - (s - 2) ≠ 0 := norm_pos_iff.1 (one_pos.trans_le (denom_ge z hz_left))
    exact ((differentiableAt_regularL χ hz_pos).fun_div (by fun_prop)
      h_denom).differentiableWithinAt
  have weight : (s.re - a) / (a + 1 / 3 - a) = 1 - 6 / l := by rw [ha]; ring
  have three_lines : ‖g s‖ ≤ (rexp l ^ 3) ^ (1 - (1 - 6 / l)) * (1 + l) ^ (1 - 6 / l) := by
    have hs_strip : s ∈ verticalClosedStrip a (a + 1 / 3) := ⟨by linarith, by linarith⟩
    have g_bdd : BddAbove ((norm ∘ g) '' verticalClosedStrip a (a + 1 / 3)) :=
      ⟨rexp l ^ 3, forall_mem_image.2 fun z ⟨hz, _⟩ ↦ g_le_exp_cube z hz⟩
    rw [← weight]
    exact norm_le_interp_of_mem_verticalClosedStrip' (by linarith) hs_strip g_diff g_bdd
      (fun z hz ↦ g_le_exp_cube z hz.ge) right_edge
  have left_factor : (rexp l ^ 3) ^ (1 - (1 - 6 / l)) ≤ 3 ^ 18 := by
    have h_exp : ((3 : ℕ) * l) * (1 - (1 - 6 / l)) = (18 : ℕ) * 1 := by field
    rw [← Real.exp_natCast_mul, ← Real.exp_mul, h_exp, Real.exp_natCast_mul]
    exact pow_le_pow_left₀ (exp_nonneg 1) exp_one_lt_three.le 18
  have right_factor : (1 + l) ^ (1 - 6 / l) ≤ 1 + l :=
    rpow_le_self_of_one_le (by linarith) (sub_le_self 1 (by positivity))
  calc
    ‖regularL χ s‖ = 2 * ‖g s‖ := by simp [g, mul_div_cancel₀]
    _ ≤ 2 * (3 ^ 18 * (1 + l)) := by grw [three_lines, left_factor, right_factor]
    _ ≤ l ^ 2 := by nlinarith

/-- Cauchy's estimate: if `l ≥ 10¹⁰` and the modulus `N` is at most `e^l`, then `|𝖿_χ'(s)| ≤ 2 l³`
for `re s ≥ 1 - 1 / (2 l)` and `|s| ≤ 2 e^l`. Here `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. -/
lemma norm_deriv_regularL_le (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l) (h_re : 1 - 1 / l / 2 ≤ s.re)
    (h_norm : ‖s‖ ≤ 2 * rexp l) : ‖deriv (regularL χ) s‖ ≤ 2 * l ^ 3 := by
  have inv_le : 1 / l ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have disc (z : ℂ) (hz : z ∈ closedBall s (1 / l / 2)) :
      1 - 1 / l ≤ z.re ∧ ‖z‖ ≤ 3 * rexp l := by
    rw [mem_closedBall_iff_norm] at hz
    exact ⟨by linarith [neg_le_of_abs_le (abs_re_le_norm (z - s)), sub_re z s],
      by linarith [norm_le_norm_sub_add z s, add_one_le_exp l]⟩
  have h_diff : DiffContOnCl ℂ (regularL χ) (ball s (1 / l / 2)) :=
    DifferentiableOn.diffContOnCl_ball (fun z hz ↦ (differentiableAt_regularL χ
      (by linarith [(disc z hz).1])).differentiableWithinAt) subset_rfl
  have h_sphere (z : ℂ) (hz : z ∈ sphere s (1 / l / 2)) : ‖regularL χ z‖ ≤ l ^ 2 := by
    obtain ⟨hz_re, hz_norm⟩ := disc z (sphere_subset_closedBall hz)
    exact norm_regularL_le_sq χ hl hN hz_re hz_norm
  calc
    _ ≤ l ^ 2 / (1 / l / 2) :=
      norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) h_diff h_sphere
    _ = 2 * l ^ 3 := by field

end New

end
