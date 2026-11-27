module

import TauCeti.Analysis.Complex.Taylor.RapidDecay
import TauCeti.Analysis.Convex.Lipschitz
import TauCeti.Analysis.LaplaceTransform.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HalfPlane
public import Lib.Speed
import Lib.Analytic.EntireLFunction

/-!
# A Tauberian theorem with a power of the logarithm

Let `R` be measurable and Lipschitz on `v ≥ 0`, and let its transform `∫₀^∞ R(v) e^{(1 - s) v} dv`
be `(F s - F 1) / (s - 1)` in `re s > 2`. Suppose that for all large `l` the function `F` is
holomorphic and at most `l ^ A` on `re s ≥ 1 - l ^ (-A)`, `|s| ≤ e ^ l`. Then `R(v) = O(v ^ (-B))`
for every `B`. The theorem is meant for the remainder in the prime number theorem for a sum over
prime powers with weights that vanish at the cutoff `x`: at `x = e ^ v` it is Lipschitz in `v`.

The proof reads one Taylor coefficient of the transform at a far point `1 + H` in two ways. It is a
mean of `R` against a Gamma density that is concentrated at the given point `u`, hence close to
`R(u)`; and it is small by Tau Ceti's Cauchy estimate on a disc reaching left of `re s = 1`.

## Relation to the literature

Known result: the passage from a zero-free region to the error term of the prime number theorem.
Source: Montgomery and Vaughan, Multiplicative Number Theory I, 2007, Section 6.2, where a contour
integral is used in place of the Taylor coefficient.
-/

@[expose] public section

open Complex Filter MeasureTheory Metric Set Topology

open scoped Nat Real

namespace New

/-- Differentiation under the integral sign. Let `R` be measurable with `|R v| ≤ C e^v` for
`v ≥ 0`, and let `Φ s` be its transform `∫₀^∞ R(v) e^{(1 - s) v} dv` in `re s > 2`. Then, for such
`s`, the function `(-v)^k R(v) e^{(1 - s) v}` is integrable on `(0, ∞)`, and its integral is the
`k`-th derivative of `Φ` at `s`. -/
lemma iteratedDeriv_transform {R : ℝ → ℝ} {C : ℝ} {Φ : ℂ → ℂ} (hR : Measurable R)
    (R_le : ∀ v : ℝ, 0 ≤ v → |R v| ≤ C * rexp v)
    (Φ_eq : ∀ s : ℂ, 2 < s.re → Φ s = ∫ v in Ioi (0 : ℝ), R v * cexp ((1 - s) * v)) (k : ℕ) (s : ℂ)
    (hs : 2 < s.re) :
    IntegrableOn (fun v : ℝ ↦ (-v) ^ k * R v * cexp ((1 - s) * v)) (Ioi 0) ∧
      iteratedDeriv k Φ s = ∫ v in Ioi (0 : ℝ), (-v) ^ k * R v * cexp ((1 - s) * v) := by
  have h_mul (w : ℂ) (v : ℝ) : cexp (-w * v) * ((R v : ℂ) * cexp v) = R v * cexp ((1 - w) * v) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  have h_lap : ∀ᶠ w in 𝓝 s, TauCeti.HasLaplace (fun v : ℝ ↦ (R v : ℂ) * cexp v) w (Φ w) := by
    filter_upwards [(isOpen_re_gt (2 : ℝ)).mem_nhds hs] with w hw
    exact TauCeti.HasLaplace.intro
      (by simpa only [IntegrableOn, smul_eq_mul, h_mul] using
        integrableOn_laplace_of_abs_le hR R_le hw)
      (by simpa only [smul_eq_mul, h_mul] using (Φ_eq w hw).symm)
  have hk := TauCeti.hasLaplace_neg_pow_smul_iteratedDeriv h_lap k
  have h_eq (v : ℝ) : cexp (-s * v) • ((-(v : ℂ)) ^ k • ((R v : ℂ) * cexp v)) =
      (-v : ℂ) ^ k * R v * cexp ((1 - s) * v) := by
    simp only [smul_eq_mul]
    calc cexp (-s * v) * ((-v : ℂ) ^ k * ((R v : ℂ) * cexp v))
        = (-v : ℂ) ^ k * (cexp (-s * v) * ((R v : ℂ) * cexp v)) := by ring
      _ = (-v : ℂ) ^ k * R v * cexp ((1 - s) * v) := by rw [h_mul]; ring
  exact ⟨by simpa only [IntegrableOn, h_eq] using hk.integrable,
    by simpa only [h_eq] using hk.integral_eq.symm⟩

/-- For `H > 0` the moments of `e^{-H v}` on `(0, ∞)` exist: the function `v ^ j e^{-H v}` is
integrable there, with integral `j! / H ^ (j + 1)`. -/
lemma integrableOn_and_integral_pow_mul_exp_neg_mul {H : ℝ} (hH : 0 < H) (j : ℕ) :
    IntegrableOn (fun v : ℝ ↦ v ^ j * rexp (-H * v)) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), v ^ j * rexp (-H * v) = j ! / H ^ (j + 1) := by
  have h_eq : ∫ v in Ioi (0 : ℝ), v ^ j * rexp (-H * v) = j ! / H ^ (j + 1) :=
    mod_cast laplace_pow (s := H) (by simpa) j
  exact ⟨.of_integral_ne_zero (h_eq.trans_ne (by positivity)), h_eq⟩

/-- For `H > 0` and the mean `u = (k + 1) / H` of the Gamma density
`H ^ (k + 1) v ^ k e^{-H v} / k!`, the function `v ^ k e^{-H v} (a + b (v - u)²)` is integrable on
`(0, ∞)`, with integral `k! / H ^ (k + 1) (a + b (k + 1) / H²)`. -/
lemma integrableOn_and_integral_gamma_mul_quadratic {H : ℝ} (hH : 0 < H) (k : ℕ) (a b : ℝ) :
    IntegrableOn (fun v : ℝ ↦ v ^ k * rexp (-H * v) * (a + b * (v - (k + 1) / H) ^ 2)) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * (a + b * (v - (k + 1) / H) ^ 2) =
        k ! / H ^ (k + 1) * (a + b * ((k + 1) / H ^ 2)) := by
  let f (j : ℕ) (v : ℝ) : ℝ := v ^ j * rexp (-H * v)
  have h_moment (j : ℕ) : IntegrableOn (f j) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), f j v = j ! / H ^ (j + 1) :=
    integrableOn_and_integral_pow_mul_exp_neg_mul hH j
  have h_expand (v : ℝ) : v ^ k * rexp (-H * v) * (a + b * (v - (k + 1) / H) ^ 2) =
      (a + b * ((k + 1) / H) ^ 2) * f k v - 2 * b * ((k + 1) / H) * f (k + 1) v +
        b * f (k + 2) v := by ring
  have h_int (j : ℕ) (c : ℝ) : IntegrableOn (fun v : ℝ ↦ c * f j v) (Ioi 0) :=
    (h_moment j).left.const_mul c
  simp only [h_expand]
  refine ⟨((h_int k _).sub (h_int (k + 1) _)).add (h_int (k + 2) _), ?_⟩
  rw [integral_add ((h_int k _).sub' (h_int (k + 1) _)) (h_int (k + 2) _),
    integral_sub (h_int k _) (h_int (k + 1) _)]
  simp only [integral_const_mul, (h_moment _).right, Nat.factorial_succ]
  push_cast
  field

variable {R : ℝ → ℝ} {F Φ : ℂ → ℂ} {C L : ℝ}

/-- Let `R` be measurable with `|R v| ≤ C e^v` for `v ≥ 0`, let `Φ s` be its transform
`∫₀^∞ R(v) e^{(1 - s) v} dv` in `re s > 2`, and let `H > 1`. The number
`(-H) ^ k H Φ⁽ᵏ⁾(1 + H) / k!` is the mean of `R` for the Gamma density
`H ^ (k + 1) v ^ k e^{-H v} / k!`, which has mean `(k + 1) / H` and variance `(k + 1) / H²`. So if
`|R v - c| ≤ a + b (v - (k + 1) / H)²` for all `v > 0`, it is within `a + b (k + 1) / H²` of `c`. -/
lemma norm_taylorCoeff_transform_sub_le (hR : Measurable R)
    (R_le : ∀ v : ℝ, 0 ≤ v → |R v| ≤ C * rexp v)
    (Φ_eq : ∀ s : ℂ, 2 < s.re → Φ s = ∫ v in Ioi (0 : ℝ), R v * cexp ((1 - s) * v))
    {H a b c : ℝ} (hH : 1 < H) (k : ℕ)
    (h_near : ∀ v : ℝ, 0 < v → |R v - c| ≤ a + b * (v - (k + 1) / H) ^ 2) :
    ‖(-H) ^ k * H / k ! * iteratedDeriv k Φ (1 + H) - c‖ ≤ a + b * ((k + 1) / H ^ 2) := by
  have hH_pos : 0 < H := one_pos.trans hH
  obtain ⟨moment_int, moment⟩ := integrableOn_and_integral_pow_mul_exp_neg_mul hH_pos k
  obtain ⟨int_major, major_integral⟩ :=
    integrableOn_and_integral_gamma_mul_quadratic hH_pos k a b
  have hH_re : 2 < (1 + H : ℂ).re := by simpa using (by linarith : 2 < 1 + H)
  obtain ⟨h_int, h_deriv⟩ := iteratedDeriv_transform hR R_le Φ_eq k (1 + H) hH_re
  have h_real (v : ℝ) : (-v) ^ k * R v * cexp ((1 - (1 + H)) * v) =
      (-1) ^ k * (v ^ k * rexp (-H * v) * R v : ℝ) := by
    push_cast
    ring_nf
  simp only [h_real] at h_int h_deriv
  rw [IntegrableOn, integrable_const_mul_iff (by simp)] at h_int
  -- The difference is the mean of `R - c`.
  have h_split : ∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * (R v - c) =
      (∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * R v) - k ! / H ^ (k + 1) * c := by
    simp only [mul_sub]
    rw [integral_sub (mod_cast h_int.re) (moment_int.mul_const c), integral_mul_const, moment]
  have h_mean : (-H) ^ k * H / k ! * iteratedDeriv k Φ (1 + H) - c =
      (H ^ (k + 1) / k ! * ∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * (R v - c) : ℝ) := by
    have h_pow : ((-H) ^ k * (-1) ^ k : ℂ) = H ^ k := by simp [← mul_pow]
    have h_sign (z : ℂ) : (-H) ^ k * H / k ! * ((-1) ^ k * z) = H ^ (k + 1) / k ! * z := by
      linear_combination (H / k ! * z) * h_pow
    have h_mass : H ^ (k + 1) / k ! * (k ! / H ^ (k + 1) * c) = c := by field
    rw [h_deriv, integral_const_mul, integral_complex_ofReal, h_sign, h_split, mul_sub, h_mass]
    norm_num
  rw [h_mean, norm_real, norm_mul, Real.norm_of_nonneg (by positivity)]
  calc H ^ (k + 1) / k ! * ‖∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * (R v - c)‖
      ≤ H ^ (k + 1) / k ! *
        ∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * (a + b * (v - (k + 1) / H) ^ 2) := by
        gcongr
        refine norm_integral_le_of_norm_le int_major
          (ae_restrict_of_forall_mem measurableSet_Ioi fun v (hv : 0 < v) ↦ ?_)
        grw [norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, h_near v hv]
    _ = a + b * ((k + 1) / H ^ 2) := by
        rw [major_integral]
        field

/-- If `|R v - R u| ≤ L (v - u)` for all steps `0 ≤ u ≤ v ≤ u + 1`, then `R` is Lipschitz with
constant `L` on `[0, ∞)`. -/
lemma abs_sub_le_of_unit_steps
    (h_step_le : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ u + 1 → |R v - R u| ≤ L * (v - u)) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) : |R v - R u| ≤ L * |v - u| := by
  have hL : 0 ≤ L := by
    simpa using (abs_nonneg _).trans (h_step_le 0 1 le_rfl zero_le_one (by simp))
  have h_lip : LipschitzOnWith (NNReal.mk L hL) R (Ici (0 : ℝ)) := by
    refine (convex_Ici _).lipschitzOnWith_of_locally_dist_le fun x hx ↦ ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x zero_lt_one),
      self_mem_nhdsWithin] with y hy hy0
    simp only [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mk]
    rcases le_total x y with hxy | hyx
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact h_step_le x y hx hxy (by linarith [hy.2])
    · rw [abs_sub_comm (R y), abs_sub_comm y, abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact h_step_le y x hy0 hyx (by linarith [hy.1])
  simpa only [Real.dist_eq, NNReal.coe_mk] using h_lip.dist_le_mul v hv u hu

/-- Let `R` be measurable and Lipschitz with constant `L` on `[0, ∞)`, with transform
`Φ s = ∫₀^∞ R(v) e^{(1 - s) v} dv` in `re s > 2`, and let `u, δ > 0` and `H = (k + 1) / u > 1`. The
number `(-H) ^ k H Φ⁽ᵏ⁾(1 + H) / k!` is within `L (δ + u² / ((k + 1) δ))` of `R(u)`, because the
Gamma density has mean `u` and variance `u² / (k + 1)`. -/
lemma norm_taylorCoeff_transform_sub_le_of_lipschitz (hR : Measurable R)
    (h_lip : ∀ x : ℝ, 0 ≤ x → ∀ y : ℝ, 0 ≤ y → |R y - R x| ≤ L * |y - x|)
    (Φ_eq : ∀ s : ℂ, 2 < s.re → Φ s = ∫ v in Ioi (0 : ℝ), R v * cexp ((1 - s) * v))
    {u δ H : ℝ} {k : ℕ} (hu : 0 < u) (hδ : 0 < δ) (H_eq : H = (k + 1) / u) (hH : 1 < H) :
    ‖(-H) ^ k * H / k ! * iteratedDeriv k Φ (1 + H) - R u‖ ≤ L * (δ + u ^ 2 / (k + 1) / δ) := by
  have hL : 0 ≤ L := by simpa using (abs_nonneg _).trans (h_lip 0 le_rfl 1 zero_le_one)
  have R_le (v : ℝ) (hv : 0 ≤ v) : |R v| ≤ (|R 0| + L) * rexp v := by
    have h_sub : |R v - R 0| ≤ L * v := by simpa [abs_of_nonneg hv] using h_lip 0 le_rfl v hv
    nlinarith [abs_sub_abs_le_abs_sub (R v) (R 0), Real.add_one_le_exp v, abs_nonneg (R 0)]
  have h_near (v : ℝ) (hv : 0 < v) : |R v - R u| ≤ L * δ + L / δ * (v - (k + 1) / H) ^ 2 := by
    have h_amgm : |v - u| ≤ δ + (v - u) ^ 2 / δ := by
      field_simp
      nlinarith only [sq_nonneg (|v - u| - δ), abs_nonneg (v - u), sq_abs (v - u)]
    rw [H_eq, div_div_cancel₀ (by positivity)]
    calc |R v - R u| ≤ L * |v - u| := h_lip u hu.le v hv.le
      _ ≤ L * (δ + (v - u) ^ 2 / δ) := by gcongr
      _ = L * δ + L / δ * (v - u) ^ 2 := by ring
  refine (norm_taylorCoeff_transform_sub_le hR R_le Φ_eq hH k h_near).trans_eq ?_
  rw [H_eq]
  field

/-- **Tauberian theorem.** Let `R` be measurable and Lipschitz on `v ≥ 0` (it suffices to test steps
of length at most `1`), with transform `∫₀^∞ R(v) e^{(1 - s) v} dv = (F s - F 1) / (s - 1)` in
`re s > 2`. Suppose that for all large `l` the function `F` is holomorphic and at most `l ^ A` on
`re s ≥ 1 - l ^ (-A)`, `|s| ≤ e ^ l`. Then `|R(u)| ≤ u ^ (-B)` for every `B` and all large `u`. -/
theorem eventually_abs_le_inv_pow_of_transform (hR : Measurable R)
    (h_lip : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ u + 1 → |R v - R u| ≤ L * (v - u))
    (h_transform : ∀ s : ℂ, 2 < s.re →
      (F s - F 1) / (s - 1) = ∫ v in Ioi (0 : ℝ), R v * cexp ((1 - s) * v)) {A : ℕ}
    (hF : ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ A ≤ s.re → ‖s‖ ≤ rexp l →
      DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ l ^ A) (B : ℕ) :
    ∀ᶠ u : ℝ in atTop, |R u| ≤ 1 / u ^ B := by
  have hL : 0 ≤ L := by simpa using (abs_nonneg _).trans (h_lip 0 1 le_rfl zero_le_one (by simp))
  have Φ_eq (s : ℂ) (hs : 2 < s.re) :
      dslope F 1 s = ∫ v in Ioi (0 : ℝ), R v * cexp ((1 - s) * v) := by
    have hs_ne : s ≠ 1 := fun h ↦ by norm_num [h] at hs
    rw [← h_transform s hs, dslope_of_ne _ hs_ne, slope_def_field]
  -- Compare `R u` with one normalised Taylor coefficient of `dslope F 1` at `1 + H`: the two
  -- differ by `O(u ^ (-(B + 1)))`, and Tau Ceti's rapid-decay estimate makes the coefficient
  -- at most `u ^ (-(B + 1))`.
  filter_upwards [TauCeti.eventually_norm_normalized_iteratedDeriv_dslope_le_inv_pow hF
      (2 * B + 3) (B + 1), eventually_ge_atTop (2 * L + 2)] with u h_small hu_large
  have hu_pos : 0 < u := by linarith
  let k : ℕ := ⌊u ^ (2 * B + 4)⌋₊
  have hk_ge : u ^ (2 * B + 4) ≤ k + 1 := (Nat.lt_floor_add_one _).le
  let H : ℝ := (k + 1) / u
  have hH_gt : 1 < H :=
    (one_lt_div hu_pos).2 ((lt_self_pow₀ (by linarith) (by omega)).trans_le hk_ge)
  let coeff : ℂ := (-H) ^ k * H / k ! * iteratedDeriv k (dslope F 1) (1 + H)
  have h_small' : ‖coeff‖ ≤ 1 / u ^ (B + 1) := by
    simpa only [coeff, k, H, smul_eq_mul, one_div] using h_small
  have h_close : ‖coeff - R u‖ ≤ 2 * L / u ^ (B + 1) :=
    calc ‖coeff - R u‖ ≤ L * (1 / u ^ (B + 1) + u ^ 2 / (k + 1) / (1 / u ^ (B + 1))) :=
          norm_taylorCoeff_transform_sub_le_of_lipschitz hR
            (fun x hx y hy ↦ abs_sub_le_of_unit_steps h_lip hx hy) Φ_eq hu_pos (by positivity)
            rfl hH_gt
      _ ≤ L * (1 / u ^ (B + 1) + u ^ 2 / u ^ (2 * B + 4) / (1 / u ^ (B + 1))) := by gcongr
      _ = 2 * L / u ^ (B + 1) := by field
  calc |R u| = ‖coeff - (coeff - R u)‖ := by simp
    _ ≤ 1 / u ^ (B + 1) + 2 * L / u ^ (B + 1) := norm_sub_le_of_le h_small' h_close
    _ = (1 + 2 * L) / u / u ^ B := by field
    _ ≤ 1 / u ^ B := by grw [(div_le_one hu_pos).2 (by linarith : 1 + 2 * L ≤ u)]

end New
