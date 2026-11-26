module

public import Mathlib.NumberTheory.Padics.Complex
public import Lib.CM.Sigma.Basic
import Lib.CM.Sigma.ThetaSections
import Lib.General.Algebra.AdicCompletion

/-!
# Doubling formulas for θ and σ and the quartic forms of doubling

The file expresses `θ(2 z)` and `σ(2 z) ^ 2` in `θ(z)` and `σ(z)`. The quartic forms of doubling,
`doublingForms c`, are defined over any commutative ring; over `ℂ` with `c = a₁`, their values at
`(θ², σ²)` are the square of the formula for `θ(2 z)` and the formula for `σ(2 z) ^ 2`. These facts
serve to prove that doubling raises the naive height to the fourth power; see
`Lib.CM.Integrality.TorsionValues`.

Notions from other files:
* `C : CMLattice d`: a lattice `Λ = C.Λ` in `ℂ` with a point `t = C.t` of order two modulo `Λ`,
  scaled so that `℘''(t) = 2`, and a square root `a₁ = C.a₁` of `12 ℘(t)`.
* `C.σ`, `C.θ`: the sigma function of `Λ`, and its twisted translate by `t` normalised to `1` at
  `0`; the zeros of `θ` are the `z` with `z + t ∈ Λ`.
* `C.translatedX`: the function `x(z) = ℘(z + t) - ℘(t)`, equal to `σ² / θ²` off `t + Λ`.
* `C.twistedTranslate m y`: the translation `T_y` by `y`, twisted by the exponential factor of
  degree `m`.

## Main definitions and results

* `New.doublingForms c`: the pair of quartic forms of doubling.
* `New.CMLattice.sigma_two_mul_eq`: `σ(2 z) = x' θ ^ 4` off `t + Λ`.
* `New.CMLattice.theta_two_mul`, `New.CMLattice.sigma_two_mul_sq`: `θ(2 z)` and `σ(2 z) ^ 2` as
  polynomials in `θ` and `σ`.
* `New.norm_doublingForms`: if `c` is integral and `c ^ 4 - 64` is a unit, the forms raise the
  maximum norm of a pair to the fourth power.

## Relation to the literature

Known result: the duplication formulas for theta and sigma functions. Source: DLMF, Chapters 20 and
23.

Known result: good reduction of the duplication map on the `x`-coordinate of an elliptic curve.
Source: Silverman, *The Arithmetic of Dynamical Systems* (GTM 241, Springer, 2007), Chapters 2 and
6.
-/

@[expose] public section

/-!
## Doubling formulas for θ and σ

The formula `θ(2 z) = θ ^ 4 - σ ^ 4` is the addition formula for `θ` on the diagonal. The formula
`σ(2 z) = x' θ ^ 4` is the duplication formula of `σ` at `z + t`; it uses that the number
`c₀ = (T_t σ)(0)` is a fourth root of unity.
-/

section Doubling

open Complex ComplexConjugate PeriodPair

namespace New.CMLattice
variable {d : ℕ} (C : CMLattice d)

/-- For a CM lattice with point `t` of order two, the number `c₀ = (T_t σ)(0)` is nonzero. -/
lemma twistedTranslate_t_sigma_zero_ne_zero : C.twistedTranslate 1 C.t C.σ 0 ≠ 0 := by
  simp [thetaShift_apply, C.t_notMem]

/-- The identity `T_t σ = c₀ θ` with `c₀ = (T_t σ)(0)`, with the exponential factor of the twisted
translation `T_t` written out. -/
lemma sigma_add_t (z : ℂ) :
    C.σ (z + C.t) = exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2) *
      (C.twistedTranslate 1 C.t C.σ 0 * C.θ z) := by
  rw [θ, mul_div_cancel₀ _ C.twistedTranslate_t_sigma_zero_ne_zero, twistedTranslate,
    thetaShift_apply_apply, one_smul, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/-- The identity `c₀ T_t θ = -σ` with `c₀ = (T_t σ)(0)`, with the exponential factor of the twisted
translation `T_t` written out. -/
lemma theta_add_t (z : ℂ) :
    C.twistedTranslate 1 C.t C.σ 0 * C.θ (z + C.t) =
      -exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2) * C.σ z := by
  have h_exponent : -(C.hermitianForm C.t (z + C.t) + C.hermitianForm C.t C.t / 2) +
      (2 * C.hermitianForm C.t z + 2 * C.hermitianForm C.t C.t) =
      C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2 := by
    simp only [map_add]
    ring
  rw [θ, mul_div_cancel₀ _ C.twistedTranslate_t_sigma_zero_ne_zero, twistedTranslate,
    thetaShift_apply_apply, one_smul, add_assoc z, C.sigma_add_two_t, ← h_exponent]
  simp only [exp_add]
  ring

/-- For a CM lattice `C` with point `t` of order two, the number `c₀ = (T_t σ)(0)` is a fourth root
of unity: `c₀ ^ 4 = 1`. Here `T_t` is the twisted translation of degree `1` by `t`, so
`c₀ = exp(−π |t|² / (2A)) σ(t)`, where `A` is the area of `Λ`. -/
lemma twistedTranslate_t_sigma_zero_pow_four : C.twistedTranslate 1 C.t C.σ 0 ^ 4 = 1 := by
  -- Translation by `t` turns `x θ² = σ²` into `x(z + t) σ² = c₀ ^ 4 θ²`, so that
  -- `c₀ ^ 4 = x(z) x(z + t) = 1`. We take `z = t / 2`.
  set c₀ : ℂ := C.twistedTranslate 1 C.t C.σ 0
  let z : ℂ := C.t / 2
  have hz : z ∉ C.Λ := fun h ↦ C.t_notMem (by simpa only [z, add_halves] using add_mem h h)
  have hzt : z + C.t ∉ C.Λ := fun h ↦ C.t_notMem <| by
    have ht : C.t = z + C.t + (z + C.t) - (C.t + C.t) := by
      simp only [z]
      ring
    rw [ht]
    exact sub_mem (add_mem h h) C.two_t_mem
  have hztt : z + C.t + C.t ∉ C.Λ := by rwa [add_assoc, add_mem_cancel_right C.two_t_mem]
  set e : ℂ := exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2)
  have h_translate : C.translatedX (z + C.t) * C.σ z ^ 2 = c₀ ^ 4 * C.θ z ^ 2 := by
    have h_sq : C.σ (z + C.t) ^ 2 = C.translatedX (z + C.t) * C.θ (z + C.t) ^ 2 :=
      C.sigma_sq_eq_translatedX_mul_theta_sq hztt
    have hσ : C.σ (z + C.t) = e * (c₀ * C.θ z) := C.sigma_add_t z
    have hθ : c₀ * C.θ (z + C.t) = -e * C.σ z := C.theta_add_t z
    refine mul_left_cancel₀ (pow_ne_zero 2 (exp_ne_zero _ : e ≠ 0)) ?_
    calc e ^ 2 * (C.translatedX (z + C.t) * C.σ z ^ 2)
        = C.translatedX (z + C.t) * (-e * C.σ z) ^ 2 := by ring
      _ = c₀ ^ 2 * (C.translatedX (z + C.t) * C.θ (z + C.t) ^ 2) := by
        rw [← hθ]
        ring
      _ = e ^ 2 * (c₀ ^ 4 * C.θ z ^ 2) := by
        rw [← h_sq, hσ]
        ring
  have hθ_ne : C.θ z ≠ 0 := mt C.theta_eq_zero_iff.1 hzt
  refine mul_right_cancel₀ (pow_ne_zero 2 hθ_ne) ?_
  calc c₀ ^ 4 * C.θ z ^ 2 = C.translatedX z * C.translatedX (z + C.t) * C.θ z ^ 2 := by
        rw [← h_translate, C.sigma_sq_eq_translatedX_mul_theta_sq hzt]
        ring
    _ = 1 * C.θ z ^ 2 := by rw [C.translatedX_mul_translatedX_add_t hz hzt]

/-- Doubling for the normalised twisted translate `θ` of the sigma function `σ` of `C`:
`θ(2 z) = θ(z) ^ 4 - σ(z) ^ 4`. -/
lemma theta_two_mul (z : ℂ) : C.θ (2 * z) = C.θ z ^ 4 - C.σ z ^ 4 := by
  -- Both sides are entire. Off `t + Λ` this is the addition formula for `θ` at `(z, z)`, with
  -- `x θ² = σ²`.
  revert z
  refine C.eq_of_eq_off_lattice C.t (by fun_prop) (by fun_prop) fun z hz ↦ ?_
  have h_add : C.θ (z + z) * C.θ (z - z) =
      C.θ z ^ 2 * (C.θ z ^ 2 - C.translatedX z * C.σ z ^ 2) :=
    C.theta_add_mul_theta_sub hz z
  have hσ : C.σ z ^ 2 = C.translatedX z * C.θ z ^ 2 := C.sigma_sq_eq_translatedX_mul_theta_sq hz
  rw [sub_self, theta_zero, mul_one, ← two_mul] at h_add
  linear_combination h_add + C.σ z ^ 2 * hσ

/-- Doubling for the sigma function `σ` of `C`: `σ(2 z) = x'(z) θ(z) ^ 4` away from the poles
`t + Λ` of `x(z) = ℘(z + t) - ℘(t)`, where `θ` is the normalised twisted translate of `σ` by `t`. -/
lemma sigma_two_mul_eq {z : ℂ} (hz : z + C.t ∉ C.Λ) :
    C.σ (2 * z) = deriv C.translatedX z * C.θ z ^ 4 := by
  -- This is the duplication formula `σ(2 w) = -℘'(w) σ(w) ^ 4` at `w = z + t`. The exponential
  -- factors cancel, the period `2 t` gives a sign, and `c₀ ^ 4 = 1` for `c₀ = (T_t σ)(0)`.
  set e : ℂ := exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2)
  have h_period : C.σ (2 * (z + C.t)) = -e ^ 4 * C.σ (2 * z) := by
    have h_exponent : 2 * C.hermitianForm C.t (2 * z) + 2 * C.hermitianForm C.t C.t =
        (4 : ℕ) * (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2) := by
      rw [two_mul z, map_add]
      push_cast
      ring
    rw [mul_add, two_mul C.t, C.sigma_add_two_t, h_exponent, exp_natCast_mul]
  have h_fourth : C.σ (z + C.t) ^ 4 = e ^ 4 * C.θ z ^ 4 := by
    rw [C.sigma_add_t, mul_pow, mul_pow, C.twistedTranslate_t_sigma_zero_pow_four, one_mul]
  have h_deriv : deriv C.translatedX z = ℘'[C.periodPair] (z + C.t) := by
    rw [deriv_translatedX, translatedY]
    ring
  have h_double : C.σ (2 * (z + C.t)) = -℘'[C.periodPair] (z + C.t) * C.σ (z + C.t) ^ 4 :=
    sigma_two_mul C.periodPair hz
  rw [h_period, h_fourth, ← h_deriv] at h_double
  refine mul_left_cancel₀ (pow_ne_zero 4 (exp_ne_zero _ : e ≠ 0)) ?_
  linear_combination -h_double

/-- Doubling for the sigma function `σ` of `C`, in terms of `σ` and its normalised twisted translate
`θ` by `t`: `σ(2 z)² = θ² σ² (4 θ ^ 4 + a₁² θ² σ² + 4 σ ^ 4)` at `z`. -/
lemma sigma_two_mul_sq (z : ℂ) :
    C.σ (2 * z) ^ 2 = C.θ z ^ 2 * C.σ z ^ 2 *
      (4 * C.θ z ^ 4 + C.a₁ ^ 2 * C.θ z ^ 2 * C.σ z ^ 2 + 4 * C.σ z ^ 4) := by
  -- Both sides are entire, so it suffices to compare them off `t + Λ`.
  revert z
  refine C.eq_of_eq_off_lattice C.t (by fun_prop) (by fun_prop) fun z hz ↦ ?_
  have hσ : C.σ z ^ 2 = C.translatedX z * C.θ z ^ 2 := C.sigma_sq_eq_translatedX_mul_theta_sq hz
  rw [C.sigma_two_mul_eq hz, mul_pow, C.deriv_translatedX_sq hz, hσ, pow_mul (C.σ z) 2 2, hσ]
  ring

end New.CMLattice

end Doubling

/-!
## The quartic forms of doubling over ℂ_p

If `c` is integral and `c ^ 4 - 64` is a unit, the two forms are not both of norm less than `1` at
a pair of norm `1`: combinations of `w₀² - w₁²` and the second form with integral coefficients are
`(c ^ 4 - 64) w₀ ^ 5` and `(c ^ 4 - 64) w₁ ^ 5`.
-/

section DoublingForms

namespace New

section Forms
variable {R : Type*} [CommRing R]

/-- The pair of quartic forms `B₀ = (w₀² - w₁²)²` and `B₁ = w₀ w₁ (4 w₀² + c² w₀ w₁ + 4 w₁²)` at
`w = (w₀, w₁)`. -/
def doublingForms (c : R) (w : R × R) : R × R :=
  ((w.1 ^ 2 - w.2 ^ 2) ^ 2, w.1 * w.2 * (4 * w.1 ^ 2 + c ^ 2 * w.1 * w.2 + 4 * w.2 ^ 2))

/-- The forms `doublingForms c` are homogeneous of degree `4`. -/
lemma doublingForms_smul (c a : R) (w : R × R) :
    doublingForms c (a • w) = a ^ 4 • doublingForms c w := by
  ext <;> simp only [doublingForms, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

end Forms

variable {p : ℕ} [Fact p.Prime]

/-- If `c ∈ ℂ_p` is integral and `c ^ 4 - 64` is a unit, the quartic forms `doublingForms c` take
pairs of maximum norm `1` to pairs of maximum norm `1`. -/
lemma norm_doublingForms_eq_one {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) (h_disc : ‖c ^ 4 - 64‖ = 1)
    {w : ℂ_[p] × ℂ_[p]} (hw : ‖w‖ = 1) : ‖doublingForms c w‖ = 1 := by
  have hc_mem : c ∈ valRingCp p := hc
  -- If `u`, `v` are integral and `u² - v²` and the second form at `(u, v)` have norm less than
  -- `1`, so has `u`: a combination of the two with integral coefficients is `(c ^ 4 - 64) u ^ 5`.
  have h_small {u v : ℂ_[p]} (hu : u ∈ valRingCp p) (hv : v ∈ valRingCp p)
      (h₀ : ‖u ^ 2 - v ^ 2‖ < 1)
      (h₁ : ‖u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2)‖ < 1) : ‖u‖ < 1 := by
    let x : ℂ_[p] := c ^ 2 * u - 8 * v
    let y : ℂ_[p] := (x * (c ^ 2 * u + 4 * v) - 64 * u ^ 2) * u
    have hcu : c ^ 2 * u ∈ valRingCp p := mul_mem (pow_mem hc_mem 2) hu
    have hx : x ∈ valRingCp p := sub_mem hcu (mul_mem (ofNat_mem _ 8) hv)
    have hy : y ∈ valRingCp p :=
      mul_mem (sub_mem (mul_mem hx (add_mem hcu (mul_mem (ofNat_mem _ 4) hv)))
        (mul_mem (ofNat_mem _ 64) (pow_mem hu 2))) hu
    have h_eq : (c ^ 4 - 64) * u ^ 5 =
        x * (u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2)) + y * (u ^ 2 - v ^ 2) := by
      simp only [x, y]
      ring
    have h_lt : ‖(c ^ 4 - 64) * u ^ 5‖ < 1 := by
      rw [h_eq]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · exact (norm_mul _ _).trans_lt ((mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt h₁)
      · exact (norm_mul _ _).trans_lt ((mul_le_of_le_one_left (norm_nonneg _) hy).trans_lt h₀)
    rw [norm_mul, h_disc, one_mul, norm_pow] at h_lt
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg u) (by norm_num)).1 h_lt
  obtain ⟨u, v⟩ := w
  have hu : u ∈ valRingCp p := (norm_fst_le (u, v)).trans hw.le
  have hv : v ∈ valRingCp p := (norm_snd_le (u, v)).trans hw.le
  refine le_antisymm (max_le ?_ ?_) (not_lt.1 fun h_lt ↦ ?_)
  · exact pow_mem (sub_mem (pow_mem hu 2) (pow_mem hv 2)) 2
  · exact mul_mem (mul_mem hu hv) (add_mem (add_mem (mul_mem (ofNat_mem _ 4) (pow_mem hu 2))
      (mul_mem (mul_mem (pow_mem hc_mem 2) hu) hv)) (mul_mem (ofNat_mem _ 4) (pow_mem hv 2)))
  -- Otherwise both coordinates of the pair have norm less than `1`.
  · obtain ⟨h₀, h₁⟩ : ‖(u ^ 2 - v ^ 2) ^ 2‖ < 1 ∧
        ‖u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2)‖ < 1 := max_lt_iff.1 h_lt
    rw [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h₀
    have hu_lt : ‖u‖ < 1 := h_small hu hv h₀ h₁
    have hv_lt : ‖v‖ < 1 := h_small hv hu (by rwa [norm_sub_rev]) (by
      rwa [show v * u * (4 * v ^ 2 + c ^ 2 * v * u + 4 * u ^ 2) =
        u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2) by ring])
    exact (max_lt hu_lt hv_lt).ne hw

/-- If `c ∈ ℂ_p` is integral and `c ^ 4 - 64` is a unit, the quartic forms `doublingForms c` raise
the maximum norm of a pair to the fourth power. -/
lemma norm_doublingForms {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) (h_disc : ‖c ^ 4 - 64‖ = 1)
    (w : ℂ_[p] × ℂ_[p]) : ‖doublingForms c w‖ = ‖w‖ ^ 4 := by
  -- By homogeneity, divide by the coordinate of larger norm.
  obtain ⟨a, ha⟩ : ∃ a : ℂ_[p], ‖w‖ = ‖a‖ :=
    (max_choice ‖w.1‖ ‖w.2‖).elim (fun h ↦ ⟨w.1, h⟩) (fun h ↦ ⟨w.2, h⟩)
  obtain rfl | ha_ne := eq_or_ne a 0
  · obtain rfl : w = 0 := by simpa using ha
    simp [doublingForms]
  · have h_unit : ‖a⁻¹ • w‖ = 1 := by simp [norm_smul, ha, ha_ne]
    calc ‖doublingForms c w‖ = ‖doublingForms c (a • a⁻¹ • w)‖ := by rw [smul_inv_smul₀ ha_ne]
      _ = ‖a‖ ^ 4 * ‖doublingForms c (a⁻¹ • w)‖ := by rw [doublingForms_smul, norm_smul, norm_pow]
      _ = ‖w‖ ^ 4 := by rw [norm_doublingForms_eq_one hc h_disc h_unit, mul_one, ha]

end New

end DoublingForms
