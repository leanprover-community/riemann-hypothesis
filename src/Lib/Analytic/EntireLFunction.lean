module

import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.Analysis.LaplaceTransform.Elementary
public import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Lib.General.NumberTheory.ImaginaryQuadraticField

/-!
# Quadratic twists, polar functions and entire Dirichlet L-functions

This part shows that the twist of a Dirichlet character by the Legendre symbol of an odd prime not
dividing the modulus is not principal. It defines `New.IsPolar`, the condition that a Laplace-type
transform of an error term continues meromorphically with at most simple poles in the right
half-plane. It also adds two facts about `DirichletCharacter.entireLFunction χ`: away from `1` it
vanishes where `L(s, χ)` does, and its order of vanishing at `s` is zero exactly when it is nonzero
at `s`.

## Main definitions and results

* `New.quadTwist_ne_one`: the twist of a character modulo `N` by the Legendre symbol `(·/d)`, for an
  odd prime `d` prime to `N`, is not principal.
* `New.IsPolar`: `E` is measurable, `|E v| ≤ C e^v` for `v ≥ 0`, and `∫₀^∞ E(v) e^{(1-s)v} dv`
  continues to a meromorphic function of `s` with at most simple poles of residue `r ρ` in
  `re ρ > 0`.
* `New.entireLFunction_ne_zero_iff`: for `s ≠ 1`, `entireLFunction χ s ≠ 0` iff `L(s, χ) ≠ 0`.

Notions from other files:
* `DirichletCharacter.entireLFunction` (Tau Ceti): the entire function equal to L(s, χ) if χ is not
  principal, and to the continuation of (s − 1)L(s, χ) if χ is principal.

## Relation to the literature

Known; see `Lib.Analytic.Landau` for sources.
-/

@[expose] public section

open ArithmeticFunction DirichletCharacter Complex Set Filter MeasureTheory Metric ProbabilityTheory
  Nat Topology ComplexOrder AnalyticOnNhd Real

namespace New

variable {N : ℕ} (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]

/-! ### The quadratic twist of a character -/

/-- The twist of `χ` by the Legendre symbol takes the value `χ(n) (n/d)` at an integer `n`. -/
lemma quadTwist_apply (n : ℤ) : quadTwist χ d n = χ n * legendreSym d n := by
  -- Both sides vanish unless `n` is prime to `N` and to `d`; then the change of level keeps values.
  rw [show (legendreSym d n : ℂ) = (chiK d).ringHomComp (algebraMap ℤ ℂ) n from rfl]
  by_cases h_cop : IsCoprime n (N * d : ℕ)
  · rw [quadTwist, MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ h_cop,
      changeLevel_eq_cast_of_dvd' _ _ h_cop]
  · rw [(apply_eq_zero_iff (quadTwist χ d) n).2 h_cop, zero_eq_mul, apply_eq_zero_iff,
      apply_eq_zero_iff]
    rwa [Nat.cast_mul, IsCoprime.mul_right_iff, not_and_or] at h_cop

/-- For a Dirichlet character `χ` mod `N` and an odd prime `d` coprime to `N`, the twist of `χ` by
the Legendre symbol `(·/d)`, a character mod `N * d`, is not principal. -/
lemma quadTwist_ne_one (hd : d ≠ 2) (hN : N.Coprime d) : quadTwist χ d ≠ 1 := by
  -- Take a non-residue `a` mod `d`, and `n` with `n ≡ 1` mod `N` and `n ≡ a` mod `d`. The twist is
  -- `-1` at `n`, while a value `x` of the trivial character satisfies `x * x = x`.
  intro h_one
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod d) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨n, (hn_N : n ≡ 1 [MOD N]), (hn_d : n ≡ a.val [MOD d])⟩ := chineseRemainder hN 1 a.val
  have hn_one : (n : ZMod N) = 1 := by simpa [← ZMod.natCast_eq_natCast_iff] using hn_N
  have hn_a : (n : ZMod d) = a := by simpa [← ZMod.natCast_eq_natCast_iff] using hn_d
  have h_val : quadTwist χ d n = -1 := by
    simpa [hn_one, legendreSym, hn_a, ha] using quadTwist_apply χ d n
  have h_sq : quadTwist χ d n * quadTwist χ d n = quadTwist χ d n := by
    simp [← MulChar.mul_apply, h_one]
  norm_num [h_val] at h_sq

/-! ### Polar functions and Laplace integrals -/

/-- `E` is measurable, `|E v| ≤ C e^v` for all `v ≥ 0`, and its transform
`∫₀^∞ E(v) e^{(1-s)v} dv` continues from `re s > 2` to a meromorphic function on `ℂ` whose poles in
`re s > 0` are at most simple; for `re ρ > 0`, `r ρ` is the residue at `ρ`, and `0` where there is
no pole. For `E(v) = R(e^v)` the transform is `∫₁^∞ R(y) y^{-s} dy`. -/
def IsPolar (E : ℝ → ℝ) (r : ℂ → ℂ) : Prop :=
  Measurable E ∧
  ∃ (C : ℝ) (Φ : ℂ → ℂ),
    Meromorphic Φ ∧
    -- (a) exponential growth
    (∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) ∧
    -- (b) `Φ` is the transform of `E` far to the right
    (∀ s : ℂ, 2 < re s → Φ s = ∫ v : ℝ in Ioi 0, E v * Complex.exp ((1 - s) * v)) ∧
    -- (c) at most simple poles in `re ρ > 0`, with residues `r ρ`
    ∀ ρ : ℂ, 0 < re ρ → Tendsto (fun z ↦ (z - ρ) * Φ z) (𝓝[≠] ρ) (𝓝 (r ρ))

variable {E : ℝ → ℝ} [NeZero N] {s : ℂ}

/-- If `E` is measurable and `|E v| ≤ C e^v` for `v ≥ 0`, the transform
`∫₀^∞ E(v) e^{(1-s)v} dv` converges for `re s > 2`. -/
lemma integrableOn_laplace_of_abs_le {C : ℝ} (hE : Measurable E)
    (hE_growth : ∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) (hs : 2 < s.re) :
    IntegrableOn (fun v : ℝ ↦ E v * Complex.exp ((1 - s) * v)) (Ioi 0) := by
  -- The integrand is bounded by `C * exp ((2 - re s) * v)`, whose exponent is negative.
  refine ((integrableOn_exp_mul_Ioi (sub_neg.2 hs) 0).const_mul C).mono' (by fun_prop)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun v hv ↦ ?_)
  calc
    ‖E v * cexp ((1 - s) * v)‖ = |E v| * ((1 - s.re) * v).exp := by simp [norm_exp]
    _ ≤ C * v.exp * ((1 - s.re) * v).exp := by grw [hE_growth v hv.le]
    _ = C * ((2 - s.re) * v).exp := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf

/-- For `re s > 0`, the Laplace transform of `t ^ k` at `s` is `k! / s ^ (k + 1)`. -/
lemma laplace_pow {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ∫ t : ℝ in Ioi 0, t ^ k * Complex.exp (-s * t) = k ! / s ^ (k + 1) := by
  simpa only [smul_eq_mul, mul_comm] using (TauCeti.hasLaplace_pow k hs).integral_eq

/-! ### The entire L-function of a Dirichlet character -/

/-- Away from `s = 1`, removing the possible pole preserves nonvanishing. -/
lemma entireLFunction_ne_zero_iff (hs : s ≠ 1) : χ.entireLFunction s ≠ 0 ↔ χ.LFunction s ≠ 0 := by
  obtain rfl | hχ := eq_or_ne χ 1
  · rw [entireLFunction_one_apply hs, mul_ne_zero_iff]
    exact and_iff_right (sub_ne_zero.2 hs)
  · rw [entireLFunction_of_ne_one hχ]

/-- A function continuous at `s` has residue zero there. -/
lemma tendsto_sub_mul_of_continuousAt {f : ℂ → ℂ} (hf : ContinuousAt f s) :
    Tendsto (fun z : ℂ ↦ (z - s) * f z) (𝓝[≠] s) (𝓝 0) := by
  simpa using ((tendsto_id.sub_const s).mul hf).mono_left nhdsWithin_le_nhds

lemma analyticOrderNatAt_entireLFunction_eq_zero_iff (s : ℂ) :
    analyticOrderNatAt χ.entireLFunction s = 0 ↔ χ.entireLFunction s ≠ 0 := by
  rw [← (χ.analyticAt_entireLFunction s).analyticOrderAt_eq_zero,
    ← Nat.cast_analyticOrderNatAt (χ.analyticOrderAt_entireLFunction_ne_top s), Nat.cast_eq_zero]

end New
