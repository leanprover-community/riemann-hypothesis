module

import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.LaplaceTransform.Elementary
public import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Lib.General.NumberTheory.ImaginaryQuadraticField
public import TauCeti.Analysis.LaplaceTransform.Basic
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# Quadratic twists, polar functions and logarithmic derivatives of Dirichlet L-functions

This part shows that the twist of a Dirichlet character by the Legendre symbol of an odd prime not
dividing the modulus is not principal. It defines `New.IsPolar`, the condition that a Laplace-type
transform of an error term continues meromorphically with at most simple poles in the right
half-plane. It also expresses `∑ χ(n) Λ(n) n^{-s}` through the logarithmic derivative of
`New.entireL χ` and identifies the residues of that logarithmic derivative with the orders of the
zeros of `New.entireL χ`.

## Main definitions and results

* `New.quadTwist_ne_one`: the twist of a character modulo `N` by the Legendre symbol `(·/d)`, for an
  odd prime `d` prime to `N`, is not principal.
* `New.IsPolar`: `∫₀^∞ E(v) e^{(1-s)v} dv` (the Laplace transform `TauCeti.HasLaplace` of
  `E(v) e^v`) converges for `re s > 2` and continues to a function of `s` meromorphic on `re s > 0`
  with at most simple poles of residue (trailing coefficient) `r ρ` there.
* `New.isPolar_of_tendsto`: `IsPolar` from the limits of `(z - ρ) Φ(z)`.
* `New.LSeriesHasSum_mul_vonMangoldt`: `∑ χ(n) Λ(n) n^{-s}` in terms of the logarithmic derivative
  of `New.entireL χ`.
* `New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt`: the residues of that logarithmic
  derivative are the orders of the zeros of `New.entireL χ`.

Notions from other files:
* `New.entireL`: The entire function equal to L(s, χ) if χ is not principal, and to the continuation
  of (s − 1)L(s, χ) if χ is principal.

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

/-- The transform `∫₀^∞ E(v) e^{(1-s)v} dv`, the Laplace transform of `E(v) e^v`, converges
absolutely for `re s > 2` and continues from there to a function `Φ` meromorphic on `re s > 0`
whose poles there are at most simple (order at least `-1`); for `re ρ > 0`, `r ρ` is the residue at
`ρ`, which is the trailing coefficient at a pole and `0` where there is no pole. For `E(v) = R(e^v)`
the transform is `∫₁^∞ R(y) y^{-s} dy`. -/
def IsPolar (E : ℝ → ℝ) (r : ℂ → ℂ) : Prop :=
  ∃ Φ : ℂ → ℂ, MeromorphicOn Φ {s | 0 < s.re} ∧
    -- (a) `Φ` is the transform of `E` far to the right
    (∀ s : ℂ, 2 < s.re → TauCeti.HasLaplace (fun v ↦ ((E v * Real.exp v : ℝ) : ℂ)) s (Φ s)) ∧
    -- (b) at most simple poles in `re ρ > 0`, with residues `r ρ`
    ∀ ρ : ℂ, 0 < ρ.re → -1 ≤ meromorphicOrderAt Φ ρ ∧
      r ρ = if meromorphicOrderAt Φ ρ < 0 then meromorphicTrailingCoeffAt Φ ρ else 0

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

/-- `IsPolar E r` from the residues, the constructor from the hypotheses that defined `IsPolar`
before it was stated in Tau Ceti's terms: let `E` be measurable with `|E v| ≤ C e^v` for `v ≥ 0`,
and let `Φ`, meromorphic on `re s > 0`, be the transform `∫₀^∞ E(v) e^{(1-s)v} dv` for `re s > 2`.
If `(z - ρ) Φ(z) → r ρ` at every `ρ` with `re ρ > 0`, then `IsPolar E r`. (`TauCeti.HasLaplace`
includes the integrability of the integrand, so in `IsPolar` measurability and the growth bound
are weakened to integrability of `E(v) e^{(1-s)v}` on `(0, ∞)` for `re s > 2`, not dropped.) -/
lemma isPolar_of_tendsto {C : ℝ} {r Φ : ℂ → ℂ} (hE : Measurable E)
    (hE_growth : ∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) (hΦ : MeromorphicOn Φ {s | 0 < s.re})
    (hΦ_eq : ∀ s : ℂ, 2 < re s → Φ s = ∫ v : ℝ in Ioi 0, E v * Complex.exp ((1 - s) * v))
    (hΦ_res : ∀ ρ : ℂ, 0 < re ρ → Tendsto (fun z ↦ (z - ρ) * Φ z) (𝓝[≠] ρ) (𝓝 (r ρ))) :
    IsPolar E r := by
  have h_integrand (s : ℂ) (v : ℝ) :
      Complex.exp (-s * v) • ((E v * Real.exp v : ℝ) : ℂ) = E v * Complex.exp ((1 - s) * v) := by
    push_cast
    rw [smul_eq_mul, show (1 - s) * v = -s * v + v by ring, Complex.exp_add]
    ring
  refine ⟨Φ, hΦ, fun s hs ↦ ?_, fun ρ hρ ↦ ?_⟩
  · simp only [TauCeti.hasLaplace_iff, h_integrand]
    exact ⟨integrableOn_laplace_of_abs_le hE hE_growth hs, (hΦ_eq s hs).symm⟩
  -- Tau Ceti's residue API: the limit bounds the order below by `-1` and is the residue.
  have h_order : -1 ≤ meromorphicOrderAt Φ ρ :=
    TauCeti.Contour.neg_one_le_meromorphicOrderAt_of_tendsto_sub_mul (hΦ_res ρ hρ)
  have h_res := TauCeti.Contour.residue_eq_of_tendsto_sub_mul (hΦ ρ hρ) (hΦ_res ρ hρ)
  refine ⟨h_order, ?_⟩
  rw [← h_res]
  split_ifs with h_neg
  · -- A pole of order at least `-1` is simple, and there the residue is the trailing coefficient.
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h_neg.ne_top
    have h_one : meromorphicOrderAt Φ ρ = (-1 : ℤ) := by
      rw [← hn] at h_neg h_order ⊢
      have h_lt : n < 0 := by exact_mod_cast h_neg
      have h_ge : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.1 h_order
      exact congrArg _ (show n = -1 by omega)
    exact TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one h_one
  · exact TauCeti.Contour.residue_eq_zero_of_meromorphicOrderAt_nonneg (not_lt.1 h_neg)

/-- For `re s > 0`, the Laplace transform of `t ^ k` at `s` is `k! / s ^ (k + 1)`. -/
lemma laplace_pow {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ∫ t : ℝ in Ioi 0, t ^ k * Complex.exp (-s * t) = k ! / s ^ (k + 1) := by
  simpa only [smul_eq_mul, mul_comm] using (TauCeti.hasLaplace_pow k hs).integral_eq

/-! ### The logarithmic derivative of a Dirichlet L-function -/

@[fun_prop]
lemma analyticAt_entireL (s : ℂ) : AnalyticAt ℂ (entireL χ) s := by
  refine Differentiable.analyticAt ?_ s
  rw [entireL]
  split_ifs with hχ
  exacts [differentiable_LFunctionTrivChar₁ N, differentiable_LFunction hχ]

/-- Away from `s = 1`, removing the possible pole preserves nonvanishing. -/
lemma entireL_ne_zero_iff (hs : s ≠ 1) : entireL χ s ≠ 0 ↔ χ.LFunction s ≠ 0 := by
  rw [entireL]
  split_ifs with hχ
  · subst χ
    rw [LFunctionTrivChar₁, Function.update_of_ne hs, mul_ne_zero_iff]
    exact and_iff_right (sub_ne_zero.2 hs)
  · rfl

/-- `entireL χ` has no zero in `re s ≥ 1`. -/
lemma entireL_ne_zero (hs : 1 ≤ s.re) : entireL χ s ≠ 0 := by
  obtain rfl | hs_ne := eq_or_ne s 1
  · rw [entireL]
    split_ifs with hχ
    · exact LFunctionTrivChar₁_apply_one_ne_zero N
    · exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs
  · exact (entireL_ne_zero_iff χ hs_ne).2 (LFunction_ne_zero_of_one_le_re χ (.inr hs_ne) hs)

/-- For `re s > 1`, the series `∑ χ(n) Λ(n) n^{-s}` has the sum `-L'/L(s, χ)`, written through
`entireL χ`, which is `L(s, χ)`, or `(s - 1) L(s, χ)` for principal `χ`. The term `1 / (s - 1)` is
present only for `χ = 1`. -/
lemma LSeriesHasSum_mul_vonMangoldt (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ χ n * Λ n) s
      ((if χ = 1 then 1 else 0) / (s - 1) - logDeriv (entireL χ) s) := by
  refine LSeriesHasSum_iff.2 ⟨χ.LSeriesSummable_twist_vonMangoldt hs, ?_⟩
  -- The series is `-L' / L`; for `χ = 1` the factor `s - 1` of `entireL` adds `1 / (s - 1)` to the
  -- logarithmic derivative.
  have hs_ne : s ≠ 1 := ne_of_apply_ne re hs.ne'
  have h_series : LSeries (fun n : ℕ ↦ χ n * Λ n) s = -deriv χ.LFunction s / χ.LFunction s := by
    rw [χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs]
    exact χ.LSeries_twist_vonMangoldt_eq hs
  have hL_ne : χ.LFunction s ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inr hs_ne) hs.le
  rw [h_series, entireL, logDeriv_apply]
  obtain rfl | hχ := eq_or_ne χ 1
  · rw [ite_eq_left rfl, ite_eq_left rfl, deriv_LFunctionTrivChar₁_apply_of_ne_one N hs_ne,
      LFunctionTrivChar₁, Function.update_of_ne hs_ne, LFunctionTrivChar]
    field [sub_ne_zero.2 hs_ne]
  · simp [hχ, neg_div]

/-- A function continuous at `s` has residue zero there. -/
lemma tendsto_sub_mul_of_continuousAt {f : ℂ → ℂ} (hf : ContinuousAt f s) :
    Tendsto (fun z : ℂ ↦ (z - s) * f z) (𝓝[≠] s) (𝓝 0) := by
  simpa using ((tendsto_id.sub_const s).mul hf).mono_left nhdsWithin_le_nhds

lemma analyticOrderAt_entireL_ne_top (s : ℂ) : analyticOrderAt (entireL χ) s ≠ ⊤ := by
  -- An entire function of infinite order at a point is zero, but `entireL χ 1 ≠ 0`.
  exact fun h_top ↦ entireL_ne_zero χ le_rfl
    (congrFun ((analyticOrderAt_eq_top_iff_eq_zero s (by fun_prop)).1 h_top) 1)

lemma analyticOrderNatAt_entireL_eq_zero_iff (s : ℂ) :
    analyticOrderNatAt (entireL χ) s = 0 ↔ entireL χ s ≠ 0 := by
  rw [← (analyticAt_entireL χ s).analyticOrderAt_eq_zero,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_entireL_ne_top χ s), Nat.cast_eq_zero]

/-- The logarithmic derivative of `entireL χ`, which is `L(s, χ)`, or `(s - 1) L(s, χ)` for
principal `χ`, has at most a simple pole at `s`. Its residue is the order of vanishing of
`entireL χ` at `s`. -/
lemma tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt (s : ℂ) :
    Tendsto (fun z : ℂ ↦ (z - s) * logDeriv (entireL χ) z) (𝓝[≠] s)
      (𝓝 (analyticOrderNatAt (entireL χ) s : ℂ)) := by
  let n := analyticOrderNatAt (entireL χ) s
  have h_ord : meromorphicOrderAt (entireL χ) s = ((n : ℤ) : WithTop ℤ) := by
    rw [(analyticAt_entireL χ s).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (analyticOrderAt_entireL_ne_top χ s)]
    rfl
  have h_meromorphic := (analyticAt_entireL χ s).meromorphicAt
  rw [← Int.cast_natCast,
    ← TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt h_meromorphic h_ord]
  exact TauCeti.Contour.tendsto_sub_mul_nhds_residue h_meromorphic.logDeriv
    (TauCeti.Contour.neg_one_le_meromorphicOrderAt_logDeriv h_meromorphic)

end New
