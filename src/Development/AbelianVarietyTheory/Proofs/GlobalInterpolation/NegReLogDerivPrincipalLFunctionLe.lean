module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivRiemannZetaLocalZeroSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

open Filter Topology
open scoped Classical

namespace GlobalTheory

private lemma analyticAt_eulerFactor (a : ℂ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => 1 - a * (p : ℂ) ^ (-z)) s := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact (show Differentiable ℂ (fun z : ℂ => 1 - a * (p : ℂ) ^ (-z)) by
    fun_prop (disch := exact Or.inl hp0)).analyticAt s

/-- At the origin an Euler factor is a simple zero exactly when its coefficient is one. -/
theorem analyticOrderAt_eulerFactor_zero (a : ℂ) {p : ℕ} (hp : p.Prime) :
    analyticOrderAt (fun z : ℂ => 1 - a * (p : ℂ) ^ (-z)) 0 = if a = 1 then 1 else 0 := by
  split_ifs with ha
  · subst a
    apply (analyticAt_eulerFactor 1 hp 0).analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp)
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hd : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) (Complex.log p) 0 := by
      simpa only [Pi.neg_apply, neg_zero, cpow_zero, one_mul, mul_neg_one, neg_neg] using
        (((hasDerivAt_id' (0 : ℂ)).neg).const_cpow (Or.inl hp0)).const_sub 1
    simp only [one_mul]
    rw [hd.deriv, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p)]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))
  · exact analyticOrderAt_eq_zero.mpr (.inr (by simpa using sub_ne_zero.mpr (Ne.symm ha)))

private lemma analyticOrderAt_eulerProduct_zero (a : ℕ → ℂ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    analyticOrderAt (fun z : ℂ => ∏ p ∈ S, (1 - a p * (p : ℂ) ^ (-z))) 0 =
      (S.filter fun p => a p = 1).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hp' := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have heq : (fun z : ℂ => ∏ r ∈ insert p S, (1 - a r * (r : ℂ) ^ (-z))) =
        (fun z : ℂ => 1 - a p * (p : ℂ) ^ (-z)) *
          (fun z : ℂ => ∏ r ∈ S, (1 - a r * (r : ℂ) ^ (-z))) := by
      funext z
      rw [Finset.prod_insert hp]
      rfl
    rw [heq, analyticOrderAt_mul (analyticAt_eulerFactor (a p) hp' 0)
      (S.analyticAt_fun_prod fun p hp => analyticAt_eulerFactor (a p) (hS' p hp) 0),
      analyticOrderAt_eulerFactor_zero _ hp', ih hS']
    by_cases ha : a p = 1
    · simp [ha, Finset.filter_insert, Finset.mem_filter, hp, add_comm]
    · simp [ha, Finset.filter_insert]

/-- Changing the level adds one to the origin's vanishing order for each removed
Euler factor with character value one. This also covers imprimitive characters. -/
theorem analyticOrderAt_LFunction_changeLevel_zero {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) :
    analyticOrderAt (LFunction (changeLevel hMN χ)) 0 =
      analyticOrderAt (LFunction χ) 0 + (N.primeFactors.filter fun (p : ℕ) => χ (p : ZMod M) = 1).card := by
  have ha : AnalyticAt ℂ (LFunction χ) 0 :=
    (DifferentiableOn.analyticOnNhd (fun z (hz : z ∈ ({1} : Set ℂ)ᶜ) =>
      (differentiableAt_LFunction _ z (.inl hz)).differentiableWithinAt)
      isOpen_compl_singleton) 0 (by simp)
  have hp : AnalyticAt ℂ (fun z : ℂ => ∏ p ∈ N.primeFactors,
      (1 - χ p * (p : ℂ) ^ (-z))) 0 :=
    N.primeFactors.analyticAt_fun_prod fun p hp =>
      analyticAt_eulerFactor (χ p) (Nat.prime_of_mem_primeFactors hp) 0
  have heq : LFunction (changeLevel hMN χ) =ᶠ[𝓝 (0 : ℂ)]
      LFunction χ * (fun z : ℂ => ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z))) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)] with z hz
    exact LFunction_changeLevel hMN χ (.inr hz)
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul ha hp,
    analyticOrderAt_eulerProduct_zero _ _ (fun p hp => Nat.prime_of_mem_primeFactors hp)]

end GlobalTheory

namespace GlobalTheory.PrincipalLogDeriv

lemma norm_cpow_neg_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2

lemma half_le_norm_one_sub {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
  have h := norm_cpow_neg_le hp hs
  have h' := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
  rw [norm_one] at h'
  linarith

lemma one_sub_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h' := half_le_norm_one_sub hp hs
  rw [h, norm_zero] at h'
  norm_num at h'

lemma hasDerivAt_factor {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p) s := by
  have hc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
    ((hasDerivAt_id' s).neg).const_cpow (Or.inl hc)
  have h2 : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      (-((p : ℂ) ^ (-s) * Complex.log p * (-1))) s := h.const_sub 1
  convert h2 using 1
  ring

/-- Every removed principal Euler factor has a simple zero at the origin. -/
lemma analyticOrderAt_factor_zero {p : ℕ} (hp : p.Prime) :
    analyticOrderAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) 0 = 1 := by
  simpa using GlobalTheory.analyticOrderAt_eulerFactor_zero 1 hp

/-- The principal L-function has vanishing order equal to the number of distinct
prime factors of its modulus, including order zero at modulus one. -/
theorem analyticOrderAt_LFunction_one_zero (q : ℕ) [NeZero q] :
    analyticOrderAt (LFunction (1 : DirichletCharacter ℂ q)) 0 = q.primeFactors.card := by
  have h := GlobalTheory.analyticOrderAt_LFunction_changeLevel_zero (Nat.one_dvd q)
    (1 : DirichletCharacter ℂ 1)
  have hz : analyticOrderAt riemannZeta 0 = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (by rw [riemannZeta_zero]; norm_num))
  simpa [changeLevel_one, LFunction_modOne_eq, hz, MulChar.one_apply (isUnit_of_subsingleton _)] using h

theorem analyticOrderNatAt_LFunction_one_zero (q : ℕ) [NeZero q] :
    analyticOrderNatAt (LFunction (1 : DirichletCharacter ℂ q)) 0 = q.primeFactors.card := by
  simp [analyticOrderNatAt, analyticOrderAt_LFunction_one_zero]

lemma norm_logDeriv_factor_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have h1 := norm_cpow_neg_le hp hs
  have h2 := half_le_norm_one_sub hp hs
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real,
      Real.norm_of_nonneg hl]
  rw [logDeriv_apply, (hasDerivAt_factor hp s).deriv, norm_div, norm_mul, hlog,
    div_le_iff₀ (by linarith)]
  nlinarith

lemma sum_log_primeFactors_le (q : ℕ) [NeZero q] :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  · have h := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
    rw [← Nat.cast_prod]
    exact_mod_cast h

lemma norm_logDeriv_sub_le (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
      - deriv riemannZeta s / riemannZeta s‖ ≤ Real.log q := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hre : 1 ≤ s.re := hs.le
  have hev : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[nhds s]
      fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    exact LFunctionTrivChar_eq_mul_riemannZeta hz
  have hfac : ∀ p ∈ q.primeFactors, (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ≠ 0 :=
    fun p hp => one_sub_ne_zero (Nat.prime_of_mem_primeFactors hp) hre
  have hdfac : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    fun p hp => (hasDerivAt_factor (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  have hF0 : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  have hFd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s :=
    DifferentiableAt.fun_finsetProd hdfac
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hL : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s =
      logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s := by
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hL, logDeriv_fun_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s hF0 hζ0
    hFd hζd, ← logDeriv_apply riemannZeta, add_sub_cancel_right,
    logDeriv_fun_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) hfac hdfac]
  calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
      ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p :=
        Finset.sum_le_sum fun p hp => norm_logDeriv_factor_le (Nat.prime_of_mem_primeFactors hp) hre
    _ ≤ Real.log q := sum_log_primeFactors_le q

theorem neg_re_logDeriv_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC, hZ⟩ := _root_.GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local
  refine ⟨C + 1, by linarith, ?_⟩
  intro q _ σ t hσ1 hσ2
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hsne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs1
    exact lt_irrefl _ hs1
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hdist : ‖s - (3 / 2 + t * I)‖ ≤ 2 / 3 := by
    have h1 : s - (3 / 2 + t * I) = ((σ - 3 / 2 : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  obtain ⟨hfin, hbound⟩ := hZ t s hdist hsne hζ0
  set Z := {w : ℂ | ‖w - (3 / 2 + t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0} with hZdef
  set S := ∑ᶠ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w) with hSdef
  have hterm : ∀ w ∈ Z, 0 ≤ ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re := by
    intro w hw
    have hw1 : w.re ≤ 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_lt_re h hw.2.2
    have hpos : 0 ≤ (s - w).re := by rw [Complex.sub_re, hsre]; linarith
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hpos) (Complex.normSq_nonneg _)
  have hS : 0 ≤ S.re := by
    rw [hSdef, finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    exact Finset.sum_nonneg fun w hw => hterm w (hfin.mem_toFinset.mp hw)
  set E := deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - S with hEdef
  have hζ : deriv riemannZeta s / riemannZeta s = E - 1 / (s - 1) + S := by
    rw [hEdef]; ring
  have hE : -E.re ≤ C * Real.log (|t| + 2) :=
    le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm E) hbound)
  set D := deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
    - deriv riemannZeta s / riemannZeta s with hDdef
  have hD : ‖D‖ ≤ Real.log q := norm_logDeriv_sub_le q hs1
  have hDre : -D.re ≤ Real.log q := le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm D) hD)
  have hLsplit : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s = D + (E - 1 / (s - 1) + S) := by
    rw [hDdef, ← hζ]; ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hlt : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
  have hlog : Real.log (q * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith) (by linarith)
  rw [hLsplit, hlog]
  simp only [Complex.add_re, Complex.sub_re]
  nlinarith

/-- The logarithmic derivative of a removed Euler factor at one. -/
lemma logDeriv_factor_one {p : ℕ} (hp : p.Prime) :
    logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) 1 = Complex.log p / (p - 1) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [logDeriv_apply, (hasDerivAt_factor hp 1).deriv, cpow_neg_one]
  field_simp

private lemma LFunctionTrivChar₁_eq_eulerProduct (q : ℕ) [NeZero q] :
    LFunctionTrivChar₁ q = fun s =>
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta₁ s := by
  funext s
  by_cases hs : s = 1
  · simp [hs, LFunctionTrivChar₁, cpow_neg_one]
  · rw [LFunctionTrivChar₁, Function.update_of_ne hs,
      LFunctionTrivChar_eq_mul_riemannZeta hs, riemannZeta_eq_inv_sub_mul hs]
    field_simp

/-- The regularized principal logarithmic derivative at one is Euler's constant
plus the logarithmic derivatives of the finitely many removed Euler factors. -/
theorem logDeriv_LFunctionTrivChar₁_one (q : ℕ) [NeZero q] :
    logDeriv (LFunctionTrivChar₁ q) 1 = (Real.eulerMascheroniConstant : ℂ) +
      ∑ p ∈ q.primeFactors, Complex.log p / (p - 1) := by
  let E : ℂ → ℂ := fun s => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))
  have hd : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) 1 :=
    fun p hp => (hasDerivAt_factor (Nat.prime_of_mem_primeFactors hp) 1).differentiableAt
  have hn : ∀ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) ≠ 0 :=
    fun p hp => one_sub_ne_zero (Nat.prime_of_mem_primeFactors hp) (by simp)
  rw [LFunctionTrivChar₁_eq_eulerProduct]
  rw [logDeriv_fun_mul (f := E) (g := riemannZeta₁) 1
    (Finset.prod_ne_zero_iff.mpr hn) (by simp)
    (DifferentiableAt.fun_finsetProd hd) differentiable_riemannZeta₁.differentiableAt]
  change logDeriv (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) 1 + _ = _
  rw [logDeriv_fun_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) hn hd]
  simp only [logDeriv_apply riemannZeta₁, deriv_riemannZeta₁_one, riemannZeta₁_one, div_one]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun p hp => logDeriv_factor_one (Nat.prime_of_mem_primeFactors hp)

/-- The constant term of the principal logarithmic derivative at its pole. -/
theorem logDeriv_LFunction_one_near_one (q : ℕ) [NeZero q] :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧
      g 1 = (Real.eulerMascheroniConstant : ℂ) +
        ∑ p ∈ q.primeFactors, Complex.log p / (p - 1) ∧
      ∀ᶠ s in nhdsWithin (1 : ℂ) {1}ᶜ,
        deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
          LFunction (1 : DirichletCharacter ℂ q) s = -1 / (s - 1) + g s := by
  have ha := (differentiable_LFunctionTrivChar₁ q).analyticAt 1
  have hn := LFunctionTrivChar₁_apply_one_ne_zero q
  refine ⟨logDeriv (LFunctionTrivChar₁ q), ha.deriv.div ha hn,
    logDeriv_LFunctionTrivChar₁_one q, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (ha.continuousAt.eventually_ne hn),
    self_mem_nhdsWithin] with s hs hs1
  have hL : LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := by
    rw [LFunctionTrivChar₁, Function.update_of_ne hs1] at hs
    exact (mul_ne_zero_iff.mp hs).2
  rw [logDeriv_apply, deriv_LFunctionTrivChar₁_apply_of_ne_one q hs1,
    LFunctionTrivChar₁, Function.update_of_ne hs1]
  field_simp [sub_ne_zero.mpr hs1]
  <;> ring

end GlobalTheory.PrincipalLogDeriv
