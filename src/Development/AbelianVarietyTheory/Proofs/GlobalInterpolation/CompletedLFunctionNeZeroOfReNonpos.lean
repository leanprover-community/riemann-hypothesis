module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.LSeries.Nonvanishing
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

namespace GlobalTheory

theorem inv_Gammaℝ_eq_mul_inv_add_two (s : ℂ) :
    (Gammaℝ s)⁻¹ = s / (2 * Real.pi) * (Gammaℝ (s + 2))⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Gammaℝ_def]
  · have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [Gammaℝ_add_two hs]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    generalize (Gammaℝ s)⁻¹ = g
    field_simp

private lemma deriv_inv_Gammaℝ_eq_shift (x : ℂ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) x =
      1 / (2 * Real.pi) * (Gammaℝ (x + 2))⁻¹ +
        x / (2 * Real.pi) * deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (x + 2) := by
  have hF : (fun s : ℂ => (Gammaℝ s)⁻¹) = fun s => s / (2 * Real.pi) * (Gammaℝ (s + 2))⁻¹ :=
    funext inv_Gammaℝ_eq_mul_inv_add_two
  have h1 : HasDerivAt (fun s : ℂ => s / (2 * (Real.pi : ℂ))) (1 / (2 * Real.pi)) x :=
    (hasDerivAt_id' x).div_const _
  have h2 : HasDerivAt (fun s : ℂ => (Gammaℝ (s + 2))⁻¹)
      (deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (x + 2)) x :=
    HasDerivAt.comp_add_const x 2 (differentiable_Gammaℝ_inv (x + 2)).hasDerivAt
  conv_lhs => rw [hF]
  exact (h1.mul h2).deriv

/-- The derivative of the reciprocal real gamma factor at each of its simple zeros. -/
theorem deriv_inv_Gammaℝ_neg_two_mul_nat (n : ℕ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (-(2 * n)) =
      (-1 : ℂ) ^ n * n.factorial / (2 * (Real.pi : ℂ) ^ n) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  induction n with
  | zero =>
    rw [deriv_inv_Gammaℝ_eq_shift]
    norm_num [Gammaℝ_def, Complex.Gamma_one, Complex.cpow_neg_one, hπ]
    field_simp
  | succ n ih =>
    rw [deriv_inv_Gammaℝ_eq_shift]
    have e : (-(2 * ((n + 1 : ℕ) : ℂ))) + 2 = -(2 * (n : ℂ)) := by push_cast; ring
    rw [e, inv_eq_zero.mpr (Gammaℝ_eq_zero_iff.mpr ⟨n, rfl⟩), mul_zero, zero_add, ih,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, pow_succ]
    field_simp

theorem deriv_inv_Gammaℝ_ne_zero (n : ℕ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (-(2 * n)) ≠ 0 := by
  rw [deriv_inv_Gammaℝ_neg_two_mul_nat]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))
    (mul_ne_zero two_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr Real.pi_ne_zero)))

private theorem deriv_LFunction_eq_of_gamma_shift {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (a : ℂ) (n : ℕ)
    (ha : ∀ w, gammaFactor χ w = Gammaℝ (w + a)) (hn : s + a = -(2 * n))
    (h0 : s ≠ 0 ∨ q ≠ 1) (h1 : s ≠ 1) :
    deriv (LFunction χ) s = completedLFunction χ s *
      ((-1 : ℂ) ^ n * n.factorial / (2 * (Real.pi : ℂ) ^ n)) := by
  have hCd := differentiableAt_completedLFunction χ s h0 (Or.inl h1)
  have hev : LFunction χ =ᶠ[nhds s] fun w => completedLFunction χ w * (Gammaℝ (w + a))⁻¹ := by
    have : ∀ᶠ w in nhds s, w ≠ 0 ∨ q ≠ 1 := by
      rcases h0 with h | h
      · exact (eventually_ne_nhds h).mono fun w hw => Or.inl hw
      · exact Filter.Eventually.of_forall fun _ => Or.inr h
    exact this.mono fun w hw => by
      rw [LFunction_eq_completed_div_gammaFactor χ w hw, div_eq_mul_inv, ha]
  have hh : HasDerivAt (fun w : ℂ => (Gammaℝ (w + a))⁻¹)
      (deriv (fun w : ℂ => (Gammaℝ w)⁻¹) (s + a)) s :=
    HasDerivAt.comp_add_const s a (differentiable_Gammaℝ_inv (s + a)).hasDerivAt
  have hG : Gammaℝ (s + a) = 0 := Gammaℝ_eq_zero_iff.mpr ⟨n, hn⟩
  rw [hev.deriv_eq, (hCd.hasDerivAt.fun_mul hh).deriv, inv_eq_zero.mpr hG,
    mul_zero, zero_add, hn, deriv_inv_Gammaℝ_neg_two_mul_nat]

/-- The derivative at an even character's trivial zero, including the origin when the
modulus is not one. Primitivity is not required. -/
theorem deriv_LFunction_even_neg_two_mul_nat {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.Even) (n : ℕ) (h0 : n ≠ 0 ∨ q ≠ 1) :
    deriv (LFunction χ) (-(2 * n)) = completedLFunction χ (-(2 * n)) *
      ((-1 : ℂ) ^ n * n.factorial / (2 * (Real.pi : ℂ) ^ n)) := by
  apply deriv_LFunction_eq_of_gamma_shift χ 0 n
  · intro w
    simpa using hχ.gammaFactor_def w
  · simp
  · exact h0.imp (fun hn => neg_ne_zero.mpr (mul_ne_zero two_ne_zero
      (Nat.cast_ne_zero.mpr hn))) id
  · intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- The derivative at an odd character's trivial zero. Primitivity is not required. -/
theorem deriv_LFunction_odd_neg_two_mul_nat_sub_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.Odd) (n : ℕ) :
    deriv (LFunction χ) (-(2 * n) - 1) = completedLFunction χ (-(2 * n) - 1) *
      ((-1 : ℂ) ^ n * n.factorial / (2 * (Real.pi : ℂ) ^ n)) := by
  apply deriv_LFunction_eq_of_gamma_shift χ 1 n
  · exact hχ.gammaFactor_def
  · ring
  · left
    intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

private theorem Gammaℝ_two_mul_nat_add_one (n : ℕ) :
    Gammaℝ (2 * n + 1) = (2 * n).factorial /
      ((4 : ℂ) ^ n * n.factorial * (Real.pi : ℂ) ^ n) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hs : (2 * (n : ℂ) + 1) ≠ 0 := by
      have h : (0 : ℝ) < 2 * n + 1 := by positivity
      exact_mod_cast h.ne'
    rw [show (2 * ((n + 1 : ℕ) : ℂ) + 1) = (2 * (n : ℂ) + 1) + 2 by push_cast; ring,
      Gammaℝ_add_two hs, ih]
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, pow_succ, pow_succ]
    push_cast
    field_simp
    ring

/-- The derivatives at the negative even zeros are positive-odd zeta values with the
standard factorial and power-of-pi factor. The origin is excluded. -/
theorem deriv_riemannZeta_neg_two_mul_nat (n : ℕ) (hn : n ≠ 0) :
    deriv riemannZeta (-(2 * n)) =
      ((-1 : ℂ) ^ n * (2 * n).factorial / (2 * (2 * (Real.pi : ℂ)) ^ (2 * n))) *
        riemannZeta (2 * n + 1) := by
  have h := deriv_LFunction_even_neg_two_mul_nat
    (χ := (1 : DirichletCharacter ℂ 1)) even_one n (.inl hn)
  rw [LFunction_modOne_eq, completedLFunction_modOne_eq] at h
  rw [h]
  have hFE : completedRiemannZeta (-(2 * n)) = completedRiemannZeta (2 * n + 1) := by
    have h := completedRiemannZeta_one_sub (2 * n + 1)
    rw [show (1 : ℂ) - (2 * n + 1) = -(2 * n) by ring] at h
    exact h
  have hs : (2 * (n : ℂ) + 1) ≠ 0 := by
    have h : (0 : ℝ) < 2 * n + 1 := by positivity
    exact_mod_cast h.ne'
  rw [hFE, riemannZeta_def_of_ne_zero hs, Gammaℝ_two_mul_nat_add_one]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2nfac : ((2 * n).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * n))
  rw [mul_pow, pow_mul, show (2 : ℂ) ^ 2 = 4 by norm_num, pow_mul]
  field_simp
  ring

theorem rootNumber_ne_zero_of_isPrimitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : rootNumber χ ≠ 0 := by
  have hG : gaussSum χ ZMod.stdAddChar ≠ 0 := by
    intro h
    have h1 : ZMod.dft (χ : ZMod q → ℂ) = 0 := by
      funext k
      rw [hχ.fourierTransform_eq_inv_mul_gaussSum k, h, mul_zero]
      rfl
    have h2 := congr_fun (ZMod.dft_dft (χ : ZMod q → ℂ)) (-1)
    rw [h1, _root_.map_zero] at h2
    simp only [Pi.zero_apply, neg_neg, map_one, smul_eq_mul, mul_one] at h2
    exact NeZero.ne q (by exact_mod_cast h2.symm)
  unfold rootNumber
  refine div_ne_zero (div_ne_zero hG (pow_ne_zero _ I_ne_zero)) ?_
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => NeZero.ne q (Nat.cast_eq_zero.mp h.1)

theorem completedLFunction_ne_zero_of_re_nonpos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {s : ℂ} (hs : s.re ≤ 0) (h0 : s ≠ 0 ∨ χ ≠ 1) :
    completedLFunction χ s ≠ 0 := by
  have hFE := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hFE
  rw [hFE]
  have hw : 1 ≤ (1 - s).re := by rw [sub_re, one_re]; linarith
  refine mul_ne_zero (mul_ne_zero ?_ (rootNumber_ne_zero_of_isPrimitive hχ)) ?_
  · rw [Ne, cpow_eq_zero_iff]
    exact fun h => NeZero.ne q (Nat.cast_eq_zero.mp h.1)
  · intro hC
    have hne : χ⁻¹ ≠ 1 ∨ 1 - s ≠ 1 := by
      rcases h0 with h | h
      · exact Or.inr (by intro h'; apply h; linear_combination -h')
      · exact Or.inl (inv_ne_one.mpr h)
    apply LFunction_ne_zero_of_one_le_re χ⁻¹ hne hw
    have h1s : 1 - s ≠ 0 := by
      intro h'; rw [h'] at hw; norm_num at hw
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h1s), hC, zero_div]

theorem LFunction_zero_of_re_nonpos : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ s : ℂ, s.re ≤ 0 → LFunction χ s = 0 → (∃ n : ℕ, s = -n) ∧ analyticOrderNatAt (LFunction χ) s = 1 ∧ (s = 0 → χ.Even ∧ χ ≠ 1) ∧ (s = -1 → χ.Odd) := by
  intro q _ χ hχ s hs hL
  obtain ⟨hgamma, h0⟩ := (DirichletCharacter.LFunction_eq_zero_iff_of_re_nonpos hχ hs).mp hL
  have h0' : s ≠ 0 ∨ q ≠ 1 := h0.symm
  have h0 : s ≠ 0 ∨ χ ≠ 1 := h0'.imp id fun hq htriv => by
    apply hq
    rw [htriv, IsPrimitive, conductor_one] at hχ
    exact hχ.symm
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hC : completedLFunction χ s ≠ 0 := completedLFunction_ne_zero_of_re_nonpos hχ hs h0
  have hCd : DifferentiableAt ℂ (completedLFunction χ) s :=
    differentiableAt_completedLFunction χ s h0' (Or.inl hs1)
  obtain ⟨a, ha, hpar⟩ : ∃ a : ℕ, (∀ w, gammaFactor χ w = Gammaℝ (w + a)) ∧
      (a = 0 ∧ χ.Even ∨ a = 1 ∧ χ.Odd) := by
    rcases χ.even_or_odd with h | h
    · exact ⟨0, fun w => by simp [h.gammaFactor_def], Or.inl ⟨rfl, h⟩⟩
    · exact ⟨1, fun w => by simp [h.gammaFactor_def], Or.inr ⟨rfl, h⟩⟩
  have hev : LFunction χ =ᶠ[nhds s] fun w => completedLFunction χ w * (Gammaℝ (w + a))⁻¹ := by
    have : ∀ᶠ w in nhds s, w ≠ 0 ∨ q ≠ 1 := by
      rcases h0' with h | h
      · exact (eventually_ne_nhds h).mono fun w hw => Or.inl hw
      · exact Filter.Eventually.of_forall fun _ => Or.inr h
    exact this.mono fun w hw => by
      rw [LFunction_eq_completed_div_gammaFactor χ w hw, div_eq_mul_inv, ha]
  have hG : Gammaℝ (s + a) = 0 := by rwa [ha] at hgamma
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hG
  have hh : HasDerivAt (fun w : ℂ => (Gammaℝ (w + a))⁻¹)
      (deriv (fun w : ℂ => (Gammaℝ w)⁻¹) (s + a)) s :=
    HasDerivAt.comp_add_const s (a : ℂ) (differentiable_Gammaℝ_inv (s + a)).hasDerivAt
  have hder : deriv (LFunction χ) s ≠ 0 := by
    rw [hev.deriv_eq, (hCd.hasDerivAt.fun_mul hh).deriv, inv_eq_zero.mpr hG, mul_zero, zero_add]
    refine mul_ne_zero hC ?_
    rw [hn]
    exact deriv_inv_Gammaℝ_ne_zero n
  have hAn : AnalyticAt ℂ (LFunction χ) s :=
    analyticAt_iff_eventually_differentiableAt.mpr
      ((eventually_ne_nhds hs1).mono fun w hw => differentiableAt_LFunction χ w (Or.inl hw))
  have hord : analyticOrderAt (LFunction χ) s = 1 :=
    hAn.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hL hder
  have hs_eq : s = -((2 * n + a : ℕ) : ℂ) := by push_cast; linear_combination hn
  refine ⟨⟨2 * n + a, hs_eq⟩, by simp [analyticOrderNatAt, hord], fun h => ?_, fun h => ?_⟩
  · rw [h] at hs_eq
    have hk : ((2 * n + a : ℕ) : ℂ) = 0 := by linear_combination hs_eq
    have hk' : 2 * n + a = 0 := by exact_mod_cast hk
    refine ⟨?_, h0.resolve_left (not_not.mpr h)⟩
    rcases hpar with ⟨_, he⟩ | ⟨ha1, _⟩
    · exact he
    · omega
  · rw [h] at hs_eq
    have hk : ((2 * n + a : ℕ) : ℂ) = 1 := by linear_combination hs_eq
    have hk' : 2 * n + a = 1 := by exact_mod_cast hk
    rcases hpar with ⟨ha0, _⟩ | ⟨_, ho⟩
    · omega
    · exact ho


open Filter Topology

private lemma eulerFactor_ne_zero_of_re_neg {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : s.re < 0) :
    1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  by_cases hu : IsUnit (p : ZMod M)
  · have hn : ‖χ (p : ZMod M)‖ = 1 := by simpa using χ.unit_norm_eq_one hu.unit
    have hlt : 1 < ‖χ p * (p : ℂ) ^ (-s)‖ := by
      rw [norm_mul, hn, one_mul, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
      exact Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hlt
    exact lt_irrefl _ hlt
  · simp [χ.map_nonunit hu]

private lemma zeros_eq_primitiveCharacter_of_re_neg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re < 0) :
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    (LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0) ∧
      analyticOrderNatAt (LFunction χ) s = analyticOrderNatAt (LFunction χ.primitiveCharacter) s := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  let E : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors,
    (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z))
  have hEn : E s ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      eulerFactor_ne_zero_of_re_neg χ.primitiveCharacter (Nat.prime_of_mem_primeFactors hp) hs
  have hEa : AnalyticAt ℂ E s := by
    apply Differentiable.analyticAt
    change Differentiable ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors,
      (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z)))
    intro z
    apply DifferentiableAt.fun_finsetProd
    intro p hp
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    fun_prop (disch := exact Or.inl hp0)
  have hLa : AnalyticAt ℂ (LFunction χ.primitiveCharacter) s :=
    DifferentiableOn.analyticAt (s := {z | z ≠ 1})
      (fun z hz => (differentiableAt_LFunction _ z (.inl hz)).differentiableWithinAt)
      (isOpen_ne.mem_nhds hs1)
  have hev : LFunction χ =ᶠ[𝓝 s] LFunction χ.primitiveCharacter * E := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (.inr hz)
    simpa [changeLevel_primitiveCharacter, E] using h
  constructor
  · rw [hev.eq_of_nhds, Pi.mul_apply, mul_eq_zero]
    simp [hEn]
  · unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hLa hEa,
      analyticOrderAt_eq_zero.mpr (.inr hEn), add_zero]

/-- In the open left half-plane, the zeros of any Dirichlet L-function are exactly
those of its Gamma factor. Primitivity is not needed away from the boundary. -/
theorem LFunction_eq_zero_iff_of_re_neg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s.re < 0) : LFunction χ s = 0 ↔ gammaFactor χ s = 0 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hparity : χ.primitiveCharacter.Even ↔ χ.Even := by
    change χ.primitiveCharacter (-1) = 1 ↔ χ (-1) = 1
    have h := χ.primitiveCharacter_apply_of_isCoprime (a := -1) ⟨-1, 0, by ring⟩
    simp only [Int.cast_neg, Int.cast_one] at h
    rw [h]
  rw [(zeros_eq_primitiveCharacter_of_re_neg χ hs).1,
    DirichletCharacter.LFunction_eq_zero_iff_of_re_nonpos χ.primitiveCharacter_isPrimitive hs.le]
  have hg : gammaFactor χ.primitiveCharacter s = gammaFactor χ s := by
    unfold gammaFactor
    rw [hparity]
  rw [hg]
  simp [hs0]

/-- Strictly to the left of the imaginary axis, all Dirichlet L-function zeros
are simple and at negative integers, even for imprimitive characters. -/
theorem LFunction_zero_of_re_neg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s.re < 0) (hzero : LFunction χ s = 0) :
    (∃ n : ℕ, s = -n) ∧ analyticOrderNatAt (LFunction χ) s = 1 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨hz, ho⟩ := zeros_eq_primitiveCharacter_of_re_neg χ hs
  obtain ⟨hi, hm, _⟩ := LFunction_zero_of_re_nonpos χ.conductor χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive s hs.le (hz.mp hzero)
  exact ⟨hi, ho.trans hm⟩

/-- No Dirichlet L-function vanishes on the contour line `re(s) = -1/2`. -/
theorem LFunction_ne_zero_of_re_eq_neg_half {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = -(1 / 2)) : LFunction χ s ≠ 0 := by
  intro hz
  obtain ⟨⟨n, hn⟩, _⟩ := LFunction_zero_of_re_neg χ (by linarith) hz
  have h := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at h
  have hn0 : (n : ℝ) = 0 ∨ 1 ≤ (n : ℝ) := by exact_mod_cast Nat.eq_zero_or_pos n
  rcases hn0 with hn0 | hn0 <;> linarith

end GlobalTheory
