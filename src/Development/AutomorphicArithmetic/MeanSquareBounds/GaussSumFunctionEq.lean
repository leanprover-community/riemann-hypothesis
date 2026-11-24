module

public import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
public import Formalism.PeriodIntegrals.ExplicitFormula
public import Formalism.GL3MeanSquares.HookFormulaTorsion.PsiZeroIntegral
public import Formalism.GL3MeanSquares.HookFormulaTorsion.SmoothedRemainderRealIntegralFormula
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Gamma
public import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Formalism.LandauZeroFreeBounds.NoZeroComplex
public import Formalism.PeriodIntegrals.ZerosWindow
public import Development.AutomorphicArithmetic.CharacterBoxes.PairGood
public import Development.AutomorphicArithmetic.MeanSquareBounds.realCond
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
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.NumberTheory.Harmonic.Bounds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedExplicitFormula

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros, Development.AutomorphicArithmetic.MeanSquareBounds.GIntegral, Development.AutomorphicArithmetic.MeanSquareBounds.IntThin, Development.AutomorphicArithmetic.MeanSquareBounds.PsiThin, Development.AutomorphicArithmetic.MeanSquareBounds.Thin, Development.AutomorphicArithmetic.MeanSquareBounds.GaussSumFunctionEq

-- ===== clump member: Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros", "h": "module\n\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\npublic import Mathlib.NumberTheory.LSeries.Nonvanishing\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.MulChar.Duality\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff\n\n"}
section -- clump:auto
@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem noExc_mono {c c' : ℝ} (h : c' ≤ c) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hc : NoExc c χ) : NoExc c' χ :=
  fun β h1 h2 => hc β (by linarith) h2

private theorem noExc_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ c : ℝ, 0 < c ∧ (χ ≠ 1 → NoExc c χ) := by
  by_cases hχ : χ = 1
  · exact ⟨1, one_pos, fun h => absurd hχ h⟩
  have hcont : Continuous (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal
  have h1 : (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) 1 ≠ 0 := by
    simpa using DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hev := hcont.continuousAt.eventually_ne h1
  obtain ⟨c, hc, h⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨c, hc, fun _ β hb1 hb2 => h ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private theorem noExc_level (N : ℕ) [NeZero N] :
    ∃ c : ℝ, 0 < c ∧ ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → NoExc c χ := by
  classical
  choose c hc h using fun χ : DirichletCharacter ℂ N => noExc_one χ
  obtain ⟨χ₀, hχ₀⟩ := Finite.exists_min c
  exact ⟨c χ₀, hc χ₀, fun χ hχ => noExc_mono (hχ₀ χ) (h χ hχ)⟩

theorem small_zeros :
    ∀ N₀ : ℕ, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), N ≤ N₀ → χ ≠ 1 → NoExc c₀ χ := by
  intro N₀
  induction N₀ with
  | zero =>
    exact ⟨1, one_pos, fun N _ χ hN _ => absurd (Nat.le_zero.1 hN) (NeZero.ne N)⟩
  | succ n ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨c', hc', h'⟩ := noExc_level (n + 1)
    refine ⟨min c c', lt_min hc hc', fun N _ χ hN hχ => ?_⟩
    rcases Nat.lt_or_eq_of_le hN with hlt | heq
    · exact noExc_mono (min_le_left _ _) (h N χ (Nat.lt_succ_iff.1 hlt) hχ)
    · subst heq
      exact noExc_mono (min_le_right _ _) (h' χ hχ)

end QH
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros =====

-- ===== clump member: Development.AutomorphicArithmetic.MeanSquareBounds.GIntegral =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.MeanSquareBounds.GIntegral", "h": "module\n\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds\npublic import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula\npublic import Formalism.PeriodIntegrals.ExplicitFormula\npublic import Formalism.GL3MeanSquares.HookFormulaTorsion.PsiZeroIntegral\npublic import Formalism.GL3MeanSquares.HookFormulaTorsion.SmoothedRemainderRealIntegralFormula\nimport Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.MeasureTheory.Function.Floor\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff\n\n"}
section -- clump:auto
@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

section

open Filter Topology ArithmeticFunction MeasureTheory

private noncomputable def dom (t : ℝ) : ℝ := 1 / (t * Real.log t ^ 2)

private lemma dom_integrableOn {a : ℝ} (ha : 1 < a) : IntegrableOn dom (Set.Ioi a) := by
  have key : ∀ x ∈ Set.Ioi a, HasDerivAt (fun t => -(Real.log t)⁻¹) (dom x) x := by
    intro x hx
    have hx1 : 1 < x := lt_trans ha hx
    have hx0 : 0 < x := by linarith
    have hl : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    have h : HasDerivAt (fun t => -(Real.log t)⁻¹) (-(-x⁻¹ / Real.log x ^ 2)) x :=
      ((Real.hasDerivAt_log hx0.ne').inv hl).neg
    refine h.congr_deriv ?_
    show _ = 1 / (x * Real.log x ^ 2)
    field_simp
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun t => -(Real.log t)⁻¹) (l := 0) ?_ key ?_ ?_
  · exact (((Real.continuousAt_log (by linarith)).inv₀ (Real.log_pos ha).ne').neg).continuousWithinAt
  · intro x hx
    have hx1 : 1 < x := lt_trans ha hx
    have : 0 < Real.log x := Real.log_pos hx1
    show 0 ≤ 1 / (x * Real.log x ^ 2)
    positivity
  · have := Real.tendsto_log_atTop.inv_tendsto_atTop.neg
    simpa using this

private lemma exp_sqrt_le {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / c ^ 4 / Real.log x ^ 2 := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hs : 0 < c * Real.sqrt (Real.log x) := mul_pos hc (Real.sqrt_pos.mpr hL)
  have h4 : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    rw [mul_pow]
    congr 1
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hL.le]
  have hexp := Real.pow_div_factorial_le_exp _ hs.le 4
  rw [h4] at hexp
  have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at hexp
  rw [neg_mul, Real.exp_neg, div_div, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  exact hexp

private noncomputable def aChi {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)

private lemma psi0_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ K x₁ : ℝ, 1 < x₁ ∧ ∀ t : ℝ, x₁ ≤ t → ‖PI.psi0 χ t‖ ≤ K * t / Real.log t ^ 2 := by
  obtain ⟨c, C, hc, hSW⟩ := Formalism.ZeroFreeDirichlet.siegelWalfisz 1 one_pos
  refine ⟨C * (24 / c ^ 4), max 2 (Real.exp N), lt_of_lt_of_le one_lt_two (le_max_left _ _), ?_⟩
  intro t ht
  have h2 : 2 ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  have hq : (N : ℝ) ≤ Real.log t ^ (1:ℝ) := by
    rw [Real.rpow_one]
    have he := le_trans (le_max_right _ _) ht
    calc (N:ℝ) = Real.log (Real.exp N) := (Real.log_exp _).symm
      _ ≤ Real.log t := Real.log_le_log (Real.exp_pos _) he
  have hb : ‖PI.psi0 χ t‖ ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
    have hb0 := hSW N χ t h2 hq
    by_cases hc : χ = 1
    · simpa [PI.psi0, Formalism.ZeroFreeDirichlet.psiChi, hc] using hb0
    · simpa [PI.psi0, Formalism.ZeroFreeDirichlet.psiChi, hc] using hb0
  have he := exp_sqrt_le hc (x := t) (by linarith)
  have hC : 0 ≤ C := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg ht0) (Real.exp_pos (-c * Real.sqrt (Real.log t)))
    linarith [norm_nonneg (PI.psi0 χ t)]
  calc _ ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)) := hb
    _ ≤ C * t * (24 / c ^ 4 / Real.log t ^ 2) := mul_le_mul_of_nonneg_left he (mul_nonneg hC ht0.le)
    _ = C * (24 / c ^ 4) * t / Real.log t ^ 2 := by ring

private lemma psi_zero_div_sq_integrable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => PI.psi0 χ u / (u : ℂ) ^ 2) (Set.Ioi y) := by
  obtain ⟨K, x₁, hx₁, hK⟩ := psi0_bound χ
  have hX1 : 1 < max x₁ y := lt_of_lt_of_le hx₁ (le_max_left _ _)
  have h1 : Measurable (fun u : ℝ => ∑ n ∈ Icc 1 ⌊u⌋₊, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) :=
    (measurable_from_nat (f := fun m : ℕ => ∑ n ∈ Icc 1 m, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N))).comp
      Nat.measurable_floor
  have hm : Measurable (PI.psi0 χ) := by
    by_cases hc : χ = 1
    · have e : PI.psi0 χ = fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) - (u : ℂ) := by
        funext u
        simp [PI.psi0, hc]
      rw [e]
      exact h1.sub Complex.measurable_ofReal
    · have e : PI.psi0 χ = fun u : ℝ => ∑ n ∈ Icc 1 ⌊u⌋₊, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N) := by
        funext u
        simp [PI.psi0, hc]
      rw [e]
      exact h1
  have hmeas : Measurable (fun u : ℝ => PI.psi0 χ u / (u : ℂ) ^ 2) :=
    hm.div (Complex.measurable_ofReal.pow_const 2)
  have hsplit : Set.Ioi y ⊆ Set.Ioc y (max x₁ y) ∪ Set.Ioi (max x₁ y) := by
    intro u hu
    by_cases h : u ≤ max x₁ y
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr (lt_of_not_ge h)
  refine IntegrableOn.mono_set ?_ hsplit
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := (∑ n ∈ Icc 1 ⌊max x₁ y⌋₊, vonMangoldt n) + max x₁ y)
      (by simp [Real.volume_Ioc]) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu1 : 1 ≤ u := le_trans hy hu.1.le
    have hsum : ‖∑ n ∈ Icc 1 ⌊u⌋₊, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)‖ ≤
        ∑ n ∈ Icc 1 ⌊max x₁ y⌋₊, vonMangoldt n := by
      calc _ ≤ ∑ n ∈ Icc 1 ⌊u⌋₊, ‖((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Icc 1 ⌊u⌋₊, vonMangoldt n := by
          apply Finset.sum_le_sum
          intro n _
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
          exact mul_le_of_le_one_right vonMangoldt_nonneg (χ.norm_le_one _)
        _ ≤ ∑ n ∈ Icc 1 ⌊max x₁ y⌋₊, vonMangoldt n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc_right (Nat.floor_le_floor hu.2)
          · intros
            exact vonMangoldt_nonneg
    have hden : 1 ≤ ‖(u:ℂ)^2‖ := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      nlinarith
    rw [norm_div]
    calc ‖PI.psi0 χ u‖ / ‖(u:ℂ)^2‖ ≤ ‖PI.psi0 χ u‖ := div_le_self (norm_nonneg _) hden
      _ ≤ _ := by
        unfold PI.psi0
        refine (norm_sub_le _ _).trans (add_le_add hsum ?_)
        split_ifs with hc
        · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
          exact hu.2
        · rw [norm_zero]
          linarith [le_max_right x₁ y]
  · have hdom := (dom_integrableOn hX1).const_mul K
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu' : x₁ ≤ u := le_trans (le_max_left _ _) (le_of_lt hu)
    have hu1 : 1 < u := lt_of_lt_of_le hx₁ hu'
    have hu0 : 0 < u := by linarith
    have hlog : Real.log u ≠ 0 := (Real.log_pos hu1).ne'
    have hb := hK u hu'
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    calc ‖PI.psi0 χ u‖ / u ^ 2 ≤ (K * u / Real.log u ^ 2) / u ^ 2 :=
          div_le_div_of_nonneg_right hb (by positivity)
      _ = K * dom u := by
          show _ = K * (1 / (u * Real.log u ^ 2))
          field_simp

private lemma gChi_ne {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) (y : ℝ) :
    G0 χ y = Formalism.HermitianLattices.GL2PrimeSums.Gchi (aChi χ) (-(logDerivLAtOne χ)) y := by
  unfold G0
  rw [if_neg h]
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.Gchi Formalism.HermitianLattices.GL2PrimeSums.Gchi aChi
  ring

private lemma gChi_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ = 1) (y : ℝ) :
    G0 χ y = ((Formalism.HermitianLattices.GL2PrimeSums.Gone (fun n => vonMangoldt n) y : ℝ) : ℂ) := by
  unfold G0
  rw [if_pos h]
  rfl

private lemma series_aChi {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) :
    Tendsto (fun M : ℕ => ∑ n ∈ Icc 1 M, aChi χ n / (n : ℂ)) atTop (𝓝 (-(logDerivLAtOne χ))) :=
  Formalism.HermitianLattices.GL2a2.log_deriv_series N χ h

private lemma one_apply_of_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (h : χ = 1)
    (n : ℕ) : χ (n : ZMod N) = 1 := by
  subst h
  have hN : N = 1 := by
    have := hp
    unfold DirichletCharacter.IsPrimitive at this
    rw [DirichletCharacter.conductor_one] at this
    exact this.symm
  subst hN
  exact MulChar.one_apply (isUnit_of_subsingleton _)
private theorem l21a {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) (y : ℝ) (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => PI.psi0 χ u / (u : ℂ) ^ 2) (Set.Ioi y) ∧
      G0 χ y = -(y : ℂ) * ∫ u in Set.Ioi y, PI.psi0 χ u / (u : ℂ) ^ 2 := by
  have hint := psi_zero_div_sq_integrable χ y hy
  refine ⟨hint, ?_⟩
  have hlim : Tendsto (fun U => ∫ u in y..U, PI.psi0 χ u / (u:ℂ)^2) atTop
      (𝓝 (∫ u in Set.Ioi y, PI.psi0 χ u / (u:ℂ)^2)) :=
    intervalIntegral_tendsto_integral_Ioi y hint tendsto_id
  by_cases h : χ = 1
  · obtain ⟨I, hI, hG⟩ := Formalism.HermitianLattices.GL2PrimeSums.smoothedRemainderRealIntegralFormula (fun n => vonMangoldt n)
      Formalism.HermitianLattices.GL2a2.psi_zero_integral_constant y hy
    have hone := one_apply_of_primitive hp h
    have hfun : (fun u : ℝ => PI.psi0 χ u / (u:ℂ)^2) =
        fun u => (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => vonMangoldt n) u - u) / u ^ 2 : ℝ) : ℂ) := by
      funext u
      simp only [PI.psi0, if_pos h, hone, mul_one, Formalism.HermitianLattices.GL2PrimeSums.psumR]
      push_cast
      ring
    have hlim2 : Tendsto (fun U => ∫ u in y..U, PI.psi0 χ u / (u:ℂ)^2) atTop (𝓝 (I : ℂ)) := by
      rw [hfun]
      simp_rw [intervalIntegral.integral_ofReal]
      exact (Complex.continuous_ofReal.tendsto _).comp hI
    rw [tendsto_nhds_unique hlim hlim2, gChi_one h, hG]
    push_cast
    ring
  · obtain ⟨I, hI, hG⟩ := Formalism.HermitianLattices.GL2PrimeSums.smoothedRemainderIntegralFormula (aChi χ) (-(logDerivLAtOne χ)) (series_aChi h) y hy
    have hfun : (fun u : ℝ => Formalism.HermitianLattices.GL2PrimeSums.psum (aChi χ) u / (u:ℂ)^2) =
        fun u => PI.psi0 χ u / (u:ℂ)^2 := by
      funext u
      simp [Formalism.HermitianLattices.GL2PrimeSums.psum, PI.psi0, aChi, h]
    rw [hfun] at hI
    rw [tendsto_nhds_unique hlim hI, gChi_ne h, hG]
end

theorem g_integral :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ y : ℝ, 1 ≤ y →
      G0 χ y = -(y : ℂ) * ∫ u in Set.Ioi y, PI.psi0 χ u / (u : ℂ) ^ 2 := by
  intro N _ χ hp y hy
  exact (l21a χ hp y hy).2

end QH
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.MeanSquareBounds.GIntegral =====

-- ===== clump member: Development.AutomorphicArithmetic.MeanSquareBounds.IntThin =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.MeanSquareBounds.IntThin", "h": "module\n\npublic import Mathlib.MeasureTheory.Integral.Bochner.Basic\npublic import Mathlib.MeasureTheory.Measure.Haar.OfBasis\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.CStarAlgebra.Classes\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.MeasureTheory.Integral.Gamma\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff\nimport Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis\npublic import Mathlib.Analysis.Calculus.Deriv.Basic\npublic import Mathlib.Analysis.SpecialFunctions.ExpDeriv\npublic import Mathlib.Analysis.SpecialFunctions.Gamma.Basic\n\n"}
section -- clump:auto
@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private lemma thin_intH (b : ℝ) (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-b * v ^ (39 / 100 : ℝ)))
      (Set.Ioi 0) := by
  apply MeasureTheory.Integrable.of_integral_ne_zero
  rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb]
  have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < (2 + 1) / (39 / 100))
  positivity

private lemma thin_ptw (c v lam : ℝ) (hc : 0 < c) (hv : 1 ≤ v) (hl0 : 0 < lam)
    (hl : lam ≤ v ^ (61 / 100 : ℝ)) :
    (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := by
  have hv0 : 0 < v := by linarith
  have hb1 : v ^ (61 / 100 : ℝ) ≤ v := by
    have := Real.rpow_le_rpow_of_exponent_le hv (by norm_num : (61 / 100 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  have hs : Real.sqrt v ≤ v ^ (61 / 100 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
  have hprod : v ^ (39 / 100 : ℝ) * v ^ (61 / 100 : ℝ) = v := by
    rw [← Real.rpow_add hv0]; norm_num
  have hsq : (v + lam) ^ 2 ≤ 4 * v ^ (2 : ℝ) := by
    rw [Real.rpow_two]; nlinarith
  have hs0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hg0 : 0 < v ^ (39 / 100 : ℝ) := by positivity
  have hexp : Real.exp (-c * v / (lam + Real.sqrt v)) ≤ Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hden : 0 < lam + Real.sqrt v := by linarith
    have key : c / 2 * v ^ (39 / 100 : ℝ) ≤ c * v / (lam + Real.sqrt v) := by
      rw [le_div_iff₀ hden]
      calc c / 2 * v ^ (39 / 100 : ℝ) * (lam + Real.sqrt v)
          ≤ c / 2 * v ^ (39 / 100 : ℝ) * (2 * v ^ (61 / 100 : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = c * (v ^ (39 / 100 : ℝ) * v ^ (61 / 100 : ℝ)) := by ring
        _ = c * v := by rw [hprod]
    have e1 : -c * v / (lam + Real.sqrt v) = -(c * v / (lam + Real.sqrt v)) := by ring
    rw [e1]; linarith
  calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
      ≤ (4 * v ^ (2 : ℝ)) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) :=
        mul_le_mul hsq hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

private lemma thin_integral (ε c B : ℝ) (hε : 0 < ε) (hc : 0 < c) (hB : 0 < B) :
    ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ V lam : ℝ, x ^ (ε / 3) / 2 ≤ V → 1 ≤ lam →
    lam ≤ B * x ^ (ε / 5) * Real.log x ^ 2 →
    MeasureTheory.IntegrableOn
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) ∧
    (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤
      Real.exp (-c' * x ^ (13 * ε / 100)) := by
  set H : ℝ → ℝ := fun v => v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) with hH
  have hHint : MeasureTheory.IntegrableOn H (Set.Ioi 0) := thin_intH (c / 4) (by positivity)
  set K : ℝ := ∫ v in Set.Ioi (0 : ℝ), H v with hK
  have E1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have E2 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (ε / 3) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 2
  have E3 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ 1 / (2 * B + 1) * ‖x ^ (ε / 600)‖ :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < ε / 600)).bound (by positivity)
  have E4 : ∀ᶠ x : ℝ in Filter.atTop, 4 * K ≤ Real.exp (c / 16 * x ^ (13 * ε / 100)) :=
    (Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by positivity : 0 < 13 * ε / 100)).const_mul_atTop
      (by positivity : 0 < c / 16))).eventually_ge_atTop (4 * K)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (E1.and (E2.and (E3.and E4)))
  refine ⟨c / 16, x₀, by positivity, fun x hx V lam hV hl1 hlam => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  set V0 : ℝ := x ^ (ε / 3) / 2 with hV0
  have hV01 : 1 ≤ V0 := by rw [hV0]; linarith
  have hV00 : 0 < V0 := by linarith
  have hlog : 2 * B * Real.log x ^ 2 ≤ x ^ (ε / 300) := by
    have e : x ^ (ε / 300) = x ^ (ε / 600) * x ^ (ε / 600) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hp : 0 ≤ x ^ (ε / 600) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp] at h3
    have h5 : Real.log x ^ 2 = |Real.log x| ^ 2 := (sq_abs _).symm
    rw [e, h5]
    have h6 : (2 * B + 1) * |Real.log x| ≤ x ^ (ε / 600) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)] at h3
      linarith
    have h7 := abs_nonneg (Real.log x)
    have h8 : ((2 * B + 1) * |Real.log x|) * ((2 * B + 1) * |Real.log x|) ≤
        x ^ (ε / 600) * x ^ (ε / 600) := mul_self_le_mul_self (by positivity) h6
    have h9 : 0 ≤ (4 * B ^ 2 + 2 * B + 1) * |Real.log x| ^ 2 := by positivity
    nlinarith
  have h2b : (2 : ℝ) ^ (61 / 100 : ℝ) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (61 / 100 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  have h2g : (2 : ℝ) ^ (39 / 100 : ℝ) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (39 / 100 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  have hlamV0 : lam ≤ V0 ^ (61 / 100 : ℝ) := by
    have e : V0 ^ (61 / 100 : ℝ) = x ^ (ε / 5) * x ^ (ε / 300) / 2 ^ (61 / 100 : ℝ) := by
      rw [hV0, Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      congr 2; ring
    have hp5 : 0 ≤ x ^ (ε / 5) := by positivity
    have hnum : 0 ≤ x ^ (ε / 5) * x ^ (ε / 300) := by positivity
    calc lam ≤ B * x ^ (ε / 5) * Real.log x ^ 2 := hlam
      _ = x ^ (ε / 5) * (2 * B * Real.log x ^ 2) / 2 := by ring
      _ ≤ x ^ (ε / 5) * x ^ (ε / 300) / 2 := by
          apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hp5) (by norm_num)
      _ ≤ x ^ (ε / 5) * x ^ (ε / 300) / 2 ^ (61 / 100 : ℝ) :=
          div_le_div_of_nonneg_left hnum (by positivity) h2b
      _ = V0 ^ (61 / 100 : ℝ) := e.symm
  have hV0g : x ^ (13 * ε / 100) / 2 ≤ V0 ^ (39 / 100 : ℝ) := by
    have e : V0 ^ (39 / 100 : ℝ) = x ^ (13 * ε / 100) / 2 ^ (39 / 100 : ℝ) := by
      rw [hV0, Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hx0.le]
      congr 2; ring
    have hle : x ^ (13 * ε / 100) ≤ x ^ (13 * ε / 100) :=
      le_rfl
    calc x ^ (13 * ε / 100) / 2 ≤ x ^ (13 * ε / 100) / 2 := by linarith
      _ ≤ x ^ (13 * ε / 100) / 2 ^ (39 / 100 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h2g
      _ = _ := e.symm
  set A : ℝ := Real.exp (-(c / 8) * x ^ (13 * ε / 100)) with hA
  set F : ℝ → ℝ := fun v => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) with hF
  have hFnn : ∀ v, 0 ≤ F v := fun v => by rw [hF]; positivity
  have hpt : ∀ v ∈ Set.Ioi V, F v ≤ A * 4 * H v := by
    intro v hv
    have hvV0 : V0 ≤ v := le_trans hV (le_of_lt hv)
    have hv1 : 1 ≤ v := le_trans hV01 hvV0
    have hv0 : 0 < v := by linarith
    have hl : lam ≤ v ^ (61 / 100 : ℝ) :=
      le_trans hlamV0 (Real.rpow_le_rpow hV00.le hvV0 (by norm_num))
    have hg : x ^ (13 * ε / 100) / 2 ≤ v ^ (39 / 100 : ℝ) :=
      le_trans hV0g (Real.rpow_le_rpow hV00.le hvV0 (by norm_num))
    have hp := thin_ptw c v lam hc hv1 (by linarith) hl
    have hsplit : Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) ≤
        A * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) := by
      rw [hA, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hv2 : 0 ≤ v ^ (2 : ℝ) := by positivity
    calc F v ≤ 4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := hp
      _ ≤ 4 * (v ^ (2 : ℝ) * (A * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsplit hv2) (by norm_num)
      _ = A * 4 * H v := by rw [hH]; ring
  have hV0' : (0 : ℝ) ≤ V := le_trans hV00.le hV
  have hsub : Set.Ioi V ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hV0'
  have hgint0 : MeasureTheory.IntegrableOn (fun v => A * 4 * H v) (Set.Ioi 0) := hHint.const_mul _
  have hgint : MeasureTheory.IntegrableOn (fun v => A * 4 * H v) (Set.Ioi V) := hgint0.mono_set hsub
  have hFmeas : Measurable F := by rw [hF]; fun_prop
  have hFint : MeasureTheory.IntegrableOn F (Set.Ioi V) := by
    refine MeasureTheory.Integrable.mono' hgint hFmeas.aestronglyMeasurable ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn v)]
    exact hpt v hv
  refine ⟨hFint, ?_⟩
  have hApos : 0 < A := Real.exp_pos _
  have hgnn : ∀ v ∈ Set.Ioi (0 : ℝ), 0 ≤ A * 4 * H v := by
    intro v hv
    have : 0 < v := hv
    rw [hH]; positivity
  calc (∫ v in Set.Ioi V, F v) ≤ ∫ v in Set.Ioi V, A * 4 * H v :=
        MeasureTheory.setIntegral_mono_on hFint hgint measurableSet_Ioi hpt
    _ ≤ ∫ v in Set.Ioi (0 : ℝ), A * 4 * H v :=
        MeasureTheory.setIntegral_mono_set hgint0
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hgnn)
          (Filter.Eventually.of_forall hsub)
    _ = A * (4 * K) := by rw [MeasureTheory.integral_const_mul, hK]; ring
    _ ≤ A * Real.exp (c / 16 * x ^ (13 * ε / 100)) := mul_le_mul_of_nonneg_left h4 hApos.le
    _ = Real.exp (-(c / 16) * x ^ (13 * ε / 100)) := by
        rw [hA, ← Real.exp_add]; congr 1; ring

theorem int_thin :
    ∀ ε c C A c' : ℝ, 0 < ε → 0 < c → 0 < C → 0 < A → 0 < c' → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (y lam : ℝ) (φ : ℝ → ℂ),
      Real.exp (x ^ (ε / 3)) / 3 ≤ y → 1 ≤ lam → lam ≤ A * x ^ (ε / 5) * Real.log x ^ 2 →
      (∀ u : ℝ, y ≤ u → ‖φ u‖ ≤ C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) →
      ‖(y : ℂ) * ∫ u in Set.Ioi y, φ u / (u : ℂ) ^ 2‖ ≤ y * Real.exp (-(c' * x ^ (ε / 8))) := by
  intro ε c C A c' hε hc hC hA hc'
  obtain ⟨c1, x1, hc1, hT⟩ := thin_integral ε c A hε hc hA
  obtain ⟨x2, hN⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 4).and
      (((tendsto_rpow_atTop (by positivity : 0 < ε / 200)).eventually_ge_atTop (2 * c' / c1)).and
        (Filter.eventually_gt_atTop 0)))
  obtain ⟨x3, hx3⟩ := Filter.eventually_atTop.1
    ((Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by positivity : 0 < 13 * ε / 100)).const_mul_atTop
      (by positivity : 0 < c1 / 2))).eventually_ge_atTop C)
  refine ⟨max x1 (max x2 x3), fun x hx y lam psi0 hy hl1 hlam hpsi => ?_⟩
  have hxx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxx2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxx3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hCx : C ≤ Real.exp (c1 / 2 * x ^ (13 * ε / 100)) := hx3 x hxx3
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  set V : ℝ := Real.log y with hVdef
  obtain ⟨ha, hb, hx0⟩ := hN x hxx2
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hly : x ^ (ε / 3) - Real.log 3 ≤ Real.log y := by
    have := Real.log_le_log (by positivity) hy
    rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at this
  have hV : x ^ (ε / 3) / 2 ≤ V := by linarith
  have hfin : c' * x ^ (ε / 8) ≤ c1 / 2 * x ^ (13 * ε / 100) := by
    have e : x ^ (13 * ε / 100) = x ^ (ε / 200) * x ^ (ε / 8) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have h1 : c' ≤ c1 / 2 * x ^ (ε / 200) := by
      rw [div_le_iff₀ hc1] at hb
      linarith
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  obtain ⟨hint, hbd⟩ := hT x hxx1 V lam hV hl1 hlam
  set F : ℝ → ℝ := fun v => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) with hF
  set G : ℝ → ℝ := fun u => F (Real.log u) / u with hG
  have himg : Real.exp '' Set.Ioi V = Set.Ioi y := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      have : V < v := hv
      show y < Real.exp v
      rw [← Real.exp_log hy0]
      exact Real.exp_lt_exp.mpr this
    · intro hu
      have hu' : y < u := hu
      have hu0 : 0 < u := lt_trans hy0 hu'
      exact ⟨Real.log u, Real.log_lt_log hy0 hu', Real.exp_log hu0⟩
  have hderiv : ∀ v ∈ Set.Ioi V, HasDerivWithinAt Real.exp (Real.exp v) (Set.Ioi V) v :=
    fun v _ => (Real.hasDerivAt_exp v).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp (Set.Ioi V) := Real.exp_injective.injOn
  have hcomp : (fun v => |Real.exp v| • G (Real.exp v)) = F := by
    funext v
    have hp := Real.exp_pos v
    rw [hG]
    simp only [abs_of_pos hp, Real.log_exp, smul_eq_mul]
    field_simp
  have hGint : MeasureTheory.IntegrableOn G (Set.Ioi y) := by
    rw [← himg, MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      hderiv hinj, hcomp]
    exact hint
  have hGval : (∫ u in Set.Ioi y, G u) = ∫ v in Set.Ioi V, F v := by
    rw [← himg, MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      hderiv hinj, hcomp]
  have hnorm : ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ C * ∫ u in Set.Ioi y, G u := by
    calc ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖
        ≤ ∫ u in Set.Ioi y, ‖psi0 u / (u : ℂ) ^ 2‖ := MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi y, C * G u := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hGint.const_mul C)
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
          have hu' : y < u := hu
          have hu0 : 0 < u := lt_trans hy0 hu'
          have h1 := hpsi u hu'.le
          show ‖psi0 u / (u : ℂ) ^ 2‖ ≤ C * G u
          rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
            div_le_iff₀ (by positivity)]
          refine le_trans h1 (le_of_eq ?_)
          rw [hG, hF]
          field_simp
      _ = C * ∫ u in Set.Ioi y, G u := MeasureTheory.integral_const_mul _ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
  apply mul_le_mul_of_nonneg_left _ hy0.le
  calc ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ C * ∫ u in Set.Ioi y, G u := hnorm
    _ = C * ∫ v in Set.Ioi V, F v := by rw [hGval]
    _ ≤ C * Real.exp (-c1 * x ^ (13 * ε / 100)) := mul_le_mul_of_nonneg_left hbd hC.le
    _ ≤ Real.exp (c1 / 2 * x ^ (13 * ε / 100)) * Real.exp (-c1 * x ^ (13 * ε / 100)) :=
        mul_le_mul_of_nonneg_right hCx (Real.exp_pos _).le
    _ ≤ Real.exp (-(c' * x ^ (ε / 8))) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith

end QH
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.MeanSquareBounds.IntThin =====

-- ===== clump member: Development.AutomorphicArithmetic.MeanSquareBounds.PsiThin =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.MeanSquareBounds.PsiThin", "h": "module\n\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds\npublic import Formalism.PeriodIntegrals.ExplicitFormula\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplex\npublic import Formalism.PeriodIntegrals.ZerosWindow\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Harmonic.Bounds\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff\nimport Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset\nimport Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedExplicitFormula\n\n"}
section -- clump:auto
@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem pt_zero_symm {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := by
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at h0
  have hρ1 : (1 - ρ) ≠ 0 := by
    intro h
    have : (1 - ρ).re = 0 := by rw [h]; simp
    simp at this
    linarith
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hρ0)] at hz
  have hg : DirichletCharacter.gammaFactor χ ρ ≠ 0 := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Complex.Gammaℝ_ne_zero_of_re_pos h0
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hc : DirichletCharacter.completedLFunction χ ρ = 0 := by
    rcases div_eq_zero_iff.mp hz with h | h
    · exact h
    · exact absurd h hg
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - ρ) (Or.inl hρ1),
    hχ.inv.completedLFunction_one_sub ρ, inv_inv, hc]
  simp

private theorem pt_rpow_le {u v r k : ℝ} (hu0 : 0 < u) (hv : v = Real.log u) (hv0 : 0 ≤ v) (hr : r ≤ 1 - k) :
    u ^ r ≤ u * Real.exp (-k * v) := by
  have hu : u = Real.exp v := by rw [hv, Real.exp_log hu0]
  rw [Real.rpow_def_of_pos hu0, ← hv]
  calc Real.exp (v * r) ≤ Real.exp (v + -k * v) := Real.exp_le_exp.2 (by nlinarith)
    _ = Real.exp v * Real.exp (-k * v) := Real.exp_add _ _
    _ = u * Real.exp (-k * v) := by rw [← hu]



private theorem pt_core {C7 C2 c lam : ℝ} (hC7 : 0 < C7) (hC2 : 0 ≤ C2) (hc : 0 < c) (hlam : 1 ≤ lam)
    (h7 : PI.ExplicitFormulaWith C7) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (hN : Real.log N ≤ lam)
    (hzf : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
      ρ.re ≤ 1 - c / (lam + Real.log (|ρ.im| + 3)))
    (hZ : ∀ T : ℝ, 1 ≤ T → ∑ᶠ ρ ∈ PI.ZerosBelow χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ ≤ C2 * (lam + Real.log T) ^ 2)
    (u : ℝ) (hu : Real.exp 1 ≤ u) :
    ‖PI.psi0 χ u‖ ≤ (C7 * (5 + C2) + C2) * u * (Real.log u + lam) ^ 2 *
      Real.exp (-(min (c / 3) 1) * Real.log u / (lam + Real.sqrt (Real.log u))) := by
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 1) hu
  set v : ℝ := Real.log u with hv
  have hv1 : 1 ≤ v := by rw [hv, Real.le_log_iff_exp_le hu0]; exact hu
  set s : ℝ := Real.sqrt v with hs
  have hss : s * s = v := Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hv1
  have hsv : s ≤ v := by nlinarith
  set c' : ℝ := min (c / 3) 1 with hc'
  have hc'1 : c' ≤ 1 := min_le_right _ _
  have hc'3 : c' ≤ c / 3 := min_le_left _ _
  have hls : 0 < lam + s := by linarith
  set E : ℝ := Real.exp (-c' * v / (lam + s)) with hE
  set T : ℝ := Real.exp s with hT
  have hT2 : 2 ≤ T := by have := Real.add_one_le_exp s; linarith
  have huv : u = Real.exp v := (Real.exp_log hu0).symm
  have hTu : T ≤ u := by rw [huv]; exact Real.exp_le_exp.2 hsv
  have hT0 : 0 < T := Real.exp_pos _
  have hlT : Real.log T = s := Real.log_exp s
  set W : ℝ := v + lam with hW
  set P : ℝ := u * E with hP
  have hP0 : 0 < P := by positivity
  have q0 : c' * v / (lam + s) ≤ v := by
    rw [div_le_iff₀ hls]; nlinarith
  have q1 : c' * v / (lam + s) ≤ s := by
    rw [div_le_iff₀ hls]; nlinarith
  have hP1 : 1 ≤ P := by
    rw [hP, huv, hE, ← Real.exp_add]
    apply Real.one_le_exp
    have : -c' * v / (lam + s) = -(c' * v / (lam + s)) := by ring
    rw [this]; linarith
  have hTE : T⁻¹ ≤ E := by
    rw [hT, ← Real.exp_neg, hE]
    apply Real.exp_le_exp.2
    have : -c' * v / (lam + s) = -(c' * v / (lam + s)) := by ring
    rw [this]; linarith
  obtain ⟨hfin, hexp⟩ := h7 N χ hp u T hT2 hTu
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have l1 : Real.log (N * u * T) = Real.log N + v + s := by
    rw [Real.log_mul (by positivity) hT0.ne', Real.log_mul hN0.ne' hu0.ne', hlT]
  have l2 : Real.log (N * u) = Real.log N + v := Real.log_mul hN0.ne' hu0.ne'
  have hWW : W ≤ W ^ 2 := by nlinarith
  have hWP : W ^ 2 ≤ W ^ 2 * P := by nlinarith
  have e1 : u * Real.log (N * u * T) ^ 2 / T ≤ 4 * W ^ 2 * P := by
    have a1 : Real.log (N * u * T) ^ 2 ≤ (2 * W) ^ 2 := by
      rw [l1]; apply pow_le_pow_left₀ (by linarith); linarith
    calc u * Real.log (N * u * T) ^ 2 / T = u * T⁻¹ * Real.log (N * u * T) ^ 2 := by
          rw [div_eq_mul_inv]; ring
      _ ≤ u * E * (2 * W) ^ 2 := by gcongr
      _ = 4 * W ^ 2 * P := by rw [hP]; ring
  have e2 : Real.log (N * u) ≤ W ^ 2 * P := by
    rw [l2]; exact (by linarith : Real.log N + v ≤ W).trans (hWW.trans hWP)
  have e3 : ∑ᶠ ρ ∈ PI.ZerosBelow χ 1, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ ≤ C2 * W ^ 2 * P := by
    refine (hZ 1 le_rfl).trans ?_
    rw [Real.log_one, add_zero]
    have : lam ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc C2 * lam ^ 2 ≤ C2 * (W ^ 2 * P) := mul_le_mul_of_nonneg_left (this.trans hWP) hC2
      _ = C2 * W ^ 2 * P := by ring
  have hl4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have hterm : ∀ ρ ∈ hfin.toFinset,
      ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ P * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖) := by
    intro ρ hρ
    obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ PI.ZerosBelow χ T := hfin.mem_toFinset.mp hρ
    have hre := hzf ρ r0 r1 r3
    have hg0 : 0 ≤ |ρ.im| := abs_nonneg _
    have hlg0 : 0 ≤ Real.log (|ρ.im| + 3) := Real.log_nonneg (by linarith)
    have hlg : Real.log (|ρ.im| + 3) ≤ s + 2 := by
      have : Real.log (|ρ.im| + 3) ≤ Real.log (4 * T) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hT0.ne', hlT] at this
      linarith
    have hden : 0 < lam + Real.log (|ρ.im| + 3) := by linarith
    have hcmp : c' / (lam + s) ≤ c / (lam + Real.log (|ρ.im| + 3)) := by
      rw [div_le_div_iff₀ hls hden]
      have h1 : c' * (lam + Real.log (|ρ.im| + 3)) ≤ c / 3 * (3 * (lam + s)) :=
        mul_le_mul hc'3 (by linarith) hden.le (by positivity)
      linarith
    have hle : u ^ ρ.re ≤ P := by
      have h3 : ρ.re ≤ 1 - c' / (lam + s) := by linarith
      have h4 := pt_rpow_le hu0 hv (by linarith) h3
      have h2 : -c' * v / (lam + s) = -(c' / (lam + s)) * v := by ring
      rw [hP, hE, h2]
      exact h4
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * (u ^ ρ.re / ‖ρ‖) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * (P / ‖ρ‖) := by gcongr
      _ = P * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖) := by ring
  have e4 : ‖∑ᶠ ρ ∈ PI.ZerosBelow χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ P * (C2 * W ^ 2) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum, ← finsum_mem_eq_finite_toFinset_sum _ hfin]
    apply mul_le_mul_of_nonneg_left _ hP0.le
    refine (hZ T (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ hC2)
    rw [hlT]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc ‖PI.psi0 χ u‖
      = ‖(PI.psi0 χ u + ∑ᶠ ρ ∈ PI.ZerosBelow χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
          ∑ᶠ ρ ∈ PI.ZerosBelow χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ := by
        rw [add_sub_cancel_right]
    _ ≤ ‖PI.psi0 χ u + ∑ᶠ ρ ∈ PI.ZerosBelow χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ +
          ‖∑ᶠ ρ ∈ PI.ZerosBelow χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ := norm_sub_le _ _
    _ ≤ C7 * (4 * W ^ 2 * P + W ^ 2 * P + C2 * W ^ 2 * P) + P * (C2 * W ^ 2) := by
        refine add_le_add (hexp.trans ?_) e4
        exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add e1 e2) e3) hC7.le
    _ = (C7 * (5 + C2) + C2) * u * W ^ 2 * E := by rw [hP]; ring



private theorem pt_zero_sum {C7 C lam ka : ℝ} (hC : 0 < C) (hlam : 1 ≤ lam) (hka : 0 < ka)
    (h7 : PI.ExplicitFormulaWith C7) (h11 : PI.ZerosWindowWith C) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (hN : Real.log N ≤ lam)
    (hlow : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ 2 → DirichletCharacter.LFunction χ ρ = 0 → ka / lam ≤ ρ.re)
    (T : ℝ) (hT : 1 ≤ T) :
    ∑ᶠ ρ ∈ PI.ZerosBelow χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ ≤ 6 * C * (3 / ka + 4) * (lam + Real.log T) ^ 2 := by
  classical
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hfin : (PI.ZerosBelow χ T).Finite := by
    refine (h7 N χ hp (max T 2) (max T 2) (le_max_right _ _) le_rfl).1.subset ?_
    rintro ρ ⟨r0, r1, r2, r3⟩
    exact ⟨r0, r1, lt_of_lt_of_le r2 (le_max_left _ _), r3⟩
  set M : ℕ := ⌊T⌋₊ with hM
  have hMT : (M : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  set Y : ℝ := lam + Real.log T with hY
  set La : ℝ := lam + Real.log ((M : ℝ) + 2) with hLa
  have hl2 := Real.log_two_lt_d9
  have hl3 : Real.log 3 ≤ 2 := by
    have h1 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hLa0 : 0 ≤ La := by
    have : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg (by linarith)
    linarith
  have hLa3 : La ≤ 3 * Y := by
    have h1 : Real.log ((M : ℝ) + 2) ≤ Real.log (3 * T) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hLM : Real.log ((M + 1 : ℕ) : ℝ) ≤ 1 + Real.log T := by
    have h1 : Real.log ((M + 1 : ℕ) : ℝ) ≤ Real.log (2 * T) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hwin : ∀ i : ℕ, i ≤ M → ∀ t : ℝ, |t| = i →
      ∑ ρ ∈ (h11 N χ hp t).1.toFinset, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤ C * La := by
    intro i hi t ht
    have h := (h11 N χ hp t).2
    rw [finsum_mem_eq_finite_toFinset_sum _ (h11 N χ hp t).1] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    rw [ht, Real.log_mul hN0.ne' (by positivity), hLa]
    have : (i : ℝ) ≤ M := by exact_mod_cast hi
    have h2 : Real.log ((i : ℝ) + 2) ≤ Real.log ((M : ℝ) + 2) := Real.log_le_log (by positivity) (by linarith)
    linarith
  set a : ℕ → ℝ := fun i => (if i ≤ 2 then lam / ka else 0) + 2 * (1 / ((i : ℝ) + 1)) with ha
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i
    simp only [ha]
    split_ifs <;> positivity
  have hfib : ∀ i ∈ Finset.range (M + 1),
      ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ ≤ a i * (2 * (C * La)) := by
    intro i hi
    have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have st1 : ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ ≤
        ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, a i * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨hρF, hρi⟩ := Finset.mem_filter.mp hρ
      obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ PI.ZerosBelow χ T := hfin.mem_toFinset.mp hρF
      have hile : (i : ℝ) ≤ |ρ.im| := by rw [← hρi]; exact Nat.floor_le (abs_nonneg _)
      have hpos : 0 < ‖ρ‖ := lt_of_lt_of_le r0 ((le_abs_self ρ.re).trans (Complex.abs_re_le_norm ρ))
      have h1 : 1 ≤ a i * ‖ρ‖ := by
        rcases le_total |ρ.im| 2 with h2 | h2
        · have hre := hlow ρ r0 r1 h2 r3
          have h3 := (le_abs_self ρ.re).trans (Complex.abs_re_le_norm ρ)
          have hi2 : i ≤ 2 := by
            have : (i : ℝ) ≤ 2 := hile.trans h2
            exact_mod_cast this
          have h4 : lam / ka ≤ a i := by
            simp only [ha, if_pos hi2]
            have : 0 ≤ 2 * (1 / ((i : ℝ) + 1)) := by positivity
            linarith
          calc (1 : ℝ) = lam / ka * (ka / lam) := by field_simp
            _ ≤ a i * ‖ρ‖ := mul_le_mul h4 (hre.trans h3) (by positivity) (ha0 i)
        · have h3 := Complex.abs_im_le_norm ρ
          have h4 : 2 * (1 / ((i : ℝ) + 1)) ≤ a i := by
            simp only [ha]
            split_ifs
            · have : 0 ≤ lam / ka := by positivity
              linarith
            · linarith
          have h5 : ((i : ℝ) + 1) / 2 ≤ ‖ρ‖ := by linarith
          calc (1 : ℝ) = 2 * (1 / ((i : ℝ) + 1)) * (((i : ℝ) + 1) / 2) := by field_simp
            _ ≤ a i * ‖ρ‖ := mul_le_mul h4 h5 (by positivity) (ha0 i)
      rw [div_le_iff₀ hpos]
      calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * 1 := (mul_one _).symm
        _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * (a i * ‖ρ‖) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = a i * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * ‖ρ‖ := by ring
    refine st1.trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (ha0 i)
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun ρ : ℂ => 0 ≤ ρ.im), two_mul]
    apply add_le_add
    · refine le_trans ?_ (hwin i hiM (i : ℝ) (Nat.abs_cast i))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        obtain ⟨hρ1, hs⟩ := Finset.mem_filter.mp hρ
        obtain ⟨hρF, hρi⟩ := Finset.mem_filter.mp hρ1
        obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ PI.ZerosBelow χ T := hfin.mem_toFinset.mp hρF
        rw [Set.Finite.mem_toFinset]
        refine ⟨r0, r1, ?_, r3⟩
        have a1 : (i : ℝ) ≤ |ρ.im| := by rw [← hρi]; exact Nat.floor_le (abs_nonneg _)
        have a2 : |ρ.im| < (i : ℝ) + 1 := by rw [← hρi]; exact Nat.lt_floor_add_one _
        rw [abs_of_nonneg hs] at a1 a2
        rw [abs_le]
        constructor <;> linarith
      · intro ρ _ _
        exact Nat.cast_nonneg _
    · refine le_trans ?_ (hwin i hiM (-(i : ℝ)) (by rw [abs_neg, Nat.abs_cast]))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        obtain ⟨hρ1, hs⟩ := Finset.mem_filter.mp hρ
        obtain ⟨hρF, hρi⟩ := Finset.mem_filter.mp hρ1
        obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ PI.ZerosBelow χ T := hfin.mem_toFinset.mp hρF
        rw [Set.Finite.mem_toFinset]
        refine ⟨r0, r1, ?_, r3⟩
        have a1 : (i : ℝ) ≤ |ρ.im| := by rw [← hρi]; exact Nat.floor_le (abs_nonneg _)
        have a2 : |ρ.im| < (i : ℝ) + 1 := by rw [← hρi]; exact Nat.lt_floor_add_one _
        rw [abs_of_neg (not_le.mp hs)] at a1 a2
        rw [abs_le]
        constructor <;> linarith
      · intro ρ _ _
        exact Nat.cast_nonneg _
  have hmaps : ∀ ρ ∈ hfin.toFinset, ⌊|ρ.im|⌋₊ ∈ Finset.range (M + 1) := by
    intro ρ hρ
    obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ PI.ZerosBelow χ T := hfin.mem_toFinset.mp hρ
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.floor_le_floor r2.le))
  have hH : ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / ((i : ℝ) + 1) ≤ 2 + Real.log T := by
    have h := harmonic_le_one_add_log (M + 1)
    have e : ((harmonic (M + 1) : ℚ) : ℝ) = ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / ((i : ℝ) + 1) := by
      simp [harmonic, one_div]
    rw [e] at h
    linarith
  have hb0 : 0 ≤ lam / ka := by positivity
  have hI : ∑ i ∈ Finset.range (M + 1), (if i ≤ 2 then lam / ka else 0) ≤ 3 * (lam / ka) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hb0
    have : ((Finset.range (M + 1)).filter (fun i => i ≤ 2)).card ≤ (Finset.range 3).card := by
      apply Finset.card_le_card
      intro i hi
      have := (Finset.mem_filter.mp hi).2
      exact Finset.mem_range.mpr (by omega)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hA : ∑ i ∈ Finset.range (M + 1), a i ≤ (3 / ka + 4) * Y := by
    simp only [ha]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : 3 * (lam / ka) ≤ 3 / ka * Y := by
      have : lam ≤ Y := by linarith
      calc 3 * (lam / ka) = 3 / ka * lam := by ring
        _ ≤ 3 / ka * Y := mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ i ∈ Finset.range (M + 1), ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖
      ≤ ∑ i ∈ Finset.range (M + 1), a i * (2 * (C * La)) := Finset.sum_le_sum hfib
    _ = (∑ i ∈ Finset.range (M + 1), a i) * (2 * (C * La)) := by rw [Finset.sum_mul]
    _ ≤ ((3 / ka + 4) * Y) * (2 * (C * (3 * Y))) := by
        apply mul_le_mul hA _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLa3 hC.le) (by norm_num)
    _ = 6 * C * (3 / ka + 4) * Y ^ 2 := by ring

private theorem pt_zero_free (c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ c : ℝ, 0 < c ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (lam : ℝ), 1 ≤ lam → Real.log N ≤ lam →
      (χ ^ 2 = 1 → χ ≠ 1 → NoExc c₀ χ) → ∀ ρ : ℂ, ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
        ρ.re ≤ 1 - c / (lam + Real.log (|ρ.im| + 3)) := by
  obtain ⟨c1, hc1, H⟩ := Formalism.ZeroFreeDirichlet.zFRDirichlet
  refine ⟨min c1 c₀, lt_min hc1 hc₀, ?_⟩
  intro N _ χ lam hlam hN hex ρ r1 hz
  by_contra hlt
  have ht := abs_nonneg ρ.im
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlA : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith)
  have hAB : Real.log (|ρ.im| + 2) ≤ Real.log (|ρ.im| + 3) := Real.log_le_log (by linarith) (by linarith)
  have hm0 : 0 < min c1 c₀ := lt_min hc1 hc₀
  have hreg : Formalism.ZeroFreeDirichlet.InRegion c1 N ρ := by
    unfold Formalism.ZeroFreeDirichlet.InRegion
    rw [Real.log_mul (by linarith) (by linarith)]
    have : min c1 c₀ / (lam + Real.log (|ρ.im| + 3)) ≤ c1 / (Real.log N + Real.log (|ρ.im| + 2)) :=
      div_le_div₀ hc1.le (min_le_left _ _) (by linarith) (by linarith)
    linarith
  have hLZ : Formalism.ZeroFreeDirichlet.IsLZero χ ρ := by
    refine ⟨Or.inr fun h => ?_, hz⟩
    rw [h, Complex.one_re] at r1
    exact lt_irrefl _ r1
  obtain ⟨hsq, hne, him, -⟩ := H N χ ρ hreg hLZ
  have hρ : ((ρ.re : ℝ) : ℂ) = ρ := Complex.ext (by simp) (by simp [him])
  have h2 : min c1 c₀ / (lam + Real.log (|ρ.im| + 3)) ≤ c₀ :=
    (div_le_self hm0.le (by linarith)).trans (min_le_right _ _)
  refine hex hsq hne ρ.re (by linarith) r1 ?_
  rw [hρ]; exact hz

theorem psi_thin :
    ∀ c₀ : ℝ, 0 < c₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (lam : ℝ), χ.IsPrimitive → 1 ≤ lam → Real.log N ≤ lam →
      (χ ^ 2 = 1 → χ ≠ 1 → NoExc c₀ χ) → ∀ u : ℝ, Real.exp 1 ≤ u →
        ‖PI.psi0 χ u‖ ≤ C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))) := by
  intro c₀ hc₀
  obtain ⟨c, hc, hzf⟩ := pt_zero_free c₀ hc₀
  obtain ⟨C7, hC7, h7⟩ : PI.ExplicitFormula := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C, hC, h11⟩ : PI.ZerosWindow := GlobalTheory.ZeroWindow.count_zeros_window
  have hC2 : 0 < 6 * C * (3 / (c / 3) + 4) := by positivity
  refine ⟨C7 * (5 + 6 * C * (3 / (c / 3) + 4)) + 6 * C * (3 / (c / 3) + 4), min (c / 3) 1, by positivity,
    lt_min (by positivity) one_pos, ?_⟩
  intro N _ χ lam hp hlam hN hex u hu
  refine pt_core hC7 hC2.le hc hlam h7 χ hp hN (fun ρ _ r1 hz => hzf N χ lam hlam hN hex ρ r1 hz) ?_ u hu
  intro T hT
  refine pt_zero_sum hC hlam (by positivity) h7 h11 χ hp hN ?_ T hT
  intro ρ r0 r1 r2 r3
  have hz' := pt_zero_symm hp r0 r1 r3
  have hex' : χ⁻¹ ^ 2 = 1 → χ⁻¹ ≠ 1 → NoExc c₀ χ⁻¹ := by
    intro h2 h1
    have hsq : χ ^ 2 = 1 := by rwa [inv_pow, inv_eq_one] at h2
    have hinv : χ⁻¹ = χ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq)
    rw [hinv] at h1 ⊢
    exact hex hsq h1
  have h := hzf N χ⁻¹ lam hlam hN hex' (1 - ρ) (by rw [Complex.sub_re, Complex.one_re]; linarith) hz'
  rw [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
  have hl5 : Real.log (|ρ.im| + 3) ≤ 2 := by
    have h1 : Real.log (|ρ.im| + 3) ≤ Real.log (Real.exp 2) := by
      apply Real.log_le_log (by positivity)
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h3 := Real.exp_one_gt_d9
      nlinarith
    rwa [Real.log_exp] at h1
  have hl0 : 0 ≤ Real.log (|ρ.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg ρ.im])
  have hcmp : c / 3 / lam ≤ c / (lam + Real.log (|ρ.im| + 3)) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith
  linarith

end QH
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.MeanSquareBounds.PsiThin =====

-- ===== clump member: Development.AutomorphicArithmetic.MeanSquareBounds.Thin =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.MeanSquareBounds.Thin", "h": "module\n\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.GIntegral\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.IntThin\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.PsiThin\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff\n\n"}
section -- clump:auto
@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem thin :
    ∀ ε A c c₀ : ℝ, 0 < ε → 0 < A → 0 < c → 0 < c₀ → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      Real.log N ≤ A * x ^ (ε / 5) * Real.log x ^ 2 → (χ ^ 2 = 1 → χ ≠ 1 → NoExc c₀ χ) →
      ∀ y : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y → ‖G0 χ y‖ ≤ y * Real.exp (-(c * x ^ (ε / 8))) := by
  intro ε A c c₀ hε hA hc hc₀
  obtain ⟨C, c1, hC, hc1, hpsi⟩ := psi_thin c₀ hc₀
  obtain ⟨x1, hx1⟩ := int_thin ε c1 C (A + 1) c hε hc1 hC (by linarith) hc
  refine ⟨max x1 (max (Real.exp 1) ((3 : ℝ) ^ (3 / ε))), ?_⟩
  intro x hx N _ χ hprim hN hexc y hy
  have hx1' : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : (3 : ℝ) ^ (3 / ε) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hxone : 1 ≤ x := he1.trans hxe
  have hpow3 : (3 : ℝ) ≤ x ^ (ε / 3) := by
    calc (3 : ℝ) = ((3 : ℝ) ^ (3 / ε)) ^ (ε / 3) := by
          rw [← Real.rpow_mul (by norm_num)]
          have : 3 / ε * (ε / 3) = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ x ^ (ε / 3) := Real.rpow_le_rpow (by positivity) hx3 (by positivity)
  have hy1 : Real.exp 1 ≤ y := by
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h3 : Real.exp 3 = Real.exp 1 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    have h4 : Real.exp 3 ≤ Real.exp (x ^ (ε / 3)) := Real.exp_le_exp.2 hpow3
    have h5 : Real.exp 1 * 3 ≤ Real.exp 3 := by rw [h3]; nlinarith [Real.exp_pos 1]
    linarith
  have hy1' : 1 ≤ y := he1.trans hy1
  have hlogx : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hxε : 1 ≤ x ^ (ε / 5) := Real.one_le_rpow hxone (by positivity)
  have hP : 1 ≤ x ^ (ε / 5) * Real.log x ^ 2 := one_le_mul_of_one_le_of_one_le hxε (one_le_pow₀ hlogx)
  have hlam : max 1 (Real.log N) ≤ (A + 1) * x ^ (ε / 5) * Real.log x ^ 2 := by
    rw [mul_assoc]
    rw [mul_assoc] at hN
    refine max_le (by nlinarith) (by nlinarith)
  have hψ := hpsi N χ (max 1 (Real.log N)) hprim (le_max_left _ _) (le_max_right _ _) hexc
  rw [g_integral N χ hprim y hy1', neg_mul, norm_neg]
  exact hx1 x hx1' y (max 1 (Real.log N)) (PI.psi0 χ) hy (le_max_left _ _) hlam
    (fun u hu => hψ u (hy1.trans hu))

end QH
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.MeanSquareBounds.Thin =====

-- ===== clump member: Development.AutomorphicArithmetic.MeanSquareBounds.GaussSumFunctionEq =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.MeanSquareBounds.GaussSumFunctionEq", "h": "module\n\npublic import Development.AutomorphicArithmetic.CharacterBoxes.PairGood\npublic import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.Thin\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.realCond\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds\nimport Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff\n\n"}
section -- clump:auto
@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem gauss_sum_function_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    Formalism.HC.An.gChi χ y = G0 χ y := by
  have key : ∀ n ∈ Icc 1 ⌊y⌋₊, max (y / (n : ℝ) - 1) 0 = y / n - 1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hy1 : 1 ≤ y := Nat.floor_pos.1 (by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.2 hn.2).trans (Nat.floor_le (by linarith))
    have : 1 ≤ y / n := by rw [le_div_iff₀ (by linarith)]; linarith
    exact max_eq_left (by linarith)
  unfold Formalism.HC.An.gChi G0
  by_cases h : χ = 1
  · simp only [h, if_true]
    congr 1
    unfold Formalism.HC.An.G G1
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [key n hn]
  · simp only [h, if_false]
    unfold Formalism.HC.An.sumLamChi Gchi
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [key n hn]

private theorem isReal_of_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h2 : χ ^ 2 = 1) (a : ZMod N) :
    (χ a).im = 0 := by
  by_cases ha : IsUnit a
  · have h := congrArg (fun f : DirichletCharacter ℂ N => f a) h2
    simp only [pow_two, MulChar.one_apply ha] at h
    rw [MulChar.mul_apply] at h
    have hz : χ a = 1 ∨ χ a = -1 := by
      have : (χ a - 1) * (χ a + 1) = 0 := by ring_nf; rw [← pow_two] at h; rw [h]; ring
      rcases mul_eq_zero.1 this with h1 | h1
      · left; linear_combination h1
      · right; linear_combination h1
    rcases hz with hz | hz <;> simp [hz]
  · simp [MulChar.map_nonunit χ ha]

private theorem level_dvd {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : H.IsCharE χ) : N ∣ H.condN := by
  obtain ⟨θ, hθ⟩ := h
  have hp : (Formalism.HC.PChar.mk N χ hθ.1) = H.prim θ := (H.isPrimOf_iff θ (Formalism.HC.PChar.mk N χ hθ.1)).1 hθ
  have hN : N = (H.prim θ).N := congrArg Formalism.HC.PChar.N hp
  rw [hN]
  exact DirichletCharacter.conductor_dvd_level (H.dir θ)

theorem thinH :
    UpperTheory.Top.ThinH := by
  refine ⟨1, one_pos, fun B eps he he52 => ?_⟩
  obtain ⟨c₀s, hc₀s, hsmall⟩ := small_zeros (8 * ⌊B⌋₊)
  have hc₀ : 0 < min c₀s (1 / 400) := lt_min hc₀s (by norm_num)
  obtain ⟨x₀, hx₀⟩ := thin eps 2 1 (min c₀s (1 / 400)) he two_pos one_pos hc₀
  refine ⟨x₀, fun x hx φ H hB hlog hRB => ?_⟩
  intro N _ χ hχ y hy
  rw [gauss_sum_function_eq]
  have hprim : χ.IsPrimitive := by
    obtain ⟨θ, hθ⟩ := hχ
    exact hθ.1
  have hNd : N ∣ H.condN := level_dvd H χ hχ
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hlogN : Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 :=
    (Real.log_le_log (by exact_mod_cast hNpos)
      (by exact_mod_cast Nat.le_of_dvd H.condN_pos hNd)).trans hlog
  refine hx₀ x hx N χ hprim hlogN ?_ y hy
  intro h2 h1 β hβ hβ1
  have hq : H.q.Prime := H.hyp.1
  have hd : H.d.Prime := H.hyp.2.1
  by_cases hqd : H.q ∣ N ∨ H.d ∣ N
  · exact hRB (Formalism.HC.PChar.mk N χ hprim) hχ (isReal_of_sq χ h2) hqd β
      (by have := min_le_right c₀s (1 / 400); linarith)
  · push_neg at hqd
    have hQ0 : H.QS ≠ 0 := (H.QS_pos).ne'
    have hsplitQ := Nat.ordProj_mul_ordCompl_eq_self H.QS 2
    have hprimes : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ 8 * (H.QS / 2 ^ H.QS.factorization 2) ∨ p = H.q ∨ p = H.d := by
      intro p hp hpN
      have hpc : p ∣ H.QS * H.q * H.d := hpN.trans hNd
      rcases (Nat.Prime.dvd_mul hp).1 hpc with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
        · left
          by_cases hp2 : p = 2
          · subst hp2
            exact Dvd.dvd.mul_right (by norm_num) _
          · apply Dvd.dvd.mul_left
            rw [← hsplitQ] at h'
            have hcop : Nat.Coprime p (2 ^ H.QS.factorization 2) :=
              Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
            exact hcop.dvd_of_dvd_mul_left h'
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 h'))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hd).1 h))
    have hdiv := real_cond (8 * (H.QS / 2 ^ H.QS.factorization 2)) H.q H.d N χ hprim h2
      (dvd_mul_right 8 _) hq hd hprimes
    have hcq : Nat.Coprime N H.q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd.1).symm
    have hcd : Nat.Coprime N H.d := ((Nat.Prime.coprime_iff_not_dvd hd).2 hqd.2).symm
    have hN0 : N ∣ 8 * (H.QS / 2 ^ H.QS.factorization 2) :=
      hcq.dvd_of_dvd_mul_right (hcd.dvd_of_dvd_mul_right hdiv)
    have hopos : 0 < H.QS / 2 ^ H.QS.factorization 2 := Nat.ordCompl_pos 2 hQ0
    have hofl : H.QS / 2 ^ H.QS.factorization 2 ≤ ⌊B⌋₊ := Nat.le_floor hB
    have hNle : N ≤ 8 * ⌊B⌋₊ := (Nat.le_of_dvd (by omega) hN0).trans (by omega)
    exact hsmall N χ hNle h1 β (by have := min_le_left c₀s (1 / 400); linarith) hβ1

end QH
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.MeanSquareBounds.GaussSumFunctionEq =====
