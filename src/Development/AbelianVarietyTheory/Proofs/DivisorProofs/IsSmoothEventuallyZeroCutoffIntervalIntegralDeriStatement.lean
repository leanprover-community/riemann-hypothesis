module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothEventuallyZeroCutoffIntervalIntegralDeri
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

theorem _root_.GlobalTheory.T.isSmoothEventuallyZeroCutoff_intervalIntegral_deriv : ∀ (F : ℝ → ℝ → ℝ) (a b : ℝ), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) → (∃ R : ℝ, ∀ s ∈ Set.uIcc a b, ∀ y, R ≤ y → F s y = 0) → GlobalTheory.PsCo.Pc1.IsCutFn (fun y => ∫ s in a..b, F s y) ∧ ∀ y, deriv (fun y => ∫ s in a..b, F s y) y = ∫ s in a..b, deriv (F s) y := by
  first | exact @GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv | exact GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv | (intros; apply GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv <;> assumption)
