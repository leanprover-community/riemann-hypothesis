module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivRiemannZetaLocalZeroSum
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

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

theorem _root_.GlobalTheory.T.logDeriv_riemannZeta_local_zero_sum : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|t| + 2) := by
  first | exact @GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local | exact GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local | (intros; apply GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local <;> assumption)
