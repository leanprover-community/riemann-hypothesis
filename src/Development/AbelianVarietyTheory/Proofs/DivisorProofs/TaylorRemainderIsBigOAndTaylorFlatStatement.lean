module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRemainderIsBigOAndTaylorFlat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat : ∀ {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → ((fun z ↦ f z - GlobalTheory.PeriodFamily.taylor N z f) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) ∧ ((f =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) → ∀ {D : Type} [CommRing D] [Algebra ℂ D] (t : I → D), GlobalTheory.PeriodFamily.taylor N t f = 0) := by
  first | exact @GlobalTheory.PeriodFamily.taylor_remainder_and_flat | exact GlobalTheory.PeriodFamily.taylor_remainder_and_flat | (intros; apply GlobalTheory.PeriodFamily.taylor_remainder_and_flat <;> assumption)
