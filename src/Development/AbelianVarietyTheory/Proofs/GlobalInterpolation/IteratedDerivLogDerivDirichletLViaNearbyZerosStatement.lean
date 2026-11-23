module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Mathlib.Data.FunLike.Fintype
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedDerivLogDerivDirichletLViaNearbyZeros
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

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.iteratedDeriv_logDeriv_dirichletL_via_nearby_zeros : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ) (k : ℕ), 1 < σ → σ ≤ 2 → (zerosDisc χ (2 + t * I) 3).Finite ∧ (∑ᶠ w ∈ zerosDisc χ (2 + t * I) 3, (ord χ w : ℝ)) ≤ C * Real.log (q * (|t| + 2)) ∧ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k (σ + t * I) - (if χ = 1 then 1 / ((σ : ℂ) + t * I - 1) ^ (k + 1) else 0) + ∑ᶠ w ∈ zerosDisc χ (2 + t * I) 3, (ord χ w : ℂ) / ((σ : ℂ) + t * I - w) ^ (k + 1)‖ ≤ C * Real.log (q * (|t| + 2)) / σ ^ k := by
  first | exact @GlobalTheory.LogDerivHigher.main | exact GlobalTheory.LogDerivHigher.main | (intros; apply GlobalTheory.LogDerivHigher.main <;> assumption)
