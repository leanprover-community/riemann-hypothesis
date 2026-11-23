module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def RingAFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    (∀ x ∈ ringA l, ‖x‖ ≤ 1) ∧
    (∀ x ∈ ringA l, ∃ f : ℕ, 0 < f ∧ ∃ y ∈ ringA l, x ^ (l ^ f) - x = (l : ℂ_[l]) * y)

def FrobA : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    ∃ σ0 : ringA l →+* ringA l,
      (∀ ζ : ringA l, (ζ : ℂ_[l]) ∈ muPrime l → σ0 ζ = ζ ^ l) ∧
      ∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y

def FrobAIsom : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (σ0 : ringA l →+* ringA l),
    (∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y) →
    ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖

end Formalism.L2.Th1.D
