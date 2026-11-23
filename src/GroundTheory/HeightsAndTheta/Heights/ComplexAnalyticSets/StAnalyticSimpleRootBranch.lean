module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def AnalyticSimpleRootBranch.Statement : Prop :=
  ∀ (d N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (y : Fin d → ℂ) (τ : ℂ),
    (∀ j, AnalyticAt ℂ (a j) y) →
    τ ^ N + ∑ j, a j y * τ ^ (j : ℕ) = 0 →
    (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).derivative.eval τ ≠ 0 →
    ∃ (U : Set (Fin d → ℂ)) (B : Set ℂ) (ψ : (Fin d → ℂ) → ℂ),
      IsOpen U ∧ y ∈ U ∧ IsOpen B ∧ τ ∈ B ∧ AnalyticOnNhd ℂ ψ U ∧ ψ y = τ ∧
        ∀ y' ∈ U, ψ y' ∈ B ∧ ∀ s ∈ B, (s ^ N + ∑ j, a j y' * s ^ (j : ℕ) = 0 ↔ s = ψ y')

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
