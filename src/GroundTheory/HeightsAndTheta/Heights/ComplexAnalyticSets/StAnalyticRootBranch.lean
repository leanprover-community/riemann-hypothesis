module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.Separable
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

def AnalyticRootBranch.Statement : Prop :=
  ∀ (d N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (t₀ : Fin d → ℂ) (τ₀ : ℂ),
    (∀ j, AnalyticAt ℂ (a j) t₀) →
    (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t₀) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable →
    τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
    ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ AnalyticOnNhd ℂ r O ∧ r t₀ = τ₀ ∧
      ∀ t ∈ O, r t ^ N + ∑ j, a j t * r t ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
