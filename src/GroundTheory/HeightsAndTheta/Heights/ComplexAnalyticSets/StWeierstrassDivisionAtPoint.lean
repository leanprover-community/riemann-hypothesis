module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloEliminate
public import Mathlib.Analysis.Analytic.Order
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def WeierstrassDivisionAtPoint.Statement : Prop :=
  ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (y₀ : τ → ℂ) (c : τ) (d : ℕ) (F g : (τ → ℂ) → ℂ),
    AnalyticAt ℂ F y₀ → AnalyticAt ℂ g y₀ →
    analyticOrderAt (fun s : ℂ => F (y₀ + Pi.single c s)) 0 = d →
    ∃ (q : (τ → ℂ) → ℂ) (a : Fin d → (τ → ℂ) → ℂ),
      AnalyticAt ℂ q y₀ ∧ (∀ j, AnalyticAt ℂ (a j) (zeroCoordinate c y₀)) ∧
      ∀ᶠ y in 𝓝 y₀, g y = q y * F y + ∑ j : Fin d, a j (zeroCoordinate c y) * (y c - y₀ c) ^ (j : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
