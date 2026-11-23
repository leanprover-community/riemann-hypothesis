module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloIntegral
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

noncomputable def zeroCoordinate {τ : Type} [DecidableEq τ] (c : τ) : (τ → ℂ) →L[ℂ] (τ → ℂ) :=
  ContinuousLinearMap.pi fun c' => if c' = c then 0 else ContinuousLinearMap.proj c'

theorem zeroCoordinate_apply {τ : Type} [DecidableEq τ] (c : τ) (y : τ → ℂ) (c' : τ) :
    zeroCoordinate c y c' = if c' = c then 0 else y c' := by
  by_cases h : c' = c <;> simp [zeroCoordinate, h]

def FiniteModuloEliminate.Statement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Fintype τ] [DecidableEq τ] (x : σ → ℂ) (k : ℕ)
    (f : Fin k → (σ → ℂ) → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) (c : τ),
    (∀ i, AnalyticAt ℂ (f i) x) → IsFiniteModuloOver x f L →
    (∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : τ → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ c', AnalyticAt ℂ (h' c') x) ∧
      ∀ᶠ z in 𝓝 x, (L z c - L x c) ^ r =
        ∑ i, h i z * f i z + ∑ c', h' c' z * (zeroCoordinate c (L z) c' - zeroCoordinate c (L x) c')) →
    IsFiniteModuloOver x f ((zeroCoordinate c).comp L)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
