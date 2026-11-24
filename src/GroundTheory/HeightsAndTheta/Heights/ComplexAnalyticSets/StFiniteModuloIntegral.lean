module

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

open Topology Filter

def IsFiniteModuloOver {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) {k : ℕ}
    (f : Fin k → (σ → ℂ) → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) : Prop :=
  ∃ (n : ℕ) (e : Fin n → (σ → ℂ) → ℂ), (∀ m, AnalyticAt ℂ (e m) x) ∧
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (b : Fin n → (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ m, AnalyticAt ℂ (b m) (L x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z = ∑ m, b m (L z) * e m z + ∑ i, h i z * f i z

def FiniteModuloIntegral.Statement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Fintype τ] (x : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ)
    (L : (σ → ℂ) →L[ℂ] (τ → ℂ)),
    (∀ i, AnalyticAt ℂ (f i) x) → IsFiniteModuloOver x f L →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (N : ℕ) (a : Fin N → (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ j, AnalyticAt ℂ (a j) (L x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z ^ N + ∑ j, a j (L z) * g z ^ (j : ℕ) = ∑ i, h i z * f i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
