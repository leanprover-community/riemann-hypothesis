module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermPrimitivePresentation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionObjects
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

def GermProjectionFunctionForm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    (∀ i, AnalyticAt ℂ (p i) w) → IsFiniteGermProjection w (holGermIdeal w p) A →
      (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → IsGermCombination w p (fun z => h (A z)) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) ∧
      (∀ i : σ, ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        IsGermCombination w p (fun z => z i ^ n + ∑ j, b j (A z) * z i ^ (j : ℕ))) ∧
      (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
        ∃ (s : Finset (σ → ℕ)) (a : (σ → ℕ) → (Fin d → ℂ) → ℂ), (∀ m ∈ s, AnalyticAt ℂ (a m) (A w)) ∧
          IsGermCombination w p (fun z => g z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
