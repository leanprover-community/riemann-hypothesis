module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
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

open MvPolynomial Topology

def LocalBranchedCovering.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ)),
    I.IsPrime → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    ∃ (k : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (W : Set (σ → ℂ)) (D : Set (Fin k → ℂ)) (m : ℕ)
      (δ : (Fin k → ℂ) → ℂ),
      IsOpen W ∧ w ∈ W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ IsOpen D ∧ A w ∈ D ∧
      (∀ z ∈ zeroSetIn I ∩ W, A z = A w → z = w) ∧
      (∀ z ∈ zeroSetIn I ∩ closure W, A z ∈ D → z ∈ W) ∧
      DifferentiableOn ℂ δ D ∧
      (∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, δ t ≠ 0) ∧
      (∀ y ∈ D, δ y ≠ 0 → ∃ (O : Set (Fin k → ℂ)) (s : Fin m → (Fin k → ℂ) → σ → ℂ),
        IsOpen O ∧ y ∈ O ∧ (∀ j, DifferentiableOn ℂ (s j) O) ∧
        ∀ y' ∈ O, (∀ j, s j y' ∈ zeroSetIn I ∩ W ∧ A (s j y') = y') ∧
          Function.Injective (fun j => s j y') ∧
          ∀ z ∈ zeroSetIn I ∩ W, A z = y' → z ∈ Set.range (fun j => s j y')) ∧
      ∀ z ∈ zeroSetIn I ∩ W, ∀ ε > 0, A '' (zeroSetIn I ∩ Metric.ball z ε) ∈ 𝓝 (A z)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
