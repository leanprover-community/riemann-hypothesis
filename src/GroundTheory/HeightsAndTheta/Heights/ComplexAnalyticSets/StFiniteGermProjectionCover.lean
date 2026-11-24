module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalParametrisation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
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

def FiniteGermProjectionCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N₀ ∈ 𝓝 w, ∀ (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ)),
      IsOpen B → B ⊆ N₀ → w ∈ X ∩ B → IsOpen D → IsPreconnected D → Set.MapsTo A (X ∩ B) D →
      (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
      (∀ x ∈ X ∩ B, A x = A w → x = w) →
      ∃ (δ : (Fin d → ℂ) → ℂ) (N : ℕ), IsLocalParametrisation X w B A D δ N

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
