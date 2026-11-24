module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GenericCountCover
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

def MaximalCountUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ))
    (N : ℕ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x)) →
    IsGenericCountCover Y A D N →
    ∀ x ∈ Y, {x' | x' ∈ Y ∧ A x' = A x}.encard = N →
      ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y ∈ O, A (h y) = y) ∧ Y ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
