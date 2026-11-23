module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Covering.Basic
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

open Filter Topology Matrix

noncomputable section

def FibreSectionsCovering.Statement : Prop :=
  ∀ (n e N : ℕ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (Ω : Set (Fin (e + 1) → ℂ))
    (X : Set (Fin n → ℂ)) (hX : Set.MapsTo (fun x => A *ᵥ x) X Ω),
    (∀ y ∈ Ω, {x | x ∈ X ∧ A *ᵥ x = y}.encard = N) →
    (∀ x ∈ X, ∃ (O : Set (Fin (e + 1) → ℂ)) (V' : Set (Fin n → ℂ)) (g : (Fin (e + 1) → ℂ) → Fin n → ℂ),
      IsOpen O ∧ A *ᵥ x ∈ O ∧ IsOpen V' ∧ x ∈ V' ∧ DifferentiableOn ℂ g O ∧ g (A *ᵥ x) = x ∧
        (∀ y ∈ O, A *ᵥ g y = y) ∧ X ∩ V' = g '' O) →
    IsCoveringMap hX.restrict

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
