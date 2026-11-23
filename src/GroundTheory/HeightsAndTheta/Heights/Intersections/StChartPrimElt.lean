module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Polynomial

def ChartPrimElt.Statement : Prop :=
  ∀ (Φ : Type) [Field Φ] [CharZero Φ] (Φ' : Type) [Field Φ'] [Algebra Φ Φ'] (Q : Type) [Fintype Q]
    (r : Q → Φ'),
    FiniteDimensional Φ (IntermediateField.adjoin Φ (Set.range r)) →
    ∃ (τ : MvPolynomial Q Φ) (g : Q → Φ[X]) (u : Φ[X]),
      (minpoly Φ (MvPolynomial.aeval r τ)).natDegree =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) ∧
      (∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q) ∧
      minpoly Φ (MvPolynomial.aeval r τ) ∣ u * derivative (minpoly Φ (MvPolynomial.aeval r τ)) - 1 ∧
      minpoly Φ (MvPolynomial.aeval r τ) ∣ MvPolynomial.aeval g τ - X ∧
      ∀ q, r q ≠ 0 → ∃ h : Φ[X], minpoly Φ (MvPolynomial.aeval r τ) ∣ h * g q - 1

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
