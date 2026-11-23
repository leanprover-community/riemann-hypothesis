module

public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Mathlib.Data.Matrix.ColumnRowPartitioned
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

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def IsotypicAveragingStatement : Prop :=
  ∀ (S : Type) [CommRing S] (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) S)
    (E : Matrix (Ix g) (Ix g) S) (cp : S)
    (εT : Fin m → Matrix (Ix g) (Ix g) S) (εL : Fin m → Matrix (Fin g) (Fin g) S)
    (π : Equiv.Perm (Fin m)),
    (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    Btᵀ * Ht - Htᵀ * Bt = cp • E →
    let Bt' := ∑ i, εL i * Bt * εT i
    (Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E) ∧ (∀ i, Bt' * εT i = εL i * Bt') ∧
    (Matrix.fromRows Ht Bt').det ^ 2 = cp ^ (2 * g) * E.det

end ReciprocityTheory.PGsh.Up
