module

public import ReciprocityTheory.DualLattices.UnramifiedCokernelLengthStatement
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

def qE {R : Type} [CommRing R] {g m : ℕ} (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    Submodule R (Fin g ⊕ Fin g → R) :=
  (LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)).comap (LinearMap.funLeft R R Sum.inl) ⊓
    (LinearMap.range (Matrix.mulVecLin (εL i))).comap (LinearMap.funLeft R R Sum.inr)

abbrev xModE {R : Type} [CommRing R] {g m : ℕ} (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) :=
  qE εL i (π i) ⧸
    ((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin (fromRows Ht Bt))).comap
      (qE εL i (π i)).subtype

def LenIdStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R) (E : Matrix (Ix g) (Ix g) R)
    (cp : R), cp ≠ 0 → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
    ∀ (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    ∀ (i : Fin m) (d : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin d → R)) →
    ∀ c₁ c₂ : NNReal, HasLen v R (cokE Ht εT εL i (π i)) c₁ →
      HasLen v R (cokE Ht εT εL (π i) i) c₂ →
      ∃ X : NNReal, HasLen v R (xModE Ht Bt εT εL π i) X ∧ X * c₁ = v (algebraMap R C cp) ^ d * c₂

end ReciprocityTheory.PGsh.Up
