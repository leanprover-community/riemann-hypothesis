module

public import Formalism.ThetaLogCoordinates.JacobiPathWeights.IndexWeightsDominance
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def valP {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    WithTop ℤ :=
  valS (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl G)

def lamP {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    WithBot ℤ :=
  lam1S (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl G)

def geB (x : WithTop ℤ) (θ : WithBot ℤ) : Prop := ∀ t : ℤ, θ = (t : WithBot ℤ) → (t : WithTop ℤ) ≤ x

def leT (y : WithBot ℤ) (M : WithTop ℤ) : Prop := ∀ t : ℤ, M = (t : WithTop ℤ) → y ≤ (t : WithBot ℤ)

def GoodG {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k) : Prop :=
  geB (valP isVec i G) θ ∧ leT (lamP isVec i G) M

def psiFam (R : Type*) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    MvPolynomial (ℕ × Fin n) R :=
  psiPath R isVec x.1.1 N x.1.2

def FactSplit : Prop :=
  ∀ (k : Type) [Field k] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k), i ≤ N → G ∈ polB k n N B →
    ∃ (T : Finset (ℕ × Fin n →₀ ℕ)) (Gc : (ℕ × Fin n →₀ ℕ) → MvPolynomial (ℕ × Fin n) k),
      (∀ β ∈ T, ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0) ∧
      (∀ β ∈ T, Gc β ∈ polB k n i B) ∧
      G = ∑ β ∈ T, Gc β * monomial β 1 ∧
      (GoodG isVec i θ M G → ∀ β ∈ T, GoodG isVec i θ M (Gc β))

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
