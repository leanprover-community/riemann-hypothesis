module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix

namespace GlobalTheory.SeqCx

def uniM (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Set (List M) :=
  {l | ∃ f : Fin l.length → M →ₗ[R] R, ∀ i j : Fin l.length, f i (l.get j) = if i = j then 1 else 0}

def low (R : Type) [CommRing R] (n : ℕ) : Set (ℕ →₀ R) := {x | ∀ i, n ≤ i → x i = 0}

def aff (R : Type) [CommRing R] (n j : ℕ) : Set (ℕ →₀ R) := {x | x - Finsupp.single j 1 ∈ low R n}

def LinkExactLow (R : Type) [CommRing R] (s n : ℕ) : Prop :=
  ∀ τ ∈ uniM R (ℕ →₀ R), ∀ p : ℕ, p + s + τ.length ≤ n → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R n) τ) p

def LinkExactAff (R : Type) [CommRing R] (s n : ℕ) : Prop :=
  ∀ j : ℕ, n ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), ∀ p : ℕ, p + s + τ.length ≤ n + 1 →
    ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) τ) p

def hbd (V W : Type) : (List V × List W →₀ ℤ) →ₗ[ℤ] (List V × List W →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun z : List V × List W =>
    Finsupp.mapDomain (fun x => (x, z.2)) (bd V (Finsupp.single z.1 1))

def vbd (V W : Type) : (List V × List W →₀ ℤ) →ₗ[ℤ] (List V × List W →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun z : List V × List W =>
    Finsupp.mapDomain (fun w => (z.1, w)) (bd W (Finsupp.single z.2 1))

def chains2 {V W : Type} (D : Set (List V × List W)) (a b : ℕ) : Submodule ℤ (List V × List W →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {z | z ∈ D ∧ z.1.length = a ∧ z.2.length = b}

def SubClosed2 {V W : Type} (D : Set (List V × List W)) : Prop :=
  ∀ z ∈ D, ∀ (x : List V) (w : List W), x.Sublist z.1 → w.Sublist z.2 → (x, w) ∈ D

def splitPairs (R : Type) [CommRing R] (n : ℕ) : Set (List ((Fin n → R) × (Fin n → R)) × List (Fin n → R)) :=
  {z | z.1 ∈ splitSeq R n ∧ z.2 ∈ uniSeq R n ∧ ∀ y ∈ z.1, ∀ u ∈ z.2, y.2 ⬝ᵥ u = 0}

end GlobalTheory.SeqCx

end
