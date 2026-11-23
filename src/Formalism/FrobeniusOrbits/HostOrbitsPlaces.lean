module

public import Formalism.FrobeniusOrbits.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IntermediateField

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def HostOrbits : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, (φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) →
    (∀ τ ∈ Psi e, ∀ i : ℕ, φ ^ i * τ ∈ Psi e ↔ Even i) ∧
    (φ.1 = c0 → φ.2 ≠ 1 → Even (orderOf φ.2) ∧ orderOf φ = orderOf φ.2)

def placeOf {e : ℕ} (g : GG e) : GG e := if g.1.2 = 1 then g else cc e * g

def HostOrbitsPlaces : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, (φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) → ∀ τ ∈ Psi e, ∀ i : ℕ,
    (placeOf (φ ^ i * τ)).2 = φ.2 ^ i * τ.2 ∧
    (φ.1 = c0 → (placeOf (φ ^ i * τ)).1 = τ.1) ∧
    (φ.1 = ((1 : ℤˣ), (-1 : ℤˣ)) →
      (placeOf (φ ^ i * τ)).1 = (if Even i then 1 else (sg e).1) * τ.1)

def HostOrbitCount : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, φ.1 = c0 → ∀ τ ∈ Psi e,
    (Set.range fun i : ℕ => placeOf (φ ^ i * τ)).ncard = orderOf φ.2

def HostFiniteOrder : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (k g : ℕ), g.Prime → ∀ M : Matrix (Fin k) (Fin k) (hostE ζ a b), M ^ g = 1 → M ≠ 1 →
    g - 1 ≤ 2 ^ (e + 2) * k

end Formalism.FrobeniusOrbits
