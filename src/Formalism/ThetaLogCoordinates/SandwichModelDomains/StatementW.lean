module

public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

def sExp (p r l : ℕ) : ℕ := r * (r - 1) / 2 * Nat.log p (l + r - 1)

def LBound (r : ℕ) {n : ℕ} (ν : Fin n → ℕ) (l : ℕ) : Prop :=
  (∀ t, ν t ≤ l) ∨ (n = r ∧ ∀ s t, ν s ≤ ν t + l)

def PrimeToPUnits (p : ℕ) (O : Type) [CommRing O] : Prop :=
  ∀ c : ℤ, ¬ (p : ℤ) ∣ c → IsUnit ((c : ℤ) : O)

def SandwichZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ x ∈ dualWeyl ℤ_[p] r n ν, ((p : ℤ_[p]) ^ sExp p r l) • x ∈ weyl ℤ_[p] r n hn ν

def SandwichZ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ f ∈ dualWeyl ℤ r n ν, ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ (c * (p : ℤ) ^ sExp p r l) • f ∈ weyl ℤ r n hn ν

def SandwichDomain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ (O : Type) [CommRing O] [IsDomain O], PrimeToPUnits p O →
      (∀ x ∈ dualWeyl O r n ν, ((p : O) ^ sExp p r l) • x ∈ weyl O r n hn ν) ∧
      weyl O r n hn ν ≤ dualWeyl O r n ν

def UnitsOfLocal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O], ¬ IsUnit ((p : ℕ) : O) → PrimeToPUnits p O

def SandwichLocal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], ¬ IsUnit ((p : ℕ) : O) →
      (∀ x ∈ dualWeyl O r n ν, ((p : O) ^ sExp p r l) • x ∈ weyl O r n hn ν) ∧
      weyl O r n hn ν ≤ dualWeyl O r n ν

end Formalism.InvariantFactorPaths.INST
