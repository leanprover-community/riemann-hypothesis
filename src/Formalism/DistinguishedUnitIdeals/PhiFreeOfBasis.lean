module

public import Formalism.DistinguishedUnitIdeals.ExistsConstOfInvariantMod
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
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

namespace Formalism.ExponentWindows.E

open PowerSeries

def FactVval {O : Type} [CommRing O] (u : Oˣ) (ℓ : ℕ) : Prop :=
  ∀ m : ℤ, m ≠ 0 → ∃ ε : Oˣ, 1 - ((u ^ m : Oˣ) : O) = (ε : O) * (ℓ : O) ^ (1 + padicValInt ℓ m)

def FactVvalOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (ℓ : ℕ) (u x : Oˣ), ℓ.Prime → 3 ≤ ℓ →
    ¬ IsUnit (ℓ : O) → (u : O) = 1 + (ℓ : O) * (x : O) → FactVval u ℓ

def FactVOf : Prop :=
  ∀ (O LL Ks Δ : Type) [CommRing O] [Field LL] [Algebra O LL] [CommRing Ks] [Algebra LL Ks]
    (Lev : G.Level LL Ks Δ) (u : Oˣ) (ℓ : ℕ), (Lev.u : LL) = algebraMap O LL (u : O) →
    (ℓ : LL) ≠ 0 → FactVval u ℓ → Lev.FactV

def kapExp (ℓ E : ℕ) (JS : Finset ℤ) : ℕ :=
  E + ∑ i ∈ JS.erase 0, (1 + E + padicValInt ℓ i)

def PPvalOf : Prop :=
  ∀ (O : Type) [CommRing O] (u : Oˣ) (ℓ E kap : ℕ) (JS JS' : Finset ℤ), ℓ.Prime → FactVval u ℓ →
    2 * E + ∑ i ∈ JS.erase 0, (1 + E + padicValInt ℓ i) +
      ∑ i ∈ JS'.erase 0, (1 + E + padicValInt ℓ i) ≤ 2 * kap →
    PPval ℓ kap (G.PPoly u ℓ E JS) (G.PPoly u ℓ E JS')

end Formalism.ExponentWindows.E
