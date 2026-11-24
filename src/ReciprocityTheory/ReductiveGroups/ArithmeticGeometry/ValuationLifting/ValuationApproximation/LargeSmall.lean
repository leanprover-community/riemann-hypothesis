module

public import Mathlib.RingTheory.Valuation.Basic
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

namespace ReciprocityTheory.ChartRestriction.G.Lift.VA

def PairSep : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ)) → (∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) →
    ∀ i j, i ≠ j → ∃ w, 1 < v i w ∧ v j w < 1

def LargeSmall : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, 1 < v i x) → (∀ i j, i ≠ j → ∃ w, 1 < v i w ∧ v j w < 1) →
    ∀ i, ∃ y, 1 < v i y ∧ ∀ j, j ≠ i → v j y < 1

def NearOne : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ y, 1 < v i y ∧ ∀ j, j ≠ i → v j y < 1) →
    ∀ i (ε : ι → WithZero (Multiplicative ℤ)), (∀ j, ε j ≠ 0) →
      ∃ z, v i z = 1 ∧ ∀ j, j ≠ i → v j z < ε j

def Assembly : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ)) →
    (∀ i (ε : ι → WithZero (Multiplicative ℤ)), (∀ j, ε j ≠ 0) →
      ∃ z, v i z = 1 ∧ ∀ j, j ≠ i → v j z < ε j) →
    ∀ n : ι → ℤ, ∃ x : Ω, ∀ i, v i x = WithZero.exp (n i)

end ReciprocityTheory.ChartRestriction.G.Lift.VA
