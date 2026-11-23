module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.SetTheory.Cardinal.Finite
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
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

namespace GlobalTheory.CompanionTheory.Counting

theorem card_eq_card_ker_mul_card_range (R A B : Type) [Ring R] [AddCommGroup A] [Module R A] [Finite A]
    [AddCommGroup B] [Module R B] (f : A →ₗ[R] B) :
    Nat.card A = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f) := by
  have h1 : Nat.card (A ⧸ LinearMap.ker f) = Nat.card ↥(LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have h2 : Nat.card A = Nat.card (A ⧸ (LinearMap.ker f).toAddSubgroup) * Nat.card (LinearMap.ker f).toAddSubgroup :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h3 : Nat.card (A ⧸ (LinearMap.ker f).toAddSubgroup) = Nat.card (A ⧸ LinearMap.ker f) := rfl
  have h4 : Nat.card (LinearMap.ker f).toAddSubgroup = Nat.card ↥(LinearMap.ker f) := rfl
  rw [h2, h3, h4, h1, Nat.mul_comm]

end GlobalTheory.CompanionTheory.Counting
