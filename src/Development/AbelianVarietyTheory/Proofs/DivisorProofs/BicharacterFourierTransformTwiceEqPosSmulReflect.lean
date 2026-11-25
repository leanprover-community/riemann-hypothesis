module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology

noncomputable section
namespace GlobalTheory.KSp.FourInv

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}

theorem ne_zero (he : IsPair e) (x y : X) : e x y ≠ 0 := by
  intro h
  have h1 := he.norm x y
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem add_right (he : IsPair e) (x y y' : X) : e x (y + y') = e x y * e x y' := by
  rw [he.symm x (y + y'), he.add y y' x, he.symm y x, he.symm y' x]

theorem zero_right (he : IsPair e) (x : X) : e x 0 = 1 := by
  have h := add_right he x 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (ne_zero he x 0) (by rw [mul_one]; exact h.symm)

def ann (he : IsPair e) (L : Set X) : AddSubgroup X where
  carrier := {z | ∀ y ∈ L, e y z = 1}
  zero_mem' := fun y _ => zero_right he y
  add_mem' := fun {a b} ha hb y hy => by rw [add_right he, ha y hy, hb y hy, one_mul]
  neg_mem' := fun {a} ha y hy => by
    have h := add_right he y a (-a)
    rw [add_neg_cancel, zero_right he, ha y hy, one_mul] at h
    exact h.symm

end GlobalTheory.KSp.FourInv

end
