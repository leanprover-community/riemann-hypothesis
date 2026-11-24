module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace GlobalTheory.PositiveIffLtCard

theorem pos_iff_lt_card {N : ℕ} {e : Fin N → ℤ} (he : Antitone e) (i : Fin N) :
    (0 : ℤ) < e i ↔ (i : ℕ) < Finset.card {j : Fin N | (0 : ℤ) < e j} := by
  constructor
  · intro h
    have hsub : Finset.Iic i ⊆ ({j : Fin N | (0 : ℤ) < e j} : Finset (Fin N)) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_lt_of_le h (he hj)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro h
    by_contra hn
    have hsub : ({j : Fin N | (0 : ℤ) < e j} : Finset (Fin N)) ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hji
      exact hn (lt_of_lt_of_le hj (he (not_lt.mp hji)))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

end GlobalTheory.PositiveIffLtCard
