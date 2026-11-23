module

public import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)

theorem column_top_entry : LastColumnBound := by
  intro κ lam A bt S hbt hS h0 hl hmid
  have hsucc : ∀ j : Fin (κ + 1), lam j.succ ≤ S := by
    intro j
    by_cases hj : j.succ = Fin.last (κ + 1)
    · rw [hj, hl]; linarith
    · exact (hmid j.succ (Fin.succ_ne_zero j) hj).2
  have hsum : ∑ j : Fin (κ + 1), lam j.succ ≤ (κ + 1) * S := by
    calc ∑ j : Fin (κ + 1), lam j.succ ≤ ∑ _j : Fin (κ + 1), S := Finset.sum_le_sum fun j _ => hsucc j
      _ = (κ + 1) * S := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  constructor
  · unfold wt
    rw [Fin.sum_univ_succ, h0]
    nlinarith
  · unfold wt plus
    rw [Fin.sum_univ_succ, h0, hl]
    have e : ∑ j : Fin (κ + 1), (lam j.succ - -bt) = ∑ j : Fin (κ + 1), lam j.succ + (κ + 1) * bt := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    nlinarith

end Formalism.HermitianLattices.TraceIntegrality
