module

public import Formalism.PieriBlockIdeals.ContentDistanceBounds
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

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

theorem windowResidueCountEqZero_holds : NoResidue := by
  intro l b t κ U hU
  rw [mwCount]
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_of_forall_notMem
  intro u hu'
  simp only [Finset.mem_filter] at hu'
  obtain ⟨hu, x, hx, hxu⟩ := hu'
  have hd : (l : ℤ) ∣ u - x := Int.ModEq.dvd hxu
  rcases hU u hu.1 hu.2 x hx with ⟨h1, h2⟩ | h
  · have h0 := Int.eq_zero_of_abs_lt_dvd hd h2
    rw [h0, abs_zero] at h1
    exact lt_irrefl 0 h1
  · exact h hd

end Formalism.CohomologicalDescent
