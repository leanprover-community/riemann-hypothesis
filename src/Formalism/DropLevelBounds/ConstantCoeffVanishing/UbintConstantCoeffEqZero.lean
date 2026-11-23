module

public import Formalism.IncomingBounds.StatementThmP
public import Formalism.IncomingBounds.FlowDegreeBounds.ThmPExp
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

@[expose] public section

noncomputable section
open scoped BigOperators
open MvPowerSeries Finset

namespace Formalism.UnitaryBoundIntegral

open Formalism.IncomingBounds

section UBIntLemmas

variable {C : Type} [Field C] {σ : Type}

theorem ubint_mvExp_zero : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  change ∑ k ∈ Finset.range (m.degree + 1), coeff m ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C) =
    coeff m 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    simp at h

theorem ubint_mvExp_sum [CharZero C] {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 0) :
    mvExp (∑ i ∈ s, f i) = ∏ i ∈ s, mvExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ubint_mvExp_zero]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, constantCoeff (f i) = 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h0 : constantCoeff (∑ i ∈ s, f i) = 0 := by

      rw [map_sum]
      exact Finset.sum_eq_zero hs
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      expSeriesAdd C σ (f a) _ (hf a (Finset.mem_insert_self a s)) h0, ih hs]

end UBIntLemmas


variable {C : Type} [Field C] {n0 : ℕ}




variable {C : Type} [Field C] {n0 : ℕ}


end Formalism.UnitaryBoundIntegral
