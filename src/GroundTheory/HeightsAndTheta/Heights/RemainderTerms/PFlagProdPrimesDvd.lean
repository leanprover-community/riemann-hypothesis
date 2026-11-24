module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

theorem FlagProdPrimesDvd.proof : FlagProdPrimesDvd.Statement := by
  intro R _ _ ι s p x
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert t s ht ih =>
    intro hp hne hdvd
    have hs : (∏ i ∈ s, p i) ∣ x :=
      ih (fun i hi => hp i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hne i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
        (fun i hi => hdvd i (mem_insert_of_mem hi))
    obtain ⟨y, hy⟩ := hs
    have hpt : Prime (p t) := hp t (mem_insert_self t s)
    have hnd : ¬ p t ∣ ∏ i ∈ s, p i := by
      rw [Prime.dvd_finsetProd_iff hpt]
      rintro ⟨j, hj, hdj⟩
      refine hne t (mem_insert_self t s) j (mem_insert_of_mem hj) ?_ hdj
      rintro rfl
      exact ht hj
    have hty : p t ∣ y := by
      have h := hdvd t (mem_insert_self t s)
      rw [hy] at h
      exact (hpt.dvd_or_dvd h).resolve_left hnd
    rw [prod_insert ht, hy, mul_comm (p t)]
    exact mul_dvd_mul_left _ hty

end RestTerms

end GroundTheory.Heights₂.Heights
