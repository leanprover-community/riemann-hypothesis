module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
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
public import Mathlib.Combinatorics.Nullstellensatz
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

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

theorem EventuallyPolyUnique.proof : EventuallyPolyUnique.Statement := by
  intro K _ h p q hp hq
  classical
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (hp.and hq)
  have hpq : p - q = 0 := by
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset (p - q)
      (fun k => (Finset.range ((p - q).degreeOf k + 1)).image
        (fun i : ℕ => ((M k + (i : ℤ) : ℤ) : ℚ)))
    · intro k
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b hab
        simpa using hab
    · intro x hx
      choose i _ hix using fun k => Finset.mem_image.1 (hx k)
      have hm : M ≤ fun k => M k + (i k : ℤ) := fun k => by simp
      have hxm : x = fun k => (((M k + (i k : ℤ) : ℤ)) : ℚ) := funext fun k => (hix k).symm
      obtain ⟨h1, h2⟩ := hM _ hm
      rw [map_sub, hxm, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 hpq

end GroundTheory.Heights₂.Heights.FieldNumbers
