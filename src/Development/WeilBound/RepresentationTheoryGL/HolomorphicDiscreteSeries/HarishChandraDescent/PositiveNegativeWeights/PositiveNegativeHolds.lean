module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

theorem positive_negative_holds : PosNeg := by
  intro H _ _ _ a ha
  refine ⟨cfc (fun x : ℝ => max x 0) a, cfc (fun x : ℝ => max (-x) 0) a, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cfc_sub (fun x : ℝ => max x 0) (fun x : ℝ => max (-x) 0) a]
    conv_lhs => rw [← cfc_id' ℝ a]
    refine cfc_congr fun x _ => ?_
    exact (max_zero_sub_eq_self x).symm
  · rw [← cfc_mul (fun x : ℝ => max (-x) 0) (fun x : ℝ => max x 0) a]
    rw [← cfc_zero ℝ a]
    refine cfc_congr fun x _ => ?_
    rcases le_total x 0 with h | h
    · simp [max_eq_right h]
    · simp [max_eq_right (neg_nonpos.mpr h)]
  · intro x
    have hp : 0 ≤ cfc (fun x : ℝ => max x 0) a := cfc_nonneg fun y _ => le_max_right _ _
    exact ((ContinuousLinearMap.nonneg_iff_isPositive).mp hp).re_inner_nonneg_left x
  · intro x
    have hm : 0 ≤ cfc (fun x : ℝ => max (-x) 0) a := cfc_nonneg fun y _ => le_max_right _ _
    exact ((ContinuousLinearMap.nonneg_iff_isPositive).mp hm).re_inner_nonneg_left x
  · intro S hS
    exact ⟨hS.cfc_real _, hS.cfc_real _⟩

end PositivityTheory.RgHe3
