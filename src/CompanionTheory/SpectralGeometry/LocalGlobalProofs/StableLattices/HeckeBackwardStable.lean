module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgHeckeBack

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk

variable {n : ℕ}

theorem tensVd_apply (X : GMod n) (a b : Fin n) (f : Fin n → X.V) (i : Fin n) :
    tensVd X.E a b f i = X.E a b (f i) - if i = b then f a else 0 := by
  by_cases h : i = b <;> simp [tensVd, h]

theorem eeVd_apply (X : GMod n) (f : Fin n → X.V) (a : Fin n) :
    eeVd X.E f a = -∑ c, X.E a c (f c) := by
  simp [eeVd]

theorem commute_tensVd_eeVd (X : GMod n) (c d : Fin n) : Commute (tensVd X.E c d) (eeVd X.E) := by
  refine LinearMap.ext fun f => funext fun a => ?_

  simp only [Module.End.mul_apply, tensVd_apply, eeVd_apply, map_neg, map_sum, map_sub]
  simp only [comm_apply X c d a _ _, sum_sub_distrib, sum_add_distrib, apply_ite (X.E a _), map_zero]
  by_cases h : a = d
  · subst h
    simp
    abel
  · simp [h, Ne.symm h]

theorem backStable : BackStable := fun _ X z a b _ hx =>
  Module.End.mapsTo_maxGenEigenspace_of_comm (commute_tensVd_eeVd X a b).symm (-z - cn _) hx

end GlobalTheory.CompanionTheory.RgHeckeBack
