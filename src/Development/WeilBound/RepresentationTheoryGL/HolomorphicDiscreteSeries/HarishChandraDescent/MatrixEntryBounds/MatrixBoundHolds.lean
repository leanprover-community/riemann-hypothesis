module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent
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

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

theorem matrix_bound_holds : MatBd := by
  intro n ε M _ _ E _ _ Λ A v hv hA hoff Y
  have hsplit : actM E Y v - (∑ c : Fin n, Y c c * (Λ c : ℂ)) • v
      = ∑ a : Fin n, ∑ b : Fin n, Y a b • (E a b v - if a = b then (Λ a : ℂ) • v else 0) := by
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, smul_sub,
      Finset.sum_sub_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_smul, mul_smul]
  rw [hsplit]
  have hb : ∀ a b : Fin n, ‖Y a b • (E a b v - if a = b then (Λ a : ℂ) • v else 0)‖
      ≤ ‖Y a b‖ * (A * ‖v‖) := by
    intro a b
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    by_cases hab : a = b
    · subst hab
      simp [hv a]
      positivity
    · simp only [hab, if_false, sub_zero]
      exact hoff a b hab
  calc _ ≤ ∑ a : Fin n, ‖∑ b : Fin n, Y a b • (E a b v - if a = b then (Λ a : ℂ) • v else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, ‖Y a b‖ * (A * ‖v‖) :=
        Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb a b)
    _ = _ := by simp only [Finset.sum_mul, mul_assoc]

end PositivityTheory.RgHe3
