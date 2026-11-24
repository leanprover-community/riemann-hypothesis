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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NumRho
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.KhwLowKSubRootEqZero

@[expose] public section

noncomputable section

open Finset

namespace PositivityTheory.RgHe3.DropRoots

open ReciprocityTheory.ChartRestriction.DS

theorem abs_rhoC_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ (n : ℝ) / 2 := by
  unfold rhoC
  have h1 : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) ≤ n := by
    exact_mod_cast (card_filter_le _ _).trans (by simp)
  have h2 : ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) ≤ n := by
    exact_mod_cast (card_filter_le _ _).trans (by simp)
  have h3 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem dot_root {n : ℕ} (x : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) : dot x (root a b) = x a - x b := by
  simp [dot, root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

end PositivityTheory.RgHe3.DropRoots

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgHe3.DropRoots

theorem drop_holds : Drop := by
  intro n ε L a b hab
  unfold casValK
  have e : L - root a b + rhoC ε = (L + rhoC ε) - root a b := by
    funext c; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [e, nsq_sub', nsq_root hab, dot_root _ hab]
  have h1 := abs_rhoC_le ε a
  have h2 := abs_rhoC_le ε b
  simp only [Pi.add_apply]
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

end PositivityTheory.RgHe3
