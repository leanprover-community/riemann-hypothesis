module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem prod_eq_zero_of_succ_le {I : Type} {D : Type} [CommRing D] (N : ℕ) (t : I → D)
    (h : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (k : ℕ) (hk : N + 1 ≤ k) (s : Fin k → I) :
    ∏ a, t (s a) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Fin.prod_univ_add, h (fun a => s (Fin.castAdd j a)), zero_mul]

theorem taylor_eq_of_le : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (N' : ℕ), N ≤ N' → ∀ f : (I → ℂ) → ℂ, GlobalTheory.PeriodFamily.taylor N' t f = GlobalTheory.PeriodFamily.taylor N t f := by
  intro I _ _ D _ _ N t h N' hN f
  induction N', hN using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← ih]
    unfold taylor
    rw [Finset.sum_range_succ _ (n + 1)]
    simp [prod_eq_zero_of_succ_le N t h (n + 1) (by omega)]

end GlobalTheory.PeriodFamily
