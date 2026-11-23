module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

private theorem UpperTheory.cardinal_sum_eq_finite_sum_range (N : ℕ) : ∀ f : ℕ → Cardinal.{0}, (∀ q, N ≤ q → f q = 0) →
    Cardinal.sum f = ∑ q ∈ Finset.range N, f q := by
  induction N with
  | zero =>
    intro f hf
    have hf0 : f = fun _ => 0 := funext fun q => hf q (Nat.zero_le q)
    subst hf0
    rw [Cardinal.sum_const', mul_zero, Finset.sum_range_zero]
  | succ N ih =>
    intro f hf
    rw [Cardinal.sum_nat_eq_add_sum_succ, ih (fun i => f (i+1)) (fun q hq => hf (q+1) (by omega)),
      Finset.sum_range_succ', add_comm]

theorem UpperTheory.adelic_rep_bounded_of_degree_bounded :
    UpperTheory.V.Af.BA.BddOfDeg := by
  unfold UpperTheory.V.Af.BA.BddOfDeg
  intro Γ _ hc hD
  choose c hc using hc
  obtain ⟨D, hD⟩ := hD
  unfold UpperTheory.V.Af.CohB.Bdd
  refine ⟨∑ q ∈ Finset.range D, c q, fun A => ?_⟩
  unfold UpperTheory.V.Af.CohB.totCoh
  rw [UpperTheory.cardinal_sum_eq_finite_sum_range D _ (fun q hq => hD q hq A), Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun q _ => hc q A
