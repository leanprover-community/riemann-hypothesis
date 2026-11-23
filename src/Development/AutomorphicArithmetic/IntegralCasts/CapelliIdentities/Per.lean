module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace PeriodicSumRangeMul

private lemma per {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (h : ∀ (i : ℕ), g (i + P) = g i) (k x : ℕ) : g (k * P + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P + x = (k * P + x) + P by ring, h, ih]

end PeriodicSumRangeMul

theorem UpperTheory.Reformulated.B.Yra7.main :
    ∀ {N : Type} [inst : AddCommGroup N] (g : ℕ → N) (P : ℕ),
      (∀ (i : ℕ), g (i + P) = g i) → ∀ (k : ℕ), ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i := by
  intro N _ g P h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P = k * P + P by ring, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => PeriodicSumRangeMul.per g P h k x)
