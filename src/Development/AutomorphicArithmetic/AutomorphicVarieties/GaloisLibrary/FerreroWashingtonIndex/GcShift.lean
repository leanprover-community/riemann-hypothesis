module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcDiff
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.V.FW

private theorem gauss_count_shift_eq_sum (M c : ℕ) [NeZero M] (s : ZMod M) (hc : c.Coprime M) (n : ℕ) :
    gc M c s - gc M c (s - ((c * n : ℕ) : ZMod M)) =
      ∑ j ∈ Finset.range (c * n), if (j : ZMod M) = s then (1 - if c ∣ j then (c : ℤ) else 0) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := gcDiff M c (s - ((c * n : ℕ) : ZMod M)) hc
    have e : s - ((c * (n + 1) : ℕ) : ZMod M) = s - ((c * n : ℕ) : ZMod M) - c := by
      push_cast; ring
    rw [e, Nat.mul_succ, Finset.sum_range_add, ← ih]
    have key : (∑ j ∈ Finset.range c, if ((c * n + j : ℕ) : ZMod M) = s then
        (1 - if c ∣ c * n + j then (c : ℤ) else 0) else 0) =
        (∑ j ∈ Finset.range c, if (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) then 1 else 0) -
          if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0 := by
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · simp
      have h2 : (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) =
          ∑ j ∈ Finset.range c, if j = 0 then
            (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) else 0 := by
        rw [Finset.sum_ite_eq' (Finset.range c) 0]
        simp [hpos]
      rw [h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      have h3 : (((c * n + j : ℕ) : ZMod M) = s) ↔ (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) := by
        rw [Nat.cast_add, eq_sub_iff_add_eq']
      have h4 : c ∣ c * n + j ↔ j = 0 := by
        rw [Nat.dvd_add_right (dvd_mul_right c n)]
        exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hj', fun h => h ▸ dvd_zero c⟩
      simp only [h3, h4]
      generalize s - ((c * n : ℕ) : ZMod M) = t
      by_cases h0 : j = 0
      · subst h0
        by_cases ht : t = 0
        · simp [ht]
        · simp [ht, Ne.symm ht]
      · simp [h0]
    rw [key, ← h]
    ring

theorem UpperTheory.V.FW.gcShift :
    ∀ (M c F : ℕ) [NeZero M] (k : Type) [CommRing k] (Ψ : ZMod M → k) (s : ZMod M), c.Coprime M → (∀ x, Ψ (x + F) = Ψ x) → (gc M c s : k) * Ψ s - (gc M c (s - ((c * F : ℕ) : ZMod M)) : k) * Ψ (s - ((c * F : ℕ) : ZMod M)) = ∑ j ∈ Finset.range (c * F), if (j : ZMod M) = s then Ψ j * (1 - if c ∣ j then (c : k) else 0) else 0 := by
  intro M c F _ k _ Ψ s hc hΨ
  have hp : ∀ n : ℕ, Ψ (s - ((n * F : ℕ) : ZMod M)) = Ψ s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, ← hΨ (s - (((n + 1) * F : ℕ) : ZMod M))]
      congr 1
      push_cast; ring
  rw [hp c, ← sub_mul, ← Int.cast_sub, gauss_count_shift_eq_sum M c s hc F, Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ZMod M) = s
  · rw [if_pos h, if_pos h, h, mul_comm]
    by_cases h' : c ∣ j <;> simp [h']
  · simp [h]
