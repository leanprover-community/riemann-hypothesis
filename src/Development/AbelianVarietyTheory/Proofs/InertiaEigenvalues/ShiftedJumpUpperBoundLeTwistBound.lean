module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntPts
public import Mathlib.Basic.Real.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory

open GlobalTheory.PositionData

theorem hS_le_bound : ∀ (t : ℕ) (up : Bool) (Fl Fc : Finset ℤ) (η S B W0 : ℝ), 1 ≤ t → (t : ℝ) ≤ η → 0 ≤ B → 0 ≤ S →
    (∀ z ∈ Fl, |(z : ℝ) - ((t : ℝ) - 1) / 2| ≤ η ∧ 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) →
    (∀ z ∈ Fc, W0 ≤ (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ≤ W0 + S + η + 1) →
    2 * B + (t : ℝ) / 2 + 3 ≤ W0 →
    ((GlobalTheory.PositionData.hS up t Fl Fc : ℕ) : ℝ) ≤ W0 + S + 2 * η + 3 := by
  intro t up Fl Fc η S B W0 ht htη hB hS0 hFl hFc hW
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hFl' : ∀ z ∈ Fl, ((t : ℝ) - 1) / 2 - η ≤ (z : ℝ) ∧ (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    intro z hz
    have h := (hFl z hz).1
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have castToNat : ∀ x : ℤ, ((x.toNat : ℕ) : ℝ) = max (x : ℝ) 0 := by
    intro x
    have h : ((x.toNat : ℕ) : ℤ) = max x 0 := Int.toNat_eq_max x
    rw [← Int.cast_natCast, h]
    push_cast
    rfl
  have hmn : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, a ≤ (y : ℝ)) →
      a ≤ ((s.min' H : ℤ) : ℝ) := fun s H a h => h _ (Finset.min'_mem s H)
  have hmx : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, (y : ℝ) ≤ a) →
      ((s.max' H : ℤ) : ℝ) ≤ a := fun s H a h => h _ (Finset.max'_mem s H)

  have hmxLo : ((mxLo t Fl : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    apply hmx
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · push_cast; linarith
    · exact (hFl' y hy).2
  cases up
  ·
    have hFc' : ∀ z ∈ Fc, ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ (z : ℝ) := by
      intro z hz
      have h := (hFc z hz).2
      simp only [Bool.false_eq_true, if_false] at h
      linarith
    have h1 : ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ ((mnAll Fl Fc : ℤ) : ℝ) := by
      apply hmn
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · push_cast; linarith
      · linarith [(hFl' y hy).1]
      · exact hFc' y hy
    have h0 : mnAll Fl Fc ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hw : ((wS false Fl Fc : ℕ) : ℤ) = 1 - mnAll Fl Fc := by
      simp only [wS, Bool.false_eq_true, if_false]
      exact Int.toNat_of_nonneg (by omega)
    simp only [PositionData.hS, Bool.false_eq_true, if_false]
    rw [castToNat, hw]
    apply max_le
    · push_cast; linarith
    · linarith
  ·
    have hFc' : ∀ z ∈ Fc, (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1 := by
      intro z hz
      have h := (hFc z hz).2
      simp only [if_true] at h
      linarith
    have h1 : ((mxAll t Fl Fc : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1 := by
      apply hmx
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · push_cast; linarith
      · linarith [(hFl' y hy).2]
      · exact hFc' y hy
    have h2 : ((t : ℝ) - 1) / 2 - η ≤ ((mnLo Fl : ℤ) : ℝ) := by
      apply hmn
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · push_cast; linarith
      · exact (hFl' y hy).1
    have h0 : mnLo Fl ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hw : ((wS true Fl Fc : ℕ) : ℤ) = 1 - mnLo Fl := by
      simp only [wS, if_true]
      exact Int.toNat_of_nonneg (by omega)
    simp only [PositionData.hS, if_true]
    rw [castToNat, hw]
    apply max_le
    · push_cast; linarith
    · linarith

end GlobalTheory
