module

public import Development.EtaleCohomology.EtaleSheaves.PartDiagCut
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace LateralTheory.E.PartDirectedPf

variable {A : Type} [CommRing A]

theorem prod_eq_zero_of_ne {a b c d : A} (P Q : PartDiagCut.Part A)
    (ha : a ∈ P.blocks) (hb : b ∈ Q.blocks) (hc : c ∈ P.blocks) (hd : d ∈ Q.blocks)
    (hne : (a, b) ≠ (c, d)) : (a * b) * (c * d) = 0 := by
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h; exact hne (by rw [hac, h])
    have := Q.orth b hb d hd hbd
    calc a * b * (c * d) = a * c * (b * d) := by ring
      _ = 0 := by rw [this, mul_zero]
  · have := P.orth a ha c hc hac
    calc a * b * (c * d) = a * c * (b * d) := by ring
      _ = 0 := by rw [this, zero_mul]

open Classical in
noncomputable def meet (P Q : PartDiagCut.Part A) : PartDiagCut.Part A where
  blocks := ((P.blocks ×ˢ Q.blocks).filter (fun x => x.1 * x.2 ≠ 0)).image (fun x => x.1 * x.2)
  idem := by
    intro e he
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hne⟩, rfl⟩ := he
    exact ⟨(P.idem a ha).1.mul (Q.idem b hb).1, hne⟩
  orth := by
    intro e he e' he' hee
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he he'
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
    obtain ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, _⟩, rfl⟩ := he'
    refine prod_eq_zero_of_ne P Q ha hb hc hd ?_
    intro h; apply hee; simp only [Prod.mk.injEq] at h; rw [h.1, h.2]
  sum_eq := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter_ne_zero, Finset.sum_product, ← Finset.sum_mul_sum,
        P.sum_eq, Q.sum_eq, mul_one]
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
      by_contra hne
      have h0 := prod_eq_zero_of_ne P Q hx.1.1 hx.1.2 hy.1.1 hy.1.2 hne
      change x.1 * x.2 = y.1 * y.2 at hxy
      rw [← hxy] at h0
      have hid : IsIdempotentElem (x.1 * x.2) := (P.idem _ hx.1.1).1.mul (Q.idem _ hx.1.2).1
      exact hx.2 (by rw [← hid.eq]; exact h0)

theorem le_meet_left (P Q : PartDiagCut.Part A) : P ≤ meet P Q := by
  intro e he
  simp only [meet, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
  refine ⟨a, ha, ?_⟩
  calc a * b * a = a * a * b := by ring
    _ = a * b := by rw [(P.idem a ha).1.eq]

theorem le_meet_right (P Q : PartDiagCut.Part A) : Q ≤ meet P Q := by
  intro e he
  simp only [meet, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
  refine ⟨b, hb, ?_⟩
  calc a * b * b = a * (b * b) := by ring
    _ = a * b := by rw [(Q.idem b hb).1.eq]

theorem part_nonempty (A : Type) [CommRing A] : Nonempty (PartDiagCut.Part A) := by
  by_cases h : Nontrivial A
  · exact ⟨{ blocks := {1}
             idem := by intro e he; rw [Finset.mem_singleton] at he; subst he; exact ⟨IsIdempotentElem.one, one_ne_zero⟩
             orth := by intro e he e' he' hne; rw [Finset.mem_singleton] at he he'; exact absurd (he.trans he'.symm) hne
             sum_eq := by simp }⟩
  · rw [not_nontrivial_iff_subsingleton] at h
    exact ⟨{ blocks := ∅
             idem := by simp
             orth := by simp
             sum_eq := Subsingleton.elim _ _ }⟩

theorem PartDirected_of : LateralTheory.E.PartDiagCut.PartDirected := by
  intro A _
  exact ⟨⟨fun P Q => ⟨meet P Q, le_meet_left P Q, le_meet_right P Q⟩⟩, part_nonempty A⟩

end LateralTheory.E.PartDirectedPf
