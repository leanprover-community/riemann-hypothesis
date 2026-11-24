module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem Comb.pcnt_succ_self {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := by
  unfold pcnt
  have hins : (univ.filter (fun s : Fin n => (s : ℕ) < (t : ℕ) + 1 ∧ w s = w t)) =
      insert t (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = w t)) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl (Fin.ext h)
    · rintro (h | ⟨h1, h2⟩)
      · subst h; exact ⟨Nat.lt_succ_self _, rfl⟩
      · exact ⟨Nat.lt_succ_of_lt h1, h2⟩
  rw [hins, card_insert_of_notMem]
  simp

theorem CombCellOfWordMono.proof : CombCellOfWordMono.Statement := by
  intro m n w hw s t hrow hcol
  by_contra hst
  rw [not_le] at hst
  simp only [cellOfWord] at hrow hcol
  have h1 : pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := Comb.pcnt_succ_self w t
  have h2 : pcnt w ((t : ℕ) + 1) (w s) ≤ pcnt w s (w s) :=
    pcnt_le_of_le w (Nat.succ_le_of_lt hst) (w s)
  have h3 : pcnt w ((t : ℕ) + 1) (w t) ≤ pcnt w ((t : ℕ) + 1) (w s) :=
    hw _ (by have := s.isLt; have : (t : ℕ) < s := hst; omega) (w s) (w t) hrow
  omega

end GroundTheory.Heights₂.Heights.RestTerms
