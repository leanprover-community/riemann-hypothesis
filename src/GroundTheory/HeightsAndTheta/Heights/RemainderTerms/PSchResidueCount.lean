module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchResidueCount.proof : SchResidueCount.Statement := by
  intro k l hlt hinj
  have hsplit : ∀ i, l i = l i % k + k * (if k ≤ l i then 1 else 0) := by
    intro i
    have hi := hlt i
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  have himg : (univ.image fun i => l i % k) = range k := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [mem_image, mem_univ, true_and] at hc
      obtain ⟨i, rfl⟩ := hc
      exact mem_range.2 (Nat.mod_lt _ i.pos)
    · rw [card_image_of_injective _ hinj, card_range, card_univ, Fintype.card_fin]
  have hres : ∑ i, l i % k = k * (k - 1) / 2 := by
    rw [← sum_range_id, ← himg, sum_image (fun i _ j _ h => hinj h)]
  calc ∑ i, l i = ∑ i, (l i % k + k * (if k ≤ l i then 1 else 0)) :=
        sum_congr rfl (fun i _ => hsplit i)
    _ = ∑ i, l i % k + k * (univ.filter fun i => k ≤ l i).card := by
        rw [sum_add_distrib, ← mul_sum, sum_boole, Nat.cast_id]
    _ = k * (k - 1) / 2 + k * (univ.filter fun i => k ≤ l i).card := by
        rw [hres]

end GroundTheory.Heights₂.Heights.RestTerms
