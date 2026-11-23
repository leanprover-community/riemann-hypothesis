module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem FlagInjSumBound.finset_sum_bound (S : Finset ℕ) :
    ∑ i ∈ Finset.range S.card, i ≤ ∑ x ∈ S, x ∧
      (∑ x ∈ S, x = ∑ i ∈ Finset.range S.card, i → S ⊆ Finset.range S.card) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m S' hlt ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hm : m ∉ S' := fun h => lt_irrefl m (hlt m h)
    have hsub : S' ⊆ Finset.range m := fun x hx => Finset.mem_range.2 (hlt x hx)
    have hcard : S'.card ≤ m := by simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hm, Finset.sum_range_succ, Finset.sum_insert hm]
    refine ⟨by omega, fun heq => ?_⟩
    have hmeq : m = S'.card := by omega
    have hS' := ih₂ (by omega)
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_range.2 (by omega)
    · exact Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hS' hx)))

theorem FlagInjSumBound.proof : FlagInjSumBound.Statement := by
  intro N g hg
  classical
  set S := Finset.univ.image g with hSdef
  have hcard : S.card = N := by
    rw [hSdef, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i, g i = ∑ x ∈ S, x := by
    rw [hSdef, Finset.sum_image (fun i _ j _ h => hg h)]
  obtain ⟨h₁, h₂⟩ := FlagInjSumBound.finset_sum_bound S
  rw [hcard, Finset.sum_range_id] at h₁ h₂
  rw [hsum]
  refine ⟨h₁, fun heq i => ?_⟩
  have hi : g i ∈ S := Finset.mem_image_of_mem g (Finset.mem_univ i)
  exact Finset.mem_range.1 (h₂ heq hi)

end RestTerms

end GroundTheory.Heights₂.Heights
