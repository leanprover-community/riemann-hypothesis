module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegreeSteps
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module Set

theorem SpanningExtension.proof : SpanningExtension.Statement := by
  intro V _ _ _ ι _ v S hv hS
  classical
  set s : Set V := range v with hs_def
  have hs : LinearIndepOn ℝ id s := (linearIndepOn_id_range_iff hv.injective).mpr hv
  have hst : s ⊆ s ∪ S := subset_union_left
  set b := hs.extend hst with hb_def
  have hsb : s ⊆ b := hs.subset_extend hst
  have hbt : b ⊆ s ∪ S := hs.extend_subset hst
  have hbli : LinearIndependent ℝ (fun x : b => (x : V)) := hs.linearIndepOn_extend hst
  have hspan : ⊤ ≤ Submodule.span ℝ (range (fun x : b => (x : V))) := by
    rw [Subtype.range_coe, ← hS]
    exact Submodule.span_le.2 (subset_union_right.trans (hs.subset_span_extend hst))
  let B := Basis.mk hbli hspan
  have hcard_b : Nat.card b = finrank ℝ V := (finrank_eq_nat_card_basis B).symm
  have : Finite b := Module.Finite.finite_basis B
  have hbfin : b.Finite := toFinite b
  have hcard_s : s.ncard = Fintype.card ι := by
    rw [hs_def, ncard_range_of_injective hv.injective, Nat.card_eq_fintype_card]
  have hk : Nat.card (b \ s : Set V) = finrank ℝ V - Fintype.card ι := by
    rw [Nat.card_coe_set_eq, ncard_sdiff hsb (hbfin.subset hsb), ← hcard_s, ← Nat.card_coe_set_eq,
      hcard_b]
  let e : (b \ s : Set V) ≃ Fin (finrank ℝ V - Fintype.card ι) := Finite.equivFinOfCardEq hk
  let w : Fin (finrank ℝ V - Fintype.card ι) → V := fun j => (e.symm j : V)
  have hw_mem : ∀ j, w j ∈ b \ s := fun j => (e.symm j).2
  refine ⟨w, fun j => ?_, ?_⟩
  · obtain ⟨hb, hns⟩ := hw_mem j
    rcases hbt hb with h | h
    · exact absurd h hns
    · exact h
  · let f : ι ⊕ Fin (finrank ℝ V - Fintype.card ι) → b :=
      Sum.elim (fun i => ⟨v i, hsb (mem_range_self i)⟩) (fun j => ⟨w j, (hw_mem j).1⟩)
    have hf : Function.Injective f := by
      rintro (i | j) (i' | j') h <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      · rw [hv.injective h]
      · exact absurd (h ▸ mem_range_self i) (hw_mem j').2
      · exact absurd (h ▸ mem_range_self i') (hw_mem j).2
      · rw [e.symm.injective (Subtype.ext h)]
    have : Sum.elim v w = (fun x : b => (x : V)) ∘ f := by
      funext x; rcases x with i | j <;> rfl
    rw [this]
    exact hbli.comp f hf

end GroundTheory.Heights₂.Heights.HilbertSamuel
