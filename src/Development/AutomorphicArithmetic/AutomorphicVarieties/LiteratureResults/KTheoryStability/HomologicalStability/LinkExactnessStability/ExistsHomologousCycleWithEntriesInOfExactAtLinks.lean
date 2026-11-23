module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainBoundaryCompBoundaryApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainCycleRetractionOfLinkExact
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

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem exists_sub_bd_mem_chains_linkIn_nil :
    ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ),
      (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length ≤ p →
        ExactAt (linkIn F S τ) (p - τ.length)) →
      ∀ c ∈ chains F p, bd V c = 0 →
        ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains (linkIn F S []) p ∧ bd V (c - bd V b) = 0 := by
  intro V F S hF p hex
  have key : ∀ k : ℕ, ∀ c ∈ chains {l ∈ F | ∀ y ∈ l.drop k, y ∈ S} p, bd V c = 0 →
      ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains (linkIn F S []) p := by
    intro k
    induction k with
    | zero =>
      intro c hc _
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero, sub_zero]
      refine Finsupp.supported_mono ?_ hc
      rintro l ⟨⟨hl, hS⟩, hp⟩
      exact ⟨⟨by simpa using hS, by simpa using hl⟩, hp⟩
    | succ k ih =>
      intro c hc h0
      obtain ⟨b, hb, hcb⟩ := GlobalTheory.T.seqChain_cycle_retraction_of_link_exact V F S hF p k
        (fun τ hτ x hx hxS _ hle => hex τ hτ x hx hxS hle) c hc h0
      obtain ⟨b', hb', hcb'⟩ := ih (c - bd V b) hcb
        (by rw [map_sub, h0, GlobalTheory.T.seqChain_boundary_comp_boundary_apply, sub_zero])
      refine ⟨b + b', Submodule.add_mem _ hb hb', ?_⟩
      rw [map_add (f := _), ← sub_sub]
      exact hcb'
  intro c hc h0
  have hc' : c ∈ chains {l ∈ F | ∀ y ∈ l.drop p, y ∈ S} p := by
    refine Finsupp.supported_mono ?_ hc
    rintro l ⟨hl, hp⟩
    refine ⟨⟨hl, ?_⟩, hp⟩
    intro y hy
    rw [List.drop_eq_nil_of_le hp.le] at hy
    simp at hy
  obtain ⟨b, hb, hcb⟩ := key p c hc' h0
  exact ⟨b, hb, hcb, by rw [map_sub, h0, GlobalTheory.T.seqChain_boundary_comp_boundary_apply, sub_zero]⟩

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exists_homologous_cycle_with_entries_in_of_exactAt_links : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ), (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ∀ c ∈ chains F p, bd V c = 0 → ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains (linkIn F S []) p ∧ bd V (c - bd V b) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.exists_sub_bd_mem_chains_linkIn_nil
end
