module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Filtration

@[expose] public section

namespace GlobalTheory

theorem compact_dvr_complete_separated : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ϖ : O), Irreducible ϖ → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  intro O _ _ _ _ _ _ _ _ ϖ hϖ
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · set s : ℕ → O := fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j with hs
    let C : ℕ → Set O := fun n => Set.range (fun b : O => s n + ϖ ^ n * b)
    have hcpt : ∀ n, IsCompact (C n) := fun n =>
      isCompact_range (continuous_const.add (continuous_const.mul continuous_id))
    have hdec : ∀ n, C (n + 1) ⊆ C n := by
      intro n y ⟨b, hb⟩
      refine ⟨x n + ϖ * b, ?_⟩
      rw [← hb]
      simp only [hs, Finset.sum_range_succ, pow_succ]
      ring
    have hne : ∀ n, (C n).Nonempty := fun n => ⟨_, ⟨0, rfl⟩⟩
    obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hne
      (hcpt 0) (fun n => (hcpt n).isClosed)
    refine ⟨a, fun n => ?_⟩
    obtain ⟨b, hb⟩ := Set.mem_iInter.mp ha n
    exact ⟨b, by rw [← hb]; simp [hs]⟩
  · have hne : Ideal.span {ϖ} ≠ (⊤ : Ideal O) := by
      rw [Ne, Ideal.span_singleton_eq_top]; exact hϖ.not_isUnit
    have h := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {ϖ}) hne
    have : a ∈ ⨅ i, (Ideal.span {ϖ}) ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      obtain ⟨b, hb⟩ := ha i
      rw [Ideal.span_singleton_pow, hb]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [h] at this
    exact (Submodule.mem_bot O).mp this

end GlobalTheory
