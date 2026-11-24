module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem embMem : EmbMem := by
  intro L _ _ σ n r e β γ ι hσ hD hι g
  obtain ⟨he, -, -, -, -, hβγ⟩ := hD
  obtain ⟨h1, h2⟩ := hι g
  have hcases : ∀ a b : Fin n, (∃ i j, a = e i ∧ b = e j) ∨ (a ∉ Set.range e ∨ b ∉ Set.range e) := by
    intro a b
    by_cases ha : a ∈ Set.range e
    · by_cases hb : b ∈ Set.range e
      · obtain ⟨i, rfl⟩ := ha
        obtain ⟨j, rfl⟩ := hb
        exact Or.inl ⟨i, j, rfl, rfl⟩
      · exact Or.inr (Or.inr hb)
    · exact Or.inr (Or.inl ha)
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_KU_iff hσ, mem_KU_iff hσ]
    refine ⟨fun h i j => h1 i j ▸ h (e i) (e j), fun h a b => ?_⟩
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | hab
    · rw [h1]; exact h i j
    · rw [h2 a b hab, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · rw [h1]
      exact hg i j fun hij => hab ((hβγ i j).2 hij)
    · rw [h2 a b h]
      exact Matrix.one_apply_ne fun h' => hab (h' ▸ rfl)
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · have hji : j ≤ i := he.le_iff_le.1 hab
      rw [h1, hg i j hji, Matrix.one_apply, Matrix.one_apply]
      simp only [he.injective.eq_iff]
    · exact h2 a b h

end GlobalTheory.SatakeWeyl
