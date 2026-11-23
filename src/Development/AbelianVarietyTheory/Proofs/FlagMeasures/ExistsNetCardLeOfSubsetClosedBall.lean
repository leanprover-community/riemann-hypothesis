module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteInterClosedBallOfSeparated
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

open Metric

namespace GlobalTheory

theorem exists_net_card_le_of_subset_closedBall :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (S : Set E)
      (R δ : ℝ), 0 < δ → 0 ≤ R → S ⊆ closedBall 0 R →
      ∃ T : Finset E, (T : Set E) ⊆ S ∧ (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E ∧
        ∀ x ∈ S, ∃ t ∈ T, dist x t ≤ δ := by
  intro E _ _ _ S R δ hδ hR hS
  classical
  let P : Finset E → Prop := fun T =>
    (T : Set E) ⊆ S ∧ (T : Set E).Pairwise fun a b => δ ≤ dist a b
  have hb : ∀ T, P T → (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E := fun T hT =>
    finset_card_le_of_separated T hδ hR 0 (fun a ha => hS (hT.1 ha)) hT.2
  obtain ⟨N, hN⟩ := exists_nat_ge ((1 + 2 * R / δ) ^ Module.finrank ℝ E)
  let Q : ℕ → Prop := fun n => ∃ T, P T ∧ T.card = n
  have hQ0 : Q 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨T, hT, hTc⟩ : Q (Nat.findGreatest Q N) := Nat.findGreatest_spec (Nat.zero_le N) hQ0
  refine ⟨T, hT.1, hb T hT, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hxT : x ∉ T := fun h => by
    have := hcon x h
    rw [dist_self] at this
    linarith
  have hP : P (insert x T) := by
    refine ⟨?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hx hT.1
    · rw [Finset.coe_insert]
      refine hT.2.insert fun b hb' _ => ⟨(hcon b hb').le, ?_⟩
      rw [dist_comm]
      exact (hcon b hb').le
  have hle : (insert x T).card ≤ N := by
    exact_mod_cast (hb _ hP).trans hN
  have := Nat.le_findGreatest (P := Q) hle ⟨_, hP, rfl⟩
  rw [Finset.card_insert_of_notMem hxT] at this
  omega

end GlobalTheory
