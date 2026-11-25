module

public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
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

namespace GlobalTheory.ScalarStatement

open Formalism.L2.FormalSeriesBounds

theorem main : (let d1 : {C : Type} → [inst : Field C] → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → C) → Prop := @(fun {C : Type} [Field C] (V : Formalism.L2.FormalSeriesBounds.VF C) (s : ℕ → C) ↦ ∃ (K : ℝ), ∀ (n : ℕ), Formalism.L2.FormalSeriesBounds.VF.Ge V K (s n)); ∀ {C : Type} [inst : Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {ι : Type} (S : Finset ι) {s : ι → ℕ → C}, (∀ i ∈ S, d1 V (s i)) → d1 V fun (n : ℕ) ↦ ∑ i ∈ S, s i n) := by
  intro d1 C _ V ι S s h
  classical
  have h' : ∀ i, ∃ K : ℝ, i ∈ S → ∀ n, Formalism.L2.FormalSeriesBounds.VF.Ge V K (s i n) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨K, hK⟩ := h i hi
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose K hK using h'
  refine ⟨-(∑ i ∈ S, |K i|), fun n => ?_⟩
  refine Formalism.L2.FormalSeriesBounds.VF.Ge.sum fun i hi => (hK i hi n).mono ?_
  have h1 : |K i| ≤ ∑ j ∈ S, |K j| :=
    Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) hi
  have h2 : -|K i| ≤ K i := neg_abs_le _
  linarith

end GlobalTheory.ScalarStatement
