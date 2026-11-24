module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory.CompanionTheory.RgPath

open CompanionTheory.RgExh

theorem pathEnd_eq_add_nat {n : ℕ} (ss : List (_root_.Fin n)) :
    ∀ χ : _root_.Fin n → ℂ, ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a := by
  induction ss with
  | nil =>
    intro χ
    refine ⟨0, ?_, by simp⟩
    funext a
    change χ a = χ a + (↑(0 : ℕ) : ℂ)
    simp
  | cons s ss ih =>
    intro χ
    obtain ⟨m', h, hm⟩ := ih (χ + Pi.single s 1)
    refine ⟨m' + Pi.single s 1, ?_, ?_⟩
    · change pathEnd (χ + Pi.single s 1) ss = _
      rw [h]
      funext a
      by_cases e : a = s
      · subst a
        simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_add, Nat.cast_one]
        ac_rfl
      · simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]
    · intro a ha
      rcases List.mem_cons.1 ha with e | ha
      · subst a
        simpa only [Pi.add_apply, Pi.single_eq_same] using Nat.succ_le_succ (Nat.zero_le (m' s))
      · exact (hm a ha).trans (Nat.le_add_right _ _)

theorem pathEndNat (n : ℕ) (χ : _root_.Fin n → ℂ) (ss : List (_root_.Fin n)) :
    ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a :=
  pathEnd_eq_add_nat ss χ

end GlobalTheory.CompanionTheory.RgPath
