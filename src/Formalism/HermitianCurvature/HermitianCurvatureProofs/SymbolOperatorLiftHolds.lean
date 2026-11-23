module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def liftA {d o : ℕ} (a : (k : Fin (o + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ) (m' : ℕ) :
    (k : Fin (m' + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ :=
  fun k w x => if h : (k : ℕ) ≤ o then a ⟨k, by omega⟩ w x else 0

theorem symbol_operator_lift_holds : SOpLift := by
  intro d S m' O hle hS
  obtain ⟨o, a⟩ := S
  simp only at hle
  refine ⟨⟨m', liftA a m'⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    change ContDiffOn ℝ ∞ (liftA a m' i w) O
    by_cases h : (i : ℕ) ≤ o
    · have e : liftA a m' i w = a ⟨i, by omega⟩ w := funext fun x => dif_pos h
      rw [e]
      exact hS (⟨i, Nat.lt_succ_of_le h⟩ : Fin (o + 1)) w
    · have e : liftA a m' i w = fun _ => 0 := funext fun x => dif_neg h
      rw [e]
      exact contDiffOn_const
  · intro u x
    simp only [SOp.app]
    let F : ℕ → ℂ := fun n =>
      if h : n ≤ o then ∑ w : Fin n → Fin d, a ⟨n, by omega⟩ w x * pdc (List.ofFn w) u x else 0
    have h1 : ∑ k : Fin (m' + 1), ∑ w : Fin k → Fin d, liftA a m' k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (m' + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F, liftA]
      split_ifs with h
      · rfl
      · simp
    have h2 : ∑ k : Fin (o + 1), ∑ w : Fin k → Fin d, a k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (o + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F]
      rw [dif_pos (by omega)]
    rw [h1, h2, Fin.sum_univ_eq_sum_range F, Fin.sum_univ_eq_sum_range F]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n hn hn'
      simp only [Finset.mem_range] at hn hn'
      simp only [F]
      rw [dif_neg (by omega)]
  · intro x ξ
    simp only [SOp.symb]
    by_cases h : o = m'
    · subst h
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [liftA]
      rw [dif_pos (by simp)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [liftA]
      rw [dif_neg (by simp; omega)]
      simp

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
