module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Intervals
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.SumAntidiagonalTuple, Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple

-- ===== clump member: Formalism.PeriodIntegrals.SumAntidiagonalTuple =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.SumAntidiagonalTuple", "h": "module\n\npublic import Mathlib.Data.Fin.Tuple.NatAntidiagonal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace PI

def SumAntidiagonalTuple : Prop :=
  ∀ D T : ℕ, D < T →
    ∑ k ∈ Finset.range (T - D), (Finset.Nat.antidiagonalTuple D k).card = Nat.choose (T - 1) D

end PI
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.SumAntidiagonalTuple =====

-- ===== clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple", "h": "module\n\npublic import Formalism.PeriodIntegrals.SumAntidiagonalTuple\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Algebra.BigOperators.Intervals\n\n"}
section -- clump:auto
@[expose] public section

private theorem sum_range_add_choose_eq_choose_succ (E n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k + E).choose E = (n + E + 1).choose (E + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show n + 1 + E + 1 = (n + E + 1) + 1 by omega,
      Nat.choose_succ_succ (n + E + 1) E, show n + 1 + E = n + E + 1 by omega]
    simp only [Nat.succ_eq_add_one]
    omega

private theorem card_antidiagonal_tuple_succ_eq_sum_range (D k : ℕ) :
    (Finset.Nat.antidiagonalTuple (D + 1) k).card =
      ∑ i ∈ Finset.range (k + 1), (Finset.Nat.antidiagonalTuple D (k - i)).card := by
  calc (Finset.Nat.antidiagonalTuple (D + 1) k).card
      = ((Finset.range (k + 1)).sigma fun i => Finset.Nat.antidiagonalTuple D (k - i)).card := by
        refine Finset.card_nbij' (fun x => ⟨x 0, Fin.tail x⟩) (fun p => Fin.cons p.1 p.2)
          ?_ ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hx
          rw [Fin.sum_univ_succ] at hx
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range,
            Finset.Nat.mem_antidiagonalTuple, Fin.tail]
          omega
        · rintro ⟨i, y⟩ hp
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range,
            Finset.Nat.mem_antidiagonalTuple] at hp
          simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ,
            Fin.cons_zero, Fin.cons_succ]
          omega
        · intro x _
          simp
        · rintro ⟨i, y⟩ _
          simp
    _ = ∑ i ∈ Finset.range (k + 1), (Finset.Nat.antidiagonalTuple D (k - i)).card :=
        Finset.card_sigma _ _

private theorem card_antidiagonal_tuple_succ_eq_choose (D : ℕ) :
    ∀ k, (Finset.Nat.antidiagonalTuple (D + 1) k).card = (k + D).choose D := by
  induction D with
  | zero =>
    intro k
    rw [card_antidiagonal_tuple_succ_eq_sum_range, Finset.sum_eq_single k]
    · simp [Finset.Nat.antidiagonalTuple_zero_zero]
    · intro i hi hik
      simp only [Finset.mem_range] at hi
      obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 := ⟨k - i - 1, by omega⟩
      rw [hm, Finset.Nat.antidiagonalTuple_zero_succ, Finset.card_empty]
    · intro h
      simp at h
  | succ D ih =>
    intro k
    rw [card_antidiagonal_tuple_succ_eq_sum_range]
    simp only [ih]
    have h : ∑ j ∈ Finset.range (k + 1), (k - j + D).choose D =
        ∑ j ∈ Finset.range (k + 1), (j + D).choose D := by
      have := Finset.sum_range_reflect (fun i => (i + D).choose D) (k + 1)
      simpa only [Nat.add_sub_cancel] using this
    rw [h, sum_range_add_choose_eq_choose_succ, Nat.add_assoc]

theorem sum_antidiagonalTuple : PI.SumAntidiagonalTuple := by
  intro D T hDT
  cases D with
  | zero =>
    obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.choose_zero_right]
    rw [Finset.sum_range_succ']
    simp [Finset.Nat.antidiagonalTuple_zero_succ, Finset.Nat.antidiagonalTuple_zero_zero]
  | succ E =>
    obtain ⟨n, rfl⟩ : ∃ n, T = n + E + 2 := ⟨T - E - 2, by omega⟩
    have h1 : n + E + 2 - (E + 1) = n + 1 := by omega
    have h2 : n + E + 2 - 1 = n + E + 1 := by omega
    rw [h1, h2]
    simp only [card_antidiagonal_tuple_succ_eq_choose]
    exact sum_range_add_choose_eq_choose_succ E n
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple =====
