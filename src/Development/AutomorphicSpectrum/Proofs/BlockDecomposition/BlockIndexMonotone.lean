module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.BlockIndex

theorem sum_castLE_eq_range {h : ℕ} (d : Fin h → ℕ) (a : Fin h) :
    ∑ b : Fin a, d (Fin.castLE a.2.le b) =
      ∑ c ∈ Finset.range a, (fun c => if hc : c < h then d ⟨c, hc⟩ else 0) c := by
  rw [← Fin.sum_univ_eq_sum_range (fun c => if hc : c < h then d ⟨c, hc⟩ else 0) a]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dite_eq_left (b.2.trans a.2)] <;> rfl

theorem partial_sum_succ_le {h : ℕ} (d : Fin h → ℕ) {a b : Fin h} (hab : b < a) :
    ∑ c : Fin b, d (Fin.castLE b.2.le c) + d b ≤ ∑ c : Fin a, d (Fin.castLE a.2.le c) := by
  have hsub : Finset.range ((b : ℕ) + 1) ⊆ Finset.range a := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (show (b : ℕ) + 1 ≤ a from hab))
  have key := Finset.sum_le_sum_of_subset (f := fun c => if hc : c < h then d ⟨c, hc⟩ else 0) hsub
  rw [Finset.sum_range_succ, dite_eq_left b.2] at key
  rw [GlobalTheory.CompanionTheory.BlockIndex.sum_castLE_eq_range d b, GlobalTheory.CompanionTheory.BlockIndex.sum_castLE_eq_range d a]
  exact key

theorem stdBlocks_lt_of_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {a b : Fin h} (hab : b < a)
    (x : Fin (d a)) (y : Fin (d b)) : stdBlocks d hd ⟨b, y⟩ < stdBlocks d hd ⟨a, x⟩ := by
  rw [Fin.lt_def, GlobalTheory.SmGL.stdBlocks_val,
    GlobalTheory.SmGL.stdBlocks_val]
  have h1 := GlobalTheory.CompanionTheory.BlockIndex.partial_sum_succ_le d hab
  have h2 := y.2
  omega

theorem blockIdx_monotone : ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), Monotone (Zl.JC.blockIdx d hd) := by
  intro h N d hd i j hij
  by_contra H
  rw [not_le] at H
  have H' : ((GlobalTheory.SmGL.stdBlocks d hd).symm j).1 <
      ((GlobalTheory.SmGL.stdBlocks d hd).symm i).1 := H
  have key := GlobalTheory.CompanionTheory.BlockIndex.stdBlocks_lt_of_lt d hd H'
    ((GlobalTheory.SmGL.stdBlocks d hd).symm i).2
    ((GlobalTheory.SmGL.stdBlocks d hd).symm j).2
  simp only [Sigma.eta, Equiv.apply_symm_apply] at key
  exact absurd hij (not_le.mpr key)

end GlobalTheory.CompanionTheory.BlockIndex
