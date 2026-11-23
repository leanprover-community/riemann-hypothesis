module

public import Formalism.PeriodIntegrals.QmDefs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.QmSkipWork

theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  by_cases h : k.val < p.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt p k (by simpa [Fin.lt_def] using h)]
    simp
  · rw [if_neg h, Fin.succAbove_of_le_castSucc p k (by simp [Fin.le_def]; omega)]
    simp

theorem skipSucc : PI.SkipSucc := by
  unfold PI.SkipSucc
  intro t i j
  apply Fin.ext
  rw [PI.QmSkipWork.val_succAbove]
  unfold PI.skip1
  split_ifs <;> rfl

theorem skipSucc2 : PI.SkipSucc2 := by
  unfold PI.SkipSucc2
  intro t i i' j hii'
  have hb : (i.succAbove i').val = i'.val + 1 := by
    rw [PI.QmSkipWork.val_succAbove, if_neg (by omega)]
  apply Fin.ext
  simp only [PI.QmSkipWork.val_succAbove]
  unfold PI.skip2
  split_ifs <;> (try dsimp only) <;> omega

end PI.QmSkipWork
