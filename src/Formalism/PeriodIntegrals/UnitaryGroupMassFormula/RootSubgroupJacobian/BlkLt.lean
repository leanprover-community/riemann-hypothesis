module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.PtEntryNeZeroImp
public import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

noncomputable section

namespace PI.AmpRootJacW

open Formalism.MainNotions.S PI.AmpRootCommon

theorem blk_lt : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), i < j → j < (bs.map Prod.snd).sum →
    blockIdx bs i ≠ blockIdx bs j → pv bs i < pv bs j
  | [], i, j, _, hj, _ => by simp at hj
  | (t, s) :: bs, i, j, hij, hj, hne => by
    simp only [List.map_cons, List.sum_cons] at hj
    simp only [blockIdx, pv] at hne ⊢
    by_cases hi : i < s
    · by_cases hjs : j < s
      · simp [hi, hjs] at hne
      · rw [ite_eq_left hi, ite_eq_right hjs]
        omega
    · have hjs : ¬ j < s := by omega
      simp only [ite_eq_right hi, ite_eq_right hjs] at hne ⊢
      have := blk_lt bs (i - s) (j - s) (by omega) (by omega) (fun e => hne (by rw [e]))
      omega

end PI.AmpRootJacW
