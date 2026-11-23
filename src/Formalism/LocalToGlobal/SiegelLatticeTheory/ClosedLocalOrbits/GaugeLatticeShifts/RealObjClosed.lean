module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

open Formalism.BasicNotions Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf

theorem realObj_inNuX {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ) : InNuX X u u' sc := by
  have hC : 0 ≤ DisintegrationConstant X u u' sc := by
    unfold DisintegrationConstant
    split_ifs with h
    · exact h.choose_spec.1.le
    · exact le_rfl
  have hO : ∀ c, 0 ≤ hilbertSchmidtSqGram X u u' sc c := fun c => by
    unfold hilbertSchmidtSqGram hs2
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm : Measurable (fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (InfCut.wt_cont X u u').measurable)
  unfold InNuX intOOe intCe nuM
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine MeasureTheory.lintegral_congr fun c => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul' (hO c), ← ENNReal.ofReal_mul hC, mul_assoc]

end Formalism.L2.SG.Pf
