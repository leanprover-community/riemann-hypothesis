module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapAtEveryTrueColumnMemberStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

theorem constructedPoint_referenceChainWord_formsMap (Q : V4.Slot) (hQ : OverCols Q) (K : Ctx) (β : BPt K) (hq : β.Is Q) :
    ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 β.D u :=
  GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D _ => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u)
    (fun _ _ _ w Z _ _ _ _ _ => GlobalTheory.T.aux_of_ok_of_pins w.I w.ok w.pins w.l Z)
    K β (hQ _ _ _ _ _ hq)

theorem referenceChainEvaluation_bundlePoints_overColumns : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints Q Lk :=
  fun Q hQ _ Lk => Row0.row (validForConstructedPointClasses_eventuallyWorkingClass (R := fun D _ => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u)
    (EvP.of_all fun _ K _ β hq => constructedPoint_referenceChainWord_formsMap Q hQ K β hq)) Lk

end GlobalTheory.Fc.PeriodEntriesOverColumns

end
