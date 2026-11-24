module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClosingTrueCols
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.Cv

theorem row_level_valuations : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  refine Row0.row (H := EvC fun D O => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT O.X O.ex.tw u)
    (validForConstructedPointClasses_eventuallyWorkingClass (EvP.of_all fun _ K _ β hβ => ?_)) Lk
  refine GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D O => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT O.X O.ex.tw u) ?_ K β
    (hQ _ _ _ _ _ hβ)
  intro B f T w Z O nch hv hs _ u
  rw [hv.tw_eq]
  exact GlobalTheory.LvT.Built.TrueCols.closing_true_cols w.I w.ok hv.jets hs w.l Z w.l0 O.X u

end GlobalTheory.Fc.Cv
