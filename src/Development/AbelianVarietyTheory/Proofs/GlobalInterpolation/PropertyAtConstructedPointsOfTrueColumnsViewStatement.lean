module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsView
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

theorem _root_.GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView : ∀ (R : ∀ D : D7, Obj D → Prop), (∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)) (nch : NChoice (w.D Z)), ColView w Z O.ex.tw nch → GlobalTheory.LvT.WtSign.BaseSigns B → Formalism.L2.Theta.RealTied (w.D Z) → R (w.D Z) O) → ∀ (K : Ctx) (β : BPt K), β.Is HasCols → R β.D β.O := by
  first | exact @GlobalTheory.Fc.Cv.view_at_built | exact GlobalTheory.Fc.Cv.view_at_built | (intros; apply GlobalTheory.Fc.Cv.view_at_built <;> assumption)
