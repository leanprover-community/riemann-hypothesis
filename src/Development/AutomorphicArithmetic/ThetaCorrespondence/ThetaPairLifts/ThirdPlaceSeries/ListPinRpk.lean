module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
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



namespace GlobalTheory.Mem.LiteralAutomorphy.PinPt

open Formalism.BasicNotions GlobalTheory.EX.OB
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem listPin_rpk_alt {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {x : GlobalTheory.Mem.R3.TwIn O.ex}
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R S)
    (r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S)
    (hr : r = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) {CF bb : ℝ}
    (h : GlobalTheory.HeightCounting.Up.ListPin D x.R.toRealDat.toLevCh CF bb) :
    GlobalTheory.HeightCounting.Up.ListPin D r.B.Q.Rl.toRealDat.toLevCh CF bb := by
  subst hr
  exact h

end GlobalTheory.Mem.LiteralAutomorphy.PinPt
