module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.Fc.Cv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure ColView (w : ColW B f T) (Z : w.Lt) (tw : TwForms (w.D Z)) (nch : NChoice (w.D Z)) : Prop where
  jets : ColIn.JetsIn w.I
  rowInt : GlobalTheory.PerQ.RowInt w.I w.l Z
  tw_eq : tw = w.tw Z
  tup : ∃ tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch, tp.xi = w.I.xi

def HasCols : V4.Slot := positionOf fun _ _ _ _ w Z c => ColView w Z c.O.tw c.O.nch

def OverCols (Q : V4.Slot) : Prop := ∀ K X f T c, Q K X f T c → HasCols K X f T c

theorem OverCols.and_left {Q R : V4.Slot} (h : OverCols Q) : OverCols fun K X f T c => Q K X f T c ∧ R K X f T c :=
  fun K X f T c t => h K X f T c t.1

end GlobalTheory.Fc.Cv

end
