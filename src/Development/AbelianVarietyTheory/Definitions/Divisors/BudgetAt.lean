module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovHt

section Steps

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i)

def ShortAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ abelian₂ : ℝ, (∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)),
      IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂) ∧
    Real.log abelian₂ * (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ C * unitE p

def GeomAt (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) ∧
    GlobalTheory.DegVal.BirOn Y.U Z (wtOf (dat p i) u1 0) ∧ (1 - rhoB (dat p i) u1) * Y.dg u1 Z ≤ delPrime Y.U Z u1

def MultAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧
    ∀ Z, Mult Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z u1 (uPrime (dat p i) u1) cc

def BudgetAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  Y.d.l₂.M'.primeFactors.card ≤ 15 ∧
  ∃ g : ℝ, WtGap (uPrime (dat p i) u1) g ∧ 0 ≤ errX (ell D) (uPrime (dat p i) u1) g ∧
    lenT p i PP * errX (ell D) (uPrime (dat p i) u1) g ≤ C * unitE p ∧
    0 ≤ htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) ∧
    lenT p i PP * (htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1)) ≤ C * unitE p

end Steps

end GlobalTheory.CovHt

end
