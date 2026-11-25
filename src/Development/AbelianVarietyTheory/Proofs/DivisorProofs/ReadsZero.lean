module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.BdryUnit

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def SameVec (Y : Model Xo c (RingHom.id c.F)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (v : Sp (DualNumber S) ⟶ Y.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber S) ⟶ Y.oF.t.G.left,
    IsTanAtG Y.oF.t (ptF y) w ∧ w ≫ Y.m0.toSABMap.φ = u ∧ w ≫ Y.m.φ = v

def Matches (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (a : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S)) : Prop :=
  a.x = ptF y ≫ Y.jQ ∧
    (∀ i : Fin Dw.p, ∃ j : Fin (Dw.mult τ.1), (j : ℕ) = i ∧ SameVec Y y (y.u τ.1 j) (a.v i).left) ∧
    ∀ i : Fin Dw.q, ∃ j : Fin (Dw.mult (conjEmb τ.1)), (j : ℕ) = i ∧ SameVec Y y (y.u (conjEmb τ.1) j) (a.w i).left

def Reads (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H)
    (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), GlobalTheory.FlatLine.Tested y →
    ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S), Matches Y V τ y a →
      evR Xo c f y = sig S (algebraMap c.F S) a

end GlobalTheory.BdryUnit
