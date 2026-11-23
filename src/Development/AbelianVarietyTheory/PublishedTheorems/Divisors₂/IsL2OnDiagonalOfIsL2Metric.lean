module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat transl IsFactor IsMetric)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points (PtsOver)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm (IsRegVar BottChern ArChow hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (om0)
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.TorsionForm

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {A : Over S}
  {g D : ℕ}

section Global

variable {D' r : ℕ}



end Global

end GlobalTheory.TorsionForm

namespace GlobalTheory.Published

open GlobalTheory.TorsionForm MvPolynomial

def AmpleVanishing : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → IsRelAcyclic A.hom A.hom L

end GlobalTheory.Published
