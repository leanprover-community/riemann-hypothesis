module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.arcFramedPoint_unique_and_baseChange :
    Out.Laws → Out.Laws2 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
      (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
      (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
      (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ)
      (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec),
    ThNZ th →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (y : FrPt Xo c S),
    GlobalTheory.ArcQ.IsArcFr W e th ι y →
      (Mono Y.j → ∀ y', GlobalTheory.ArcQ.IsArcFr W e th ι y' → y' = y) ∧
      (Mono Y.j → ∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y₁ : FrPt Xo c T),
        FrMap φ y y₁ → GlobalTheory.ArcQ.IsArcFr W e th (φ.toRingHom.comp ι) y₁) :=
  @GlobalTheory.ArcQ.isArcFr_unique_baseChange
