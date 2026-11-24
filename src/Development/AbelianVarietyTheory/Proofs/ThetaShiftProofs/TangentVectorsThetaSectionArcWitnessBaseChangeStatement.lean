module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
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

theorem _root_.GlobalTheory.T.tangentVectors_thetaSection_arcWitness_baseChange :
    Out.Laws → Out.Laws2 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
      (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
      (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
      (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ)
      (A' : Type) [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A']
      (b' : O →+* A') (a' : ArcIn Dw l β A' b') (f : A →+* A')
      (p : Out.IsPullDeg f a.D₀ a'.D₀) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)),
      InBC f a a' p → WitBC f p W W' →
        ∃ m : SABMap W'.t W.t (spMap (PowerSeries.map f)),
          W'.m.φ = m.φ ≫ W.m.φ ∧
          (∀ ν ν' v (v' : epsR (PowerSeries A') ⟶ W'.t.G),
            GlobalTheory.ArcQ.LetBC p ν ν' → LieImg W ν v →
              v'.left ≫ m.φ = spMap (Formalism.L2.Pj.dualMap (PowerSeries.map f)) ≫ v.left →
              LieImg W' ν' v') ∧
          ∀ (w : LB.Iso W'.t.PP.L (W.t.PP.L.pull m.φ)) th th' θ (θ' : LB.Sec W'.t.PP.L) θ₂,
            RigIso m w → ThBC p th th' → ThetaOf W th θ → PullSec m.φ θ θ₂ →
              IsoMaps w θ' θ₂ → ThetaOf W' th' θ' :=
  @GlobalTheory.ArcBaseChange.main
