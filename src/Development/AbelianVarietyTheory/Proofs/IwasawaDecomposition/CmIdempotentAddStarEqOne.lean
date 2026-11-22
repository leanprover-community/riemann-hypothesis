module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiUnitOnRescaleUniformizerOfQVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.ArcBuild

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) {ϖ : T.V} (hϖ : Irreducible ϖ)

def piK : (FractionRing T.V)ˣ :=
  Units.mk0 (algebraMap T.V (FractionRing T.V) ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)

theorem cmIdempotent_add_star_eq_one : letI := H.starRing; H.w0 + star H.w0 = 1 := halfUnit_add_star H

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (m : SABMap t Y.t y)

end ThetaShiftProofs

end GlobalTheory.ArcBuild
