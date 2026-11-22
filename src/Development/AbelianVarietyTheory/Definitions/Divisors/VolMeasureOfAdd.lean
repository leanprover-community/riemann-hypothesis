module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameEx
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MeasureTheory Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CxPts GlobalTheory.TopForm GlobalTheory.ChartGlue
open scoped ENNReal

namespace GlobalTheory

section General

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {B L : LB Y} {O : Y.Opens}

namespace CompHS

variable {D : ℕ} [SmoothOfRelativeDimension D p] (K : CanonLB p D) (φ φ' : Weight p σ L)
  (ω : H0 p (LB.div K.bundle L) O)

variable {φ φ'}

variable [SecondCountableTopology (CxPts p σ)]

end CompHS

end General

namespace CompHS

open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt (exOf wtOf lieFacZ modelWt homN)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Good

variable {Y T : Scheme.{0}} {p : Y ⟶ Sp c.F} {σ σ' : c.F →+* ℂ} {B : LB Y}

end Good

section Fac

variable {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)

open Classical in
def diagChar (e : Ix Dw → ℤ) (t : Ix Dw → (CAt σ)ˣ) : ℂ := toC (∏ ix, t ix ^ e ix).val

def homFac (la : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) : ℝ :=
  lieFacZ Dw x (wtOf Dw la 0) * (U.X k).nfac (modelWt U (wtOf Dw la 0) k) w.1

theorem homN_eq_homFac (la : AllWt.Weight Dw) (f : Rul Xo c) (k : U.Comp) (w : (U.X k).dom) :
    homN U x (wtOf Dw la 0) f ⟨k, w.1⟩ = homFac U x la k w * ‖toC (evR Xo c f (U.un k w))‖ := by
  have e : rdU U f k w.1 = toC (evR Xo c f (U.un k w)) := dite_eq_left w.2
  change _ * (‖rdU U f k w.1‖ * (U.X k).nfac _ _) = _
  rw [e, homFac]
  ring

variable {U}

end Fac

end CompHS

end GlobalTheory
