module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (pullback biprod)
open MonoidalCategory CartesianMonoidalCategory
open GlobalTheory.Cartier
open GlobalTheory.CechPic (Pic cls lam)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
open scoped ContDiff ComplexOrder CategoryTheory.Obj

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

namespace RegCover

variable [IsIntegral X] (C : RegCover p)

end RegCover

namespace HermLB

variable [IsIntegral X] [IsLocallyNoetherian X] (L M : HermLB p)

variable {L M}

end HermLB

section Sum

variable {E₁ E₂ : X.Modules} {r s : ℕ}

end Sum

namespace VMetric

variable [IsIntegral X] {E : X.Modules} {r : ℕ} {h : VMetric p E r} {a b : ℝ}

end VMetric

namespace PPAS

attribute [instance] grp smoothDim

variable {S S' : Scheme.{0}} (P : PPAS S)

namespace RiemannData

attribute [instance] grp

variable {P} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)

end RiemannData

variable (P : PPAS X)

variable {P} {t : ℝ} {h h' : VMetric p (omega P.A) P.g}

variable (P p) [IsIntegral X]

variable {P p} {a b : ℝ}

end PPAS

end GlobalTheory
