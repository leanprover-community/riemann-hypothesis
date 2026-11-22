module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
public import ReciprocityTheory.AnalyticForms.LeviForms.Energy
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HomogeneousLiftHolomorphicOnSnd
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDirectionalDerivativeRegularCoordinate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts

namespace GlobalTheory.Mean4O

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

instance compactSpace_pts (σ : F →+* ℂ) : CompactSpace (Pts Y σ) := CxPts.compactSpace σ Y.isProjOver

section Norms

variable {σ : F →+* ℂ} {Δ : Y.Dv}

end Norms

attribute [instance] Cover.int Cover.intG Cover.fin Cover.surj

namespace Cover

variable (V : Cover Y)

end Cover

end GlobalTheory.Mean4O
