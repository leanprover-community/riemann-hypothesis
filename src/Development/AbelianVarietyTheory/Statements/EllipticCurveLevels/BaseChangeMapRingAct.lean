module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingExistsOfCubeTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAdjointEndomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open GlobalTheory.DeRham (spOver)
open GlobalTheory.AbDual GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.BadPt (IsWeilHom)
open GlobalTheory.PerfdLat (dualBaseChange)
open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin (IsPolarisation)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreTateDef

section Notions

variable {S S₀ : Scheme.{0}} {A B : Over S} {A₀ B₀ : Over S₀}

end Notions

section Clauses

variable (p : ℕ) [Fact p.Prime] (R R₀ : Type) [CommRing R] [CommRing R₀] [Algebra R R₀]

end Clauses

section Functor

variable {p : ℕ} [Fact p.Prime] {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R R₀]
  {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀]
  {i : A₀.left ⟶ A.left} {j : B₀.left ⟶ B.left} {G H : PDivGroup p R}

end Functor

section Consequences

variable {p : ℕ} [Fact p.Prime] {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R R₀]

end Consequences

section Base

end Base

section Elliptic

open GlobalTheory.WeierstrassCurve (ellPolAV)

variable (R R₀ : Type) [CommRing R] [CommRing R₀] [Algebra R R₀] [IsNoetherianRing R] [IsNoetherianRing R₀]

end Elliptic

end GlobalTheory.SerreTateDef
