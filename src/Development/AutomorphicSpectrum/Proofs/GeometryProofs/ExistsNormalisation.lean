module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CentreSetDominatingPointStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureChartSpanStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMapStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeExistsUniquePointStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonemptyStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalizationStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaledStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringIntegralClosureMaxStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocalStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalizationStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompatStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLNormExists

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.NormEx

instance isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) :=
  (LocalSubring.range (genMap ξ p)).isLocalRing

theorem exists_normalisation : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'], ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω') (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') ∧ Flat.NormalCpt M'.ξ ∧ IsFinite f ∧ ∀ p : Cpt M.ξ, NormAt M'.ξ f (algebraMap Ω Ω') p :=
  PositivityTheory.HtPt.Mb.LNormExists.NormEx.exists_normalisation

end GlobalTheory.CompanionTheory.Ar.NormEx
