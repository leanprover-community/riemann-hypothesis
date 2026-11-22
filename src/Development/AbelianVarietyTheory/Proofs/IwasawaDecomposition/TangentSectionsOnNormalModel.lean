module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTorsionSemiAbelian
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm.Chart

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet

section Alg

end Alg

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {m g : ℕ}

end Tan

section Geo

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end Geo

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)}

end Coord

end GlobalTheory.LineNorm.Chart

