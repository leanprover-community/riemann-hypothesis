module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTorsionSemiAbelian
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegrallyClosedInFractionFieldPowerSeries
public import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharacterCocycleDescent

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.HTMap

attribute [local instance] Over.cartesianMonoidalCategory

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {T T' : Scheme.{0}} {y : T ⟶ X} {y' : T' ⟶ X}

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {q : ℕ}

attribute [instance] FP.ring FP.alg

namespace FP

variable (P : FP t x₀ q) {S S' : Type} [CommRing S] [CommRing S']

variable {P}

end FP

section Dom

variable [IsDomain A]

namespace FP

variable (P : FP t x₀ q)

variable {P}

end FP

variable [IsIntegrallyClosed A] {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ}

end Dom

section Tan

variable {S : Type} [CommRing S] {x : Sp S ⟶ X}

end Tan

section Char

variable {O : Type} [CommRing O] [IsLocalRing O] {x : A →+* O} {P : FP t x₀ q}

end Char

end GlobalTheory.HTMap
