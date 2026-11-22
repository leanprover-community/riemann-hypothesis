module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsOfPolAV
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HtExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumberStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGenericStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionFieldStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullbackStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorsionQuasiFiniteGroupStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullbackIffStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairingStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosedStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem lattice_integrally_closed_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (s : Sp Ω ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (_ : SABMap o.t t ξ) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (n : ℕ) (q : Cpt ξ), IsCptGen ξ → 0 < n → FullTorsion t.G ξ n → IsIntegrallyClosed (X.presheaf.stalk q.1) → IsNoetherianRing (X.presheaf.stalk q.1) → M.IsHTFormAt n q 0 ∧ (0 < D.p + D.q → ∃ ζ : Ω, IsPrimitiveRoot ζ n) ∧ M.htOm t.PP.L n q = M.htLat n q :=
  _root_.GlobalTheory.T.full_torsion_integrally_closed

end PositivityTheory.UnitarySelfGeneration
