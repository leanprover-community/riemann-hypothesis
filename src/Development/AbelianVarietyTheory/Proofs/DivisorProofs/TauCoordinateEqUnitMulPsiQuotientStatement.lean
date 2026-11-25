module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

theorem _root_.GlobalTheory.T.tauCoordinate_eq_unit_mul_psi_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X)
    (x x₁ x₂ x₃ : (FractionRing R)ˣ), IsTauCoord D a b x → IsPsiCoord D (a + b) x₁ → IsPsiCoord D a x₂ →
      IsPsiCoord D b x₃ → ∃ u : Rˣ, (x : FractionRing R) =
        algebraMap R (FractionRing R) u * x₁ * (x₂ : FractionRing R)⁻¹ * (x₃ : FractionRing R)⁻¹ := by
  first | exact @GlobalTheory.TauCoordQuot.main
