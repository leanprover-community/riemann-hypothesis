module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.degenerationValues_int_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing R) C], CExt R I C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∃ q, N.Int q := by
  first | exact @GlobalTheory.Ex.IntVal.main
