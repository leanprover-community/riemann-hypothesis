module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.CovChar

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

variable {R} {X Y : Scheme.{0}} (f : Y ⟶ X)

end GlobalTheory.Et.CovChar

namespace GlobalTheory.AV.AbVar

open ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K]

end GlobalTheory.AV.AbVar
