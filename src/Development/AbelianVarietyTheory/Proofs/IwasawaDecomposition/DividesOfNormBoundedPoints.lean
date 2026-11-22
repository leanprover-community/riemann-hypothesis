module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPoint
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Dvd

attribute [local instance] Over.cartesianMonoidalCategory

section Algebra

variable {R : Type} [CommRing R]

end Algebra

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

end Model

end GlobalTheory.HTLine.Dvd
