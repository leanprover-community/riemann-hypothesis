module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Cell

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section Mat

variable {R : Type} [CommRing R] {m : ℕ}

def IsLowInv (L : Matrix (Fin m) (Fin m) R) : Prop := (∀ i j, i < j → L i j = 0) ∧ ∀ i, IsUnit (L i i)

end Mat

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

end Geo

end GlobalTheory.ShFam.Cell
