module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

end GlobalTheory.HTPres

namespace GlobalTheory.HTPres

end GlobalTheory.HTPres
