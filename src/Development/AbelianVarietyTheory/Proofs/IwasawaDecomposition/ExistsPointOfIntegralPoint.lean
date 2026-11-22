module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj.PointsOfFlagModel GlobalTheory.ShFam.Pad.Pull

namespace GlobalTheory.ModelPt

end GlobalTheory.ModelPt
