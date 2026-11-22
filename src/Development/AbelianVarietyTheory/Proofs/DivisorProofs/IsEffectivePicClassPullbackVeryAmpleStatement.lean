module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassPullbackVeryAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
