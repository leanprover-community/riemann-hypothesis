module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveFst
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivativeClosure
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.CubeRootAut

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

end General

end GlobalTheory.ZH.CubeRootAut
