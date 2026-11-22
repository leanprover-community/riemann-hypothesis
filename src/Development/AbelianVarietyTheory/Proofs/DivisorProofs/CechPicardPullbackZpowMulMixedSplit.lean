module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiMapFst
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPullOfRigOfSym
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeMixed

open GlobalTheory.CechPic

end GlobalTheory.CubeMixed
