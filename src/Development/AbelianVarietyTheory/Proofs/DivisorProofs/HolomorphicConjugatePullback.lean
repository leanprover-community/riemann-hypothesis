module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyAndPrimeDvdDegOfDvdNorm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtOverClosureIso

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreAV

section

variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) (A : Over S) [GrpObj A]

end

end GlobalTheory.FibreAV
