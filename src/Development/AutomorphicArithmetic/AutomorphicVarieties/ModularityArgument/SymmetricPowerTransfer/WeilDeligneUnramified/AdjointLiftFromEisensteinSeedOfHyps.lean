module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NormOneOfFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SeedDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ExistenceOfGaloisRepresentationsOfHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PotOrd

@[expose] public section

open UpperTheory.GalN.V

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.toIsDomain

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

section CongLemmas

variable {l : ℕ} [Fact l.Prime]

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

end CongLemmas

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

end Gal

section Shape

variable {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

end Shape

end UpperTheory.V.Sd
