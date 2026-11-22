module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistedDualFrobeniusCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.ExConj

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
open scoped Matrix
open scoped Pointwise

namespace UpperTheory.V.Z.Ord.CU

section Abs

variable {H H' k : Type} [Group H] [Group H'] [Field k] {n : ℕ}

end Abs

end UpperTheory.V.Z.Ord.CU

namespace UpperTheory.V.Z.Ord.CU

open UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu GlobalTheory.MonoConj

section Conc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

end Conc

end UpperTheory.V.Z.Ord.CU

namespace UpperTheory.V.Z.Ord.CU

open UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu GlobalTheory.MonoConj

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

end UpperTheory.V.Z.Ord.CU
