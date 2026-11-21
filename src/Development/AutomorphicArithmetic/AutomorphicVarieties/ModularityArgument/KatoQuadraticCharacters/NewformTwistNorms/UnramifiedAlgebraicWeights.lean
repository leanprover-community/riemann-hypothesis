import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasSatOfFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.MultisetEqOfProdEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.MemKLevOneOfMemK1G
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Deadel

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.NewLevel

open UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host




private noncomputable abbrev Eo (v : InfinitePlace ℚ) (i j : Fin 2) : Module.End ℂ (TR.Sm ℚ 2) := TR.Eop v i j

private noncomputable def LowS (k : ℕ) : Submodule ℂ (TR.Sm ℚ 2) :=
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 1 - Eo v 1 0 - (Complex.I * (k : ℂ)) • (1 : Module.End ℂ (TR.Sm ℚ 2)))) ⊓
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 0 - Eo v 1 1 - Complex.I • (Eo v 0 1 + Eo v 1 0))) ⊓
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 0 + Eo v 1 1))




end GlobalTheory.NewLevel

end
