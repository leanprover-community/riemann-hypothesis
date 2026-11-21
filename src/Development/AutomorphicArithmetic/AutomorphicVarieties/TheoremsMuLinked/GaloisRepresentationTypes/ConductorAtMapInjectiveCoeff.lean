import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DataEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ValProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DirGPowOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowClogLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CountNormInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GaloisRepIneqOfAllIrreducibleNonvanishing
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.NumsZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PhiGam
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefIndep

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th

section Transfer

variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')

private def chHom : DirichletCharacter O N →* DirichletCharacter O' N where
  toFun χ := χ.ringHomComp f
  map_one' := MulChar.ringHomComp_one f
  map_mul' a b := MulChar.ringHomComp_mul a b f










end Transfer


