import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MinimalHyp5
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.KBridgeOfKPublishedW
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.InputsOfHida
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoefIsCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MinimalHyp2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.IsOpenKerKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.Seed3N
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedII
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedIII
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.VwinOfInputs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.AbelianUnitPowers.IsOpenKerKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.AbelianUnitPowers.Seed3L
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.MixedUnitCongruences.SeedII
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.MixedUnitCongruences.SeedIII
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.AdAutQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.QuadOf

section
open UpperTheory.Top

namespace UpperTheory.V

open UpperTheory.V.Published

structure HypothesesV : Prop where
  cohC : ClozelCohC
  cohR : ClozelCohR
  conjC : ClozelConjC
  conjR : ClozelConjR
  borelC : BorelInjC
  borelR : BorelInjR
  galR : GaloisRepReal
  smoR : StrongMultOneReal
  bc : QuadBaseChange
  thorne : ThorneAdjoint
  descU : DescentUnitary
  types : TypesNZero
  sign : SignCsd
  cyc : CyclicBaseChange
  jl : JacquetLanglands
  finR : FormsFiniteReal
  adj : AdjointLift
  cube : SymCube
  ind : QuadInduction
  eis : HilbertEisOne
  one : HilbertOne
  kato : Kato
  k : KPublished

end UpperTheory.V
end

section
open UpperTheory.Top

namespace UpperTheory.V

open UpperTheory.V.Published

structure PublishedTheorems : Prop where
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : GaloisRepReal
  thorne : ThorneAdjoint
  descU : DescentUnitary
  types : TypesNZero
  cyc : CyclicBaseChange
  jl : JacquetLanglands
  adj : AdjointLift
  cube : SymCube
  ind : QuadInduction
  eis : HilbertEisOne
  one : HilbertOne
  kato : Lit.KatoO
  k : KPublishedW

end UpperTheory.V
end

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.HV.Core

open UpperTheory.V.Lit UpperTheory.V.W

theorem countI (hN : LitN) (hK : ∃ CK : ℝ, LemmaK CK) (hKa : KatoUseN) (adK : Af.AdVanishK) (adQ : Af.AdVanishQ)
    (nw : Af.NewformAut) (nU : Af.CongruenceNumberRankThree) (h3 : Aut.AutomorphyUnramifiedCoefficients) : CountI :=
  KN.O.caseI
    { loc := U.localGaloisCohomology₂ hN, pt := hN.coh.pt, gf := hN.coh.gf, ge := hN.coh.ge, lemK := hK, lemM := Alg.M.main_holds,
      lemM' := Alg.M.mprime_holds, lemP := Alg.lemmaP, kato := hKa, adK := adK, adQ := adQ, newAut := nw, number := nU } h3

end UpperTheory.V.HV.Core
end
