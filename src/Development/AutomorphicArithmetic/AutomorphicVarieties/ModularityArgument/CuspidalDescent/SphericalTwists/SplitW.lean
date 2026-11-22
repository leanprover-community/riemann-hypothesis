module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.LgAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfIsCompAlongSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.SplitW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GalUnitary
public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealOld
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.LocDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IrreducibleWeilDeligneTameLevelEqCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaFixesRootsOfUnityOfArtinCongruence
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelNontrivialOfCharacterSupport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelExistsTorusCongruenceFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedCongruenceNeBotOfJacquetTorusFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasFixedOfAlgNormFixedNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactAndCongruentOfMemPrincipalCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMatchBaseChange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferEqOfIsOpenKer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharPolCharCongr

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V

def UpperTheory.V.Z.Desc.W.SphEq {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {n : ℕ} (ι : Qbar l ≃+* ℂ) (σ : Submodule ℂ (UA L n → ℂ)) (ρ : G L Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : Plc L, IsSplitAt w → ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (τ : SmIrr (GLw n w)) (b : Multiset ℂˣ),
    IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → GlobalTheory.LFun.HasSatGL w τ.ρ b →
      Af.FrobEig ι ρ w (Af.algSat n (normV w) b)

open UpperTheory.V.Z.Desc.W

namespace UpperTheory.V.Hi.Up

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {Q : QData V} {c : Coef l} {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r}

end UpperTheory.V.Hi.Up

