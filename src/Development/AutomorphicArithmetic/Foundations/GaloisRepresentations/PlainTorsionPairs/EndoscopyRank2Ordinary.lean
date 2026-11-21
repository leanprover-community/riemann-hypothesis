import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.PlainTorOfMono0
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IrrOfComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.JrTeichEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppSmo1
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SphUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinSph
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppSmo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.AdWit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ConjTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.SatOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.EndOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.DualOfWeights
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.GalAut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
open private au_isTeich au_open from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
open private absPt ss_comp iso_of_det ss_of_irr irr_of_comp irr_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IrrOfComp



theorem UpperTheory.Gal.projectedFormsSystemPart.tu_same {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (hn : 1 ≤ n) {ι : Qbar l ≃+* ℂ} {ρ : G F Ω →* GL (Fin n) (Qbar l)} {π π' : CuspSub F n}
    (h : Af.AttC ι ρ π) (h' : Af.AttC ι ρ π') {w : Plc F} (k : TU π w) : TU π' w := by
  obtain ⟨t, ht⟩ := ImaginaryQuadraticEtaCharacter.winOf F n hn π
  have ev : ∀ᶠ v : Plc F in Filter.cofinite, ∃ B, (CG.mk π).HasSat v B ∧ (CG.mk π').HasSat v B := by
    filter_upwards [h.2, h'.2] with v ⟨B, hB, hE⟩ ⟨B', hB', hE'⟩
    exact ⟨B, hB, (UpperTheory.hecke_eigenvalue_basic_properties F Ω l ι v).2.2 n ρ B B' hE hE' ▸ hB'⟩
  have k' : ImaginaryQuadraticEtaCharacter.WinAt π' t w := by
    rcases hn.eq_or_lt with rfl | h2
    · exact ImaginaryQuadraticEtaCharacter.suppSmo1 F π π' ev t w (ht w k.1 k.2)
    · exact ImaginaryQuadraticEtaCharacter.suppSmo F n h2 π π' ev t w (ht w k.1 k.2)
  exact ⟨k'.1, ImaginaryQuadraticEtaCharacter.winUnl F n π' t w k'⟩
