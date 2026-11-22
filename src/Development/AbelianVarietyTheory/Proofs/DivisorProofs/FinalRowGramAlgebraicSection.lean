module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.PublishedTheorems.ThetaCharacteristics.ThetaCharZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDieudonne
public import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameReductionEqOneOfCongruentModIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCongruenceSelfDualOfPrincipalLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveLiftCongruentModIdealStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseLevelInj
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR

theorem hatL_cong_of_hat {D : D7} (V : HSp D) (κ : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)),
      (finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F (Λ' : Set (Fin V.rank → D.host.E))) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V κ).1 *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  intro z hz
  have h1 := GlobalTheory.PrincInLevel.swap_mem_hatL Λ' _ (h _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ z hz))
  have e : (Lev.finE V κ).1 = (finHom V κ).1.map (Algebra.TensorProduct.comm D.host.F _ D.host.E) := rfl
  convert h1 using 1
  funext j
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.sub_apply, map_sub, Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply,
    Matrix.map_apply]

end GlobalTheory.BaseLevelInj

