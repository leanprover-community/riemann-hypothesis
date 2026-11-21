import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OfClassification
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MassRatioAllUnramifiedCmFields
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem discreteSeries_three_of_hypotheses (hC : GlobalTheory.Published.DiscreteSeriesCoverExists) :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) ∧ (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) ∧ (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) := by
  intro hE hU
  refine ⟨fun n ε lam hl => ?_, fun n ε lam hl H H' _ _ _ _ σ σ' hσ hσ' => hU n ε lam hl H H' σ σ' hσ hσ', hC⟩
  obtain ⟨H, i1, i2, σ, h1, h2, h3, h4, h5, h6, h7⟩ := hE n ε lam hl
  exact ⟨H, i1, i2, σ, h1, h2, h3, h4, h5, h6, h7⟩

end GlobalTheory
end

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory

theorem hypA_of_artinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCoverExists → GlobalTheory.Published.BesselUniquenessReal → GlobalTheory.Published.FormalDegreeCompactDual → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → HypA :=
fun ar cm we hm cd cw hf cl ce bu fd sw =>
  have c := GlobalTheory.DiscreteSeriesConsequences.of_classification cl
  have u : GlobalTheory.Published.DiscreteSeriesUpqUnique := GlobalTheory.Published.discreteSeriesUpqUnique_of_classification cl
  have d := GlobalTheory.discreteSeries_three_of_hypotheses ce c.2.2.2.2 u
  ⟨ar.rayClassFieldSt, ar.principalIdealSt, cm, hm, cd, cw, GlobalTheory.weilRepresentationUnitaryPair, c.2.2.1, hf, c.2.1, u,
    GlobalTheory.rowsFinDim_link, sw, GlobalTheory.BesselMapOne.besselMapUniq_of_besselUniqueness bu, c.2.2.2.2, fd, GlobalTheory.Mass.massRatio_all_unramified_cmFields,
    d.1, d.2.1, d.2.2, ar, we⟩

end GlobalTheory
end
