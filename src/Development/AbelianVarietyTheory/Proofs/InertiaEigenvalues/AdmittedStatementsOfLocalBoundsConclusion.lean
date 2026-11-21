import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTableOfLocalBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionFive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionSix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesVanishingExcluded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesConditionTwoThree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRamifiedTypePrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRowsAndBand

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem admittedStatements_of_localBoundsConclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ),
    Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  intro D L P X C h
  obtain ⟨tf, hF, h23⟩ := h.two
  refine ⟨tab L X tf C, ?_⟩
  have h2 : TwistedPlaces.adm2 L := fun j hj w hw _ => h.mult j hj w hw
  obtain ⟨hA, hB, hC, hD, hBand⟩ := GlobalTheory.T.admA_admB_inert_band_tab D L P X C tf h
  obtain ⟨hE, hExc⟩ := GlobalTheory.T.localBoundTableAllPrimes_vanishing_excluded D L P X C tf h
  obtain ⟨hG, hH⟩ := GlobalTheory.T.ramifiedPrimeLengthBound_and_generatorPrimeEtaBound_tab D L P X C tf h
  exact ⟨h.pass, h2, h.rank, GlobalTheory.T.admissible_table_of_local_bounds D L P X C tf h h23, GlobalTheory.T.localBoundTableAllPrimes_sizeConditionFive D L P X C tf h,
    GlobalTheory.T.localBoundTableAllPrimes_sizeConditionSix D L P X C tf h, hA, hB, hC, hD, hBand, hE, hExc,
    GlobalTheory.T.smallPrimeLengthBound_tab D L P X C tf h hF, hG, hH, h.par⟩

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ), Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  atlas_forward_decl GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion
