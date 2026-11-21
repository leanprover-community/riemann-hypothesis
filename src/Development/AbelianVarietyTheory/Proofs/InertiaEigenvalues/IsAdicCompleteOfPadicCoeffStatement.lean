import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteOfPadicCoeff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import BuildAid.ForwardExisting

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_of_padicCoeff' : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  atlas_forward_decl GlobalTheory.isAdicComplete_of_padicCoeff
