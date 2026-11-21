import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdelicUnitaryGroupStabilizersUnimodular
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnitaryGroupStabilizersUnimodularFinitePlacStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomainStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVector

section
namespace GlobalTheory

theorem adelicUnitaryHaar_holds : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact ⟨GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ, GlobalTheory.T.archimedean_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ,
    GlobalTheory.T.finiteAdelicUnitaryGroup_stabilizers_unimodular F E σ hσ M J hJ, GlobalTheory.T.localUnitaryGroup_stabilizers_unimodular_finitePlace F E σ hσ M J hJ,
    GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm F E σ hσ M J hJ, GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer F E σ hσ M J hJ⟩

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  atlas_forward_decl GlobalTheory.adelicUnitaryHaar_holds
