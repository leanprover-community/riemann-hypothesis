import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParamsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admDict_of_weight_blockChar : GlobalTheory.TwSys.Cheb → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  atlas_forward_decl _root_.GlobalTheory.BridgeAdmDict.main_alt_alt
end
