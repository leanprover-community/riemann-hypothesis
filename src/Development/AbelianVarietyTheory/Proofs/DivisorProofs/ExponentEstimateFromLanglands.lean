import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStatementOfSmallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStatementOfFrameGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExpansionStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCutStatement

section
set_option autoImplicit false

namespace GlobalTheory.BigOn

theorem expSt_of_hypotheses :
    GlobalTheory.Published.ClozelCohomological →
      GlobalTheory.Published.CohomologicalCsdTempered →
      GlobalTheory.Published.HeckeLAdicCharacter →
      GlobalTheory.Published.ChebotarevDegreeOne →
      GlobalTheory.Published.DiscreteSpectrumGL →
      GlobalTheory.Published.GaloisRepOfPolarizedCuspidal →
      GlobalTheory.Published.BaseChangeDefiniteUnitary →
      GlobalTheory.Published.BhattScholzeCrystallineLattices →
      GlobalTheory.Published.HeckeLAdicCharacterAbove →
      GlobalTheory.Published.LocalLanglandsGL →
      GlobalTheory.BigOn.ExpSt :=
  fun hCoh hTemp hHecke hCheb hDisc hGal hBC hBS hAbove hLL =>
    GlobalTheory.T.expansion_of_numerics_model GlobalTheory.T.weylLattice_exact_exponent_block_cut GlobalTheory.ExpTie.numSt GlobalTheory.T.sum_expansion_statement
      (GlobalTheory.T.model_statement_of_frame_galois hBS hCheb GlobalTheory.T.SmallStatement (GlobalTheory.T.FrameStatement GlobalTheory.T.SmallStatement)
        (GlobalTheory.T.galois_statement_of_small hCoh hTemp hHecke hCheb hDisc hGal hBC hBS hAbove hLL GlobalTheory.T.SmallStatement))

end GlobalTheory.BigOn
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_estimate_from_langlands : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.BigOn.ExpSt := by
  atlas_forward_decl GlobalTheory.BigOn.expSt_of_hypotheses
