import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportStatementOfDiscreteSeriesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfPrints

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exportSt_of_discrete_series_cover : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.ExportedStatement := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.exportSt_of_hypotheses_alt
end
