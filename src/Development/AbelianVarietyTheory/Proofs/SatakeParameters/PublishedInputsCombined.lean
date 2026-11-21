import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiTempered
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguezStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsPowValEqZpow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RegularAlgebraicPurityOfClozel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeLAdicParameterAboveOfAlgebraicCharacterWD
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CohomologicalCsdTemperedOfSegmentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdanStatement

section
namespace GlobalTheory

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

theorem depthZeroJacquetInjective_of_admissible :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.MoyPrasadJacquetIso →
      GlobalTheory.Published.DepthZeroJacquetInjective := by
  intro hBZ hMP k _ _ _ _ n s d e π v hv h0
  have hadm := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hb := hMP k n s d e π.V π.π hadm
  have h00 : (0 : π.V) ∈ fixed π.π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    first
      | exact Submodule.zero_mem _
      | exact fun _ => map_zero _
      | simp [fixed]
  exact hb.injOn hv h00 (by simpa using h0)

end GlobalTheory
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_above_l : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.Published.CaraianiLocalGlobal → GlobalTheory.Published.LocalGlobalAboveL := by
  first | exact @GlobalTheory.CaraianiAboveL.main | exact GlobalTheory.CaraianiAboveL.main | (intros; apply GlobalTheory.CaraianiAboveL.main <;> assumption)
end

section
section
namespace GlobalTheory.NRows.HypothesesBridge

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.MoyPrasadJacquetIso → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.CaraianiTempered → GlobalTheory.Published.TemperedProductOfSquareIntegrable → GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.GelfandKazhdanDual → GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.ClozelPurity → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.NRows.Hypotheses₂ := by
  intro hBZ hBern hGeo hTD hMP hMin hJS hFin hCT hTSI hESS hGK hGRP hCLGD hCP hCC hArt hChA hAlg hBerger hCheb hLL
  have hCSD := GlobalTheory.T.local_global_of_gelfand_kazhdan hGK
  exact
    { bz := hBZ
      bern := hBern
      geo := hGeo
      unl := GlobalTheory.TotDisjUnlinked.main hTD
      mp := GlobalTheory.depthZeroJacquetInjective_of_admissible hBZ hMP
      howe := GlobalTheory.T.howe_duality_of_minguez hMin
      js := hJS
      fin := hFin
      temp := GlobalTheory.T.cohomological_csd_tempered_of_segments hCT hTSI hESS
      gal := hCSD.2 hGRP
      car := GlobalTheory.T.local_global_above_l hFin hLL (hCSD.1 hCLGD)
      clo := GlobalTheory.regularAlgebraicPurity_of_clozel hCP hCC
      art := hArt
      chA := hChA
      chP := GlobalTheory.heckeLAdicParameterAbove_of_algebraicCharacterWD hAlg
      berger := hBerger
      cheb := hCheb }

end GlobalTheory.NRows.HypothesesBridge
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.published_inputs_combined : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.MoyPrasadJacquetIso → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.CaraianiTempered → GlobalTheory.Published.TemperedProductOfSquareIntegrable → GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.GelfandKazhdanDual → GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.ClozelPurity → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.NRows.Hypotheses₂ := by
  atlas_forward_decl GlobalTheory.NRows.HypothesesBridge.main
end
