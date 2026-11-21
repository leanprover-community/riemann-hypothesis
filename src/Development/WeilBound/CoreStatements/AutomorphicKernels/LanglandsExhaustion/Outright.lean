import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LanglandsMultisegmentsOfSeg
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ProbeL
import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.EssSquareIntegrableSegmentsMain2
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.SegmentJacquetAllStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation

section
namespace PositivityTheory.Exh

theorem essSquareIntegrableSegments_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.EssSquareIntegrableSegments := by
  have hI : GlobalTheory.Published.IrreducibleAdmissibleGL := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hU := PositivityTheory.Exh.lUnlinkedIrr_of_seg hZ
  exact PositivityTheory.PfEss.essSquareIntegrableSegments_main2
    (PositivityTheory.Exh.langlandsExhaustionGL_of_seg hZ)
    PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top
    (fun k _ _ _ _ _ => PositivityTheory.Exh.lOrderFree_of hU k)
    (fun k _ _ _ _ _ => PositivityTheory.Exh.lSegExists k)
    (fun k _ _ _ _ _ => GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hI hZ)

end PositivityTheory.Exh
end

section
namespace PositivityTheory.Exh

theorem standardCosocleGL_holds : GlobalTheory.Published.StandardCosocleGL := standardCosocleGL_of_seg PositivityTheory.RgGu.segmentRepresentation

theorem langlandsExhaustionGL_holds : GlobalTheory.Published.LanglandsExhaustionGL := langlandsExhaustionGL_of_seg PositivityTheory.RgGu.segmentRepresentation

theorem langlandsMultisegments_holds : GlobalTheory.Published.LanglandsMultisegments := langlandsMultisegments_of_seg PositivityTheory.RgGu.segmentRepresentation

end PositivityTheory.Exh
end
