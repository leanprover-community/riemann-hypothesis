module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOfSegRep2
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedCommPole
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleaveStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation

@[expose] public section

noncomputable section

namespace GlobalTheory.RgGu.Holds

theorem genericUnlinkedGL_holds : GlobalTheory.Published.GenericUnlinkedGL :=
  GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2 PositivityTheory.RgGu.segmentRepresentation

theorem lUnlinkedIrr_holds :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedIrr k :=
  GlobalTheory.RgGu.Unl.lUnlinkedIrr_pole PositivityTheory.RgGu.segmentRepresentation

theorem lUnlinkedComm_holds :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedComm k :=
  GlobalTheory.RgGu.Unl.lUnlinkedComm_pole PositivityTheory.RgGu.segmentRepresentation

end GlobalTheory.RgGu.Holds

end
