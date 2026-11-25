module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContraction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHolds

@[expose] public section

noncomputable section

namespace PositivityTheory.SphericalProduct

theorem jacquet_hecke (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : A2 G :=
  _root_.GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines G

theorem iwahori_u : IwahoriU :=
  _root_.GlobalTheory.CompanionTheory.IwUnit.iwahoriU

theorem dom_u : DomU :=
  _root_.GlobalTheory.CompanionTheory.DomUnitary.domU

end PositivityTheory.SphericalProduct

end
