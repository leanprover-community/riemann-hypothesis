import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology

namespace PositivityTheory.Rg.SwEis.Hd

open PositivityTheory.RgEis.Hd

theorem eisStrong : PositivityTheory.Rg.Sw.Glob.EisStrong :=
  GlobalTheory.T.eisenstein_topology dict dictInf (cmGood_of stdGood dict dictInf) grpTop bdetLaw extLaw (parLaw_of bdetLaw extLaw grpTop)
    sgAll GlobalTheory.T.standard_section_exists (GlobalTheory.T.eisenstein_iwasawa_estimate (GlobalTheory.T.chart_section_exists dict dictInf GlobalTheory.T.standard_section_exists)) (GlobalTheory.T.scalar_section_exists secLaw (wallLaw_of secLaw))
    (GlobalTheory.T.eisenstein_far_estimate htLip) GlobalTheory.T.eisenstein_gluing

end PositivityTheory.Rg.SwEis.Hd
