import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisibilityStatement
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.PositiveSumGrowth.AbsAPos

namespace PositivityTheory.RgEis.Sp

open ResidueKilled.Tr

theorem siegelEisensteinContinuation_of (hD : Dict) (hI : DictInf) (hL : SecLaw) (hW : WallLaw) (hG : CMGood)
    (hT : GrpTop) (hB : BdetLaw) (hE : ExtLaw) (hP : ParLaw) (hS : SgAll) : GlobalTheory.Published.SiegelEisensteinContinuation :=
  ResidueKilled.Tr.tTop hG hT hB hE hP hS (GlobalTheory.T.chart_section_exists hD hI GlobalTheory.T.standard_section_exists) (GlobalTheory.T.scalar_section_exists hL hW) GlobalTheory.T.divisibility_statement

end PositivityTheory.RgEis.Sp
