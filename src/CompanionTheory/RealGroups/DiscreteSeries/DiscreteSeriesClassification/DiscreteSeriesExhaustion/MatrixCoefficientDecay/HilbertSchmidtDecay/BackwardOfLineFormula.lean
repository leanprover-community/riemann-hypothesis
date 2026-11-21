import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.HasCharPath
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HilbertSchmidtNorms.AbsoluteL2Bound
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeometricStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistenceStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRuleStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRule
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.KrDom
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GrowthStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToL2CongrOnUnitaryBis
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PolynomialNilpotentPathStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFinal

section
namespace CompanionTheory.RgExh.Dec.L

open CompanionTheory.RgExh

theorem back_of (hA : Assembly) (h1 : AbsoluteL2Bound) (h2 : Geo) (h3 : LineFormula) (h4 : HaarExists) (h5 : PolyNilPath)
    (h6 : N.RightRule) (h7 : N.LeftRule) (h8 : KRight) (h9 : Growth) (h10 : Pack) : Back :=
  fun h0 => hA h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h0

end CompanionTheory.RgExh.Dec.L
end

section
namespace CompanionTheory.RgExh.Dec.L

theorem back_of_inputs (hLF : LineFormula) (hPN : PolyNilPath) : Back :=
  back_of CompanionTheory.RgExh.Dec.L.SA.assembly_of CompanionTheory.RgExh.Dec.L.AB.absolute_l2_bound GlobalTheory.T.GeometricStatement hLF GlobalTheory.T.HaarExistence hPN GlobalTheory.T.NilpotentRightRule GlobalTheory.T.NilpotentLeftRule
    CompanionTheory.RgExh.Dec.L.WyKR.kRight GlobalTheory.T.GrowthStatement GlobalTheory.T.rgExh_pack

theorem back_of_lineFormula (hLF : LineFormula) : Back := back_of_inputs hLF GlobalTheory.T.PolynomialNilpotentPath

theorem backward_of_line_formula : Back := back_of_lineFormula CompanionTheory.RgExh.Dec.N.S.line_formula

end CompanionTheory.RgExh.Dec.L
end
