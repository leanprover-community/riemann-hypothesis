module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.BackOf
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.HasCharPath
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HilbertSchmidtNorms.AbsoluteL2Bound
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.KrDom
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFinal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeometricStatementStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GrowthStatementStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRuleStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRuleStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PolynomialNilpotentPathStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToL2CongrOnUnitaryBisStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.RgExh.Dec.L

theorem back_of_inputs (hLF : LineFormula) (hPN : PolyNilPath) : Back :=
  back_of CompanionTheory.RgExh.Dec.L.SA.assembly_of CompanionTheory.RgExh.Dec.L.AB.absolute_l2_bound GlobalTheory.T.GeometricStatement hLF GlobalTheory.T.HaarExistence hPN GlobalTheory.T.NilpotentRightRule GlobalTheory.T.NilpotentLeftRule
    CompanionTheory.RgExh.Dec.L.WyKR.kRight GlobalTheory.T.GrowthStatement GlobalTheory.T.rgExh_pack

theorem back_of_lineFormula (hLF : LineFormula) : Back := back_of_inputs hLF GlobalTheory.T.PolynomialNilpotentPath

theorem backward_of_line_formula : Back := back_of_lineFormula CompanionTheory.RgExh.Dec.N.S.line_formula

end CompanionTheory.RgExh.Dec.L
