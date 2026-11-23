module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LUnlinkedIrrOfSeg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LanglandsMultisegmentsOfSeg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ProbeL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.EssSquareIntegrableSegmentsMain2
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

@[expose] public section

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
