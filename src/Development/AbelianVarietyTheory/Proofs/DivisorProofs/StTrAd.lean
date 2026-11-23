module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffPolynomialConjugationDerivMemShapeSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraceSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraceSumInnerOfRangeLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoeffVectorsLieInFiniteDimensionalSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerMulInnerProj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.PsCo.Pc3

theorem stTrAd : GlobalTheory.PsCo.Pc1.StTrAd :=
  stTrAd_of
    GlobalTheory.ShapeSmoothFinite.stShape
    GlobalTheory.PsCo.Pc1.B.cutoffPolynomial_conjugation_deriv_mem_shapeSpan
    uFin rangeShape
    GlobalTheory.OpTrace.hasTrace_sum_inner_of_range_le
    GlobalTheory.Pc3.conjDeriv

end GlobalTheory.PsCo.Pc3
