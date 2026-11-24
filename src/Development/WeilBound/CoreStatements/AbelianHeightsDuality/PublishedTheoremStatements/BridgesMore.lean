module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSqIntCoeffOfIsSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalChartsForFanOfToroidalForFanKS
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspTraceClassOfFactorisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegmentsStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace PositivityTheory.Prw

theorem squareIntegrableSegment_of (h : GlobalTheory.Published.EssSquareIntegrableSegments) : GlobalTheory.Published.SquareIntegrableSegment :=
  GlobalTheory.Published.squareIntegrableSegment_of_ess h

theorem cuspTraceClass_of (h : GlobalTheory.Published.DixmierMalliavinFactorisation) : GlobalTheory.Published.CuspTraceClass :=
  GlobalTheory.Published.cuspTraceClass_of_factorisation h

theorem zelevinskyPolynomialRing_of (h₁ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (h₂ : GlobalTheory.Published.SegmentRepresentation)
    (h₃ : GlobalTheory.Published.GrothendieckRingPolynomial) : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  GlobalTheory.T.zelevinskyGrothendieckPolynomialRing_of_segments h₁ h₂ h₃

theorem toroidalChartsForFan_of (h : GlobalTheory.Published.ToroidalForFanKS) : GlobalTheory.Published.ToroidalChartsForFan :=
  GlobalTheory.toroidalChartsForFan_of_toroidalForFanKS h

end PositivityTheory.Prw
