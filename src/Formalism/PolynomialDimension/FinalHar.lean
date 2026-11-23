module

public import Formalism.PolynomialDimension.StatementHar
import Formalism.PolynomialDimension.MultinomialDepth.HarmonicDecompositionHolds
public import Formalism.PolynomialDimension.MultinomialDepth.PairingAdjointLaplacianHolds
public import Formalism.PolynomialDimension.MultinomialDepth.SqrtFockGaussLatticeComparisonHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace Formalism.CountingSumsFrames.Top

theorem slTwo : Formalism.CountingSumsFrames.SlTwo := Formalism.CountingSumsFrames.slTwoCommutator_holds
theorem harProj : Formalism.CountingSumsFrames.HarProj := Formalism.CountingSumsFrames.harmonicProjection_holds
theorem levelProj : Formalism.CountingSumsFrames.LevelProj := Formalism.CountingSumsFrames.isotypicProjection_holds
theorem gaussProj : Formalism.CountingSumsFrames.GaussProj := Formalism.CountingSumsFrames.gaussLatticeProjection_holds
theorem gaussLemmaH : Formalism.CountingSumsFrames.GaussLemmaH := Formalism.CountingSumsFrames.gaussLemmaPairing_holds
theorem levelLattice : Formalism.CountingSumsFrames.LevelLattice := Formalism.CountingSumsFrames.isotypicLattice_holds
theorem harQuot : Formalism.CountingSumsFrames.HarQuot := Formalism.CountingSumsFrames.harmonicQuotient_holds

end Formalism.CountingSumsFrames.Top
