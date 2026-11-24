module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
public import Formalism.LocalRingCardinality.DataDIV
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs

@[expose] public section

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical

noncomputable section

namespace GlobalTheory.Mean4

open GlobalTheory.FlagPoly GlobalTheory.FlagAr

variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev Wt : Type := D.what₂.Tau → Fin Y.N → ℝ

abbrev Fn : Type := Pol D.what₂.Tau Y.N →ₗ[ℝ] ℝ

structure SlopeTestRemainingChoices where

  dir : Wt Y

  w : Y.Comp → ℝ

  Ps : ℝ → Y.Comp → MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ

  ht : Y.ALB → Y.Pt → ℝ

  dense : Y.Comp → Set Y.Pt → Prop

def testI : ℝ := ∑ τ, degFl D.what₂.Tau Y.N (pLow Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j)

variable {Y} (A : SlopeTestRemainingChoices Y) (Φ : ℝ → Fn Y) (hh : Fn Y)


end GlobalTheory.Mean4
