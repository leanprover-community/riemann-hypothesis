module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodDiffThetaFourthOfSigmaStarAddition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex

theorem _root_.GlobalTheory.T.halfPeriodDiffThetaFourth_of_sigmaStar_addition : Formalism.L2.Th1.F.SgStarAdd → (∀ (τ : UpperHalfPlane) (z : ℂ), Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z) → (∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0) → (∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ) → ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ := by
  first | exact @GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of | exact GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of | (intros; apply GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of <;> assumption)
