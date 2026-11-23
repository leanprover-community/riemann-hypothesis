module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem UpperTheory.RealTr.rdcalc :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V],
      (∀ f f' : Mat n → V, Set.EqOn f f' (GLs n) → ∀ X, Set.EqOn (Rd X f) (Rd X f') (GLs n)) ∧
      ∀ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) → (∀ X, ContDiffOn ℝ ∞ (Rd X f) (GLs n)) ∧
        (∀ X Y, ∀ g ∈ GLs n, Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g) ∧
        ∀ h ∈ GLs n, ∀ X, ∀ g ∈ GLs n, Rd X (fun y => f (h * y)) g = Rd X f (h * g) ∧
          Rd X (fun y => f (y * h)) g = Rd (h⁻¹ * X * h) f (g * h) := by
  intro n V _ _
  refine ⟨fun f f' e X => GlobalTheory.CompanionTheory.RCalc.Rd_congr X e, fun f hf =>
    ⟨fun X => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf, fun X Y g hg => GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y hf hg,
      fun h hh X g hg => ?_⟩⟩
  have hdet : IsUnit h.det := isUnit_iff_ne_zero.2 hh
  have hhg : h * g ∈ GLs n := by
    show (h * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hh hg
  have hgh : g * h ∈ GLs n := by
    show (g * h).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hg hh
  constructor
  · have hd := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hhg
    have hc : HasFDerivAt (fun y : Mat n => f (h * y))
        ((fderiv ℝ f (h * g)).comp (GlobalTheory.CompanionTheory.RCalc.mulL h)) g :=
      HasFDerivAt.comp (g := f) (f := fun y : Mat n => h * y) g hd.hasFDerivAt
        (GlobalTheory.CompanionTheory.RCalc.mulL h).hasFDerivAt
    simp only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulL_apply, mul_assoc]
  · have hd := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hgh
    have hc : HasFDerivAt (fun y : Mat n => f (y * h))
        ((fderiv ℝ f (g * h)).comp (GlobalTheory.CompanionTheory.RCalc.mulR h)) g :=
      HasFDerivAt.comp (g := f) (f := fun y : Mat n => y * h) g hd.hasFDerivAt
        (GlobalTheory.CompanionTheory.RCalc.mulR h).hasFDerivAt
    have e : g * h * (h⁻¹ * X * h) = g * X * h := by
      rw [Matrix.mul_assoc g h, ← Matrix.mul_assoc h, ← Matrix.mul_assoc h, Matrix.mul_nonsing_inv h hdet,
        Matrix.one_mul, Matrix.mul_assoc]
    simp only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulR_apply, e]
