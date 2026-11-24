module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaFibreSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.crofton_formula_fibre_sum : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ φ : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable φ →
    (∀ s : ℝ≥0∞, IsOpen {y | s < φ y} ∧ IsScaleStable {y | s < φ y}) →
    Measurable (fun π : Fin (e + 1) → Fin n → ℂ => ∑' y : fibrePts (coneSet h W) π, φ y) ∧
      planeMass n e * ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, φ y ∂(gaussM (e + 1) n) =
        gaussM (e + 1) n Set.univ * ∫⁻ y in coneBall h W, φ y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum | exact GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum | (intros; apply GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum <;> assumption)
