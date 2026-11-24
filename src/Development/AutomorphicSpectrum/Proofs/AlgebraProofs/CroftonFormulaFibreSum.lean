module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaOpenConeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RandomSetSumExpectationStatement
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.CroftonFormulaFibreSum
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


theorem _root_.GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ φ : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable φ →
    (∀ s : ℝ≥0∞, IsOpen {y | s < φ y} ∧ IsScaleStable {y | s < φ y}) →
    Measurable (fun π : Fin (e + 1) → Fin n → ℂ => ∑' y : fibrePts (coneSet h W) π, φ y) ∧
      planeMass n e * ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, φ y ∂(gaussM (e + 1) n) =
        gaussM (e + 1) n Set.univ * ∫⁻ y in coneBall h W, φ y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  intro n e δ h W f hW hf hδ φ hφ hlev
  have hcnt : ∀ s : ℝ≥0∞, Measurable fun π : Fin (e + 1) → Fin n → ℂ =>
      cntOver (coneSet h W ∩ {y | s < φ y}) π (firstCoordVec (e + 1)) := fun s =>
    ModelDimension.FnCrofton.measurable_cntOver_first (isSigmaCompact_cone_inter h W (hlev s).1)
  obtain ⟨hm, hi⟩ := GlobalTheory.T.random_set_sum_expectation (planeMass n e • gaussM (e + 1) n)
    ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W))
    (fun π => fibrePts (coneSet h W) π) φ (gaussM (e + 1) n Set.univ) hφ
    (fun s => by
      simp only [ModelDimension.FnCrofton.encard_fibrePts_inter]
      exact hcnt s)
    (fun s => by
      have hA := (hlev s).1
      have T := GlobalTheory.T.crofton_formula_open_cone n e δ h W f hW hf hδ {y | s < φ y} hA (hlev s).2
      simp only [ModelDimension.FnCrofton.encard_fibrePts_inter]
      rw [lintegral_smul_measure, smul_eq_mul, Measure.restrict_apply hA.measurableSet, gaussM,
        lintegral_withDensity_eq_lintegral_mul _ (ModelDimension.FnCrofton.measurable_matrix_gaussian _ _) (hcnt s)]
      have hset : {y | s < φ y} ∩ coneBall h W =
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ {y | s < φ y}} := by
        ext y
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, h3, h1⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h3, h1, h2⟩
      rw [hset]
      simpa only [Pi.mul_apply, gaussM] using T)
  refine ⟨hm, ?_⟩
  rw [lintegral_smul_measure, smul_eq_mul] at hi
  exact hi
