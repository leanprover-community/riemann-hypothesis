module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableWeightedHeckeThetaKernelHalfSpace
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

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace : ∀ (I : Type) [Fintype I] {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (q : (I → ℝ) → ℝ) (B R : ℝ), (∃ i, n i ≠ 0) → (∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) → (∃ δ : ℝ, 0 < δ ∧ ∀ j, a j ≠ 0 → e j ≠ 0 → δ ≤ ‖e j‖) → Measurable q → (∀ y, |q y| ≤ B) → (∀ y, q y ≠ 0 → ∀ i j, y i - y j ≤ R) → MeasureTheory.AEStronglyMeasurable (fun y => (q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y) MeasureTheory.volume ∧ ∀ σ : ℝ, MeasureTheory.Integrable (fun y => ‖(q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y‖ * Real.exp (σ * ∑ i, y i)) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) := by
  first | exact @GlobalTheory.HeckeTheta.Decay.integrable_weight_theta | exact GlobalTheory.HeckeTheta.Decay.integrable_weight_theta | (intros; apply GlobalTheory.HeckeTheta.Decay.integrable_weight_theta <;> assumption)
