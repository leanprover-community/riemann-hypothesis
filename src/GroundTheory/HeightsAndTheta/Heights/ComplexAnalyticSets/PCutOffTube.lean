module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffTube
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeFormCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeEuclMass
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Matrix ComplexSets

noncomputable section

theorem measurable_tubeWeight {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) : Measurable (tubeWeight Q) := by
  have hl : Measurable (logAbsSq Q) :=
    Real.measurable_log.comp ((MvPolynomial.continuous_eval Q).norm.pow 2).measurable
  exact Measurable.ite (measurableSet_le hl measurable_const) ((hl.pow_const 2).inv) measurable_const

theorem measurable_tubeDens {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (tubeDens J A P R φ) := by
  have hAm : Measurable fun x : Fin n → ℂ => A *ᵥ x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).continuous.measurable
  have hw : Measurable ((Metric.closedBall (0 : Fin n → ℂ) R).indicator
      fun x => tubeWeight P (A *ᵥ x)) :=
    ((measurable_tubeWeight P).comp hAm).indicator measurableSet_closedBall
  exact SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
    (continuous_abs.comp continuous_mul).measurable hw _

theorem tubeDens_nonneg {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin (d + 1) → ℂ) : 0 ≤ tubeDens J A P R φ y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity

theorem CutOffTube.proof (hC : TubeFormCompare.Statement) (hE : TubeEuclMass.Statement) :
    CutOffTube.Statement := by
  intro n d J A P R φ hJ hdim hA hP hφ
  obtain ⟨C, hCle⟩ := hC n d J A P R φ hJ hdim hA hφ
  refine Integrable.mono' ((hE n d J A P R hJ hdim hA hP).const_mul C)
    (measurable_tubeDens hA P R φ).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (tubeDens_nonneg J A P R φ y)]
  exact hCle y

end

end GroundTheory.Heights₂.Heights
