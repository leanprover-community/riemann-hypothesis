module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFiniteFibreDim
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeJacMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeKrullDimLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentAverage
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentDim
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PKernelProjMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentGaussInvariant
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacCompress
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PConormalGenerationGeneric
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PJacobianRankGeneric
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

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

theorem coneTangentAverage_inter (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J) (hm : 0 < m) (hmn : m ≤ n)
    (hfib : ∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤)
    (A : Set (EuclideanSpace ℂ (Fin n))) (hA : MeasurableSet A) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ y in coneSet h J ∩ A,
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      ∫⁻ y in coneSet h J ∩ A, tangentGaussProfile n m ‖y‖
        ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
  have hMass : ConeLocalMass.Statement := ConeLocalMass.of_open ConeFiniteFibreDim.proof
  have hMeas : ConeJacMeasurable.Statement :=
    ConeJacMeasurable.proof TangentJacCompress.proof KernelProjMeasurable.proof
  have hDim : ConeTangentDim.Statement :=
    ConeTangentDim.proof (ConeKrullDimLe.proof ConeFiniteFibreDim.proof) NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)
  have hInv : TangentGaussInvariant.Statement := TangentGaussInvariant.proof
  have hres : (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
      Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J ∩ A) =
      ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
        Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)).restrict A := by
    rw [Measure.restrict_restrict hA, Set.inter_comm]
  rw [hres]
  have hS : SFinite ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
      Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)) :=
    sFinite_restrict_of_ball _ _ (hMass n m h J hJ hm hmn hfib)
  have hG : Measurable fun π : Fin m → Fin n → ℂ => matGauss π := by
    unfold matGauss
    exact (by fun_prop : Continuous fun π : Fin m → Fin n → ℂ =>
      Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal
  have hP : Continuous fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) =>
      linProj p.1 p.2 := by
    unfold linProj
    fun_prop
  have hF : AEMeasurable
      (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) =>
        matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y)))
      ((volume : Measure (Fin m → Fin n → ℂ)).prod
        ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J))) :=
    (hG.comp measurable_fst).aemeasurable.mul
      (((measurable_one.indicator Metric.isOpen_ball.measurableSet).comp
        hP.measurable).aemeasurable.mul (hMeas n m h J hJ hm hmn hfib).ennreal_ofReal)
  have hFA : AEMeasurable
      (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) =>
        matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y)))
      ((volume : Measure (Fin m → Fin n → ℂ)).prod
        (((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J)).restrict A)) := by
    have hpr := Measure.prod_restrict (μ := (volume : Measure (Fin m → Fin n → ℂ)))
      (ν := (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
        Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)) Set.univ A
    rw [Measure.restrict_univ] at hpr
    rw [hpr]
    exact hF.restrict
  rw [show (fun π : Fin m → Fin n → ℂ => matGauss π *
      ∫⁻ y in A, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y)
          ∂((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J))) =
      fun π => ∫⁻ y in A, matGauss π *
        ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y))
          ∂((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J)) from
    funext fun π => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm,
    lintegral_lintegral_swap hFA]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hDim n m h J hJ hm hmn hfib,
    ae_restrict_mem (isClosed_coneSet h J).measurableSet] with y hy hyC
  simp only [← mul_assoc]
  exact hInv n m hm hmn _ hy y (mem_coneTangent_self h hJ hyC)

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
