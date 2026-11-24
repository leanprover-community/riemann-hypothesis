module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem continuous_expChart (k r : ℕ) (S : Set (Mat k r)) :
    Continuous (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) i j :
        lieE S → Mt k r) := by
  set n := 2 * r + k + 1
  have hexp : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp A) := by
    let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    have : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ) PseudoMetricSpace.toUniformSpace := by
      let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
      exact FiniteDimensional.complete ℂ _
    let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra (R := ℚ)
    exact NormedSpace.exp_continuous
  have hun : Continuous (fun x : EuclideanSpace ℝ (Fin n × Fin n × Bool) => unrealify x) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hmk : Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := Complex.equivRealProdCLM.symm.continuous
    show Continuous (fun x : EuclideanSpace ℝ (Fin n × Fin n × Bool) => (⟨x (i, j, false), x (i, j, true)⟩ : ℂ))
    exact hmk.comp ((PiLp.continuous_apply 2 (fun _ : Fin n × Fin n × Bool => ℝ) (i, j, false)).prodMk
      (PiLp.continuous_apply 2 (fun _ : Fin n × Fin n × Bool => ℝ) (i, j, true)))
  have hall : Continuous (fun x : lieE S =>
      NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) :=
    (hexp.comp hun).comp continuous_subtype_val
  exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hall)

theorem measurableSet_expBall (k r : ℕ) (S : Set (Mat k r)) (ρ : ℝ) :
    MeasurableSet (expBall (k := k) (r := r) S ρ) := by
  have hball : IsSigmaCompact (Metric.ball (0 : lieE S) ρ) :=
    isSigmaCompact_iff_sigmaCompactSpace.2
      (haveI : LocallyCompactSpace (Metric.ball (0 : lieE S) ρ) := Metric.isOpen_ball.locallyCompactSpace
       inferInstance)
  obtain ⟨K, hK, hKU⟩ := hball.image (continuous_expChart k r S)
  unfold expBall
  rw [← hKU]
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

theorem tBallMeas : TBallMeas := by
  intro k r m ρ
  have hc : Continuous (fun x : Mt k r => fun i j => (m⁻¹ * Matrix.of x) i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact (measurableSet_expBall (k := k) (r := r) (UWb k r) ρ).preimage hc.measurable

end PI.RhsWLim.W
