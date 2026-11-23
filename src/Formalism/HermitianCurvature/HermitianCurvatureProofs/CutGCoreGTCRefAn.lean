module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefCut
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem reference_annulus_holds : GTCRefAn := by
  intro TT α c hTT hα hre R hR hR2
  have hpt : ∀ θ : ℝ, TT < Complex.normSq (circleMap 0 R θ) := by
    intro θ
    have h1 : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    rw [Complex.normSq_eq_norm_sq, h1]
    exact hR2
  have hcα : Continuous (fun θ : ℝ => α (circleMap 0 R θ)) :=
    hα.continuousOn.comp_continuous (continuous_circleMap 0 R) hpt
  have hd : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I := by
    funext θ
    exact deriv_circleMap 0 R θ
  have hF : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) := by
    have h2 : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ) := by
      rw [hd]
      exact (continuous_circleMap 0 R).mul continuous_const
    exact h2.smul hcα
  have key : ∀ θ : ℝ, Complex.imCLM (deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) = c := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul, Complex.imCLM_apply]
    rw [← hre (circleMap 0 R θ) (hpt θ)]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  unfold circleIntegral
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hF.intervalIntegrable _ _)]
  simp only [key]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
