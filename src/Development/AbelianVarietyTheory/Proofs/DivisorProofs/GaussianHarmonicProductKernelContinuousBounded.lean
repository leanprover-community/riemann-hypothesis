module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
public import Mathlib.Analysis.InnerProductSpace.PiL2
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
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

noncomputable section

namespace GlobalTheory.HeckeTheta.GaussBound

open GlobalTheory.HeckeTheta

theorem gauss_cont_bound : ∀ (I : Type) [Fintype I] (n : I → ℤ), Continuous (fun w : EuclideanSpace ℂ I => GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)) ∧ ∃ C : ℝ, ∀ w : EuclideanSpace ℂ I, ‖GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)‖ ≤ C * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  intro I _ n
  refine ⟨?_, ⟨Decay.gC n, fun w => ?_⟩⟩
  · unfold gauss
    refine continuous_finsetProd _ fun i _ => ?_
    have hc : Continuous fun w : EuclideanSpace ℂ I => (WithLp.ofLp w) i :=
      (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
    exact ((Decay.continuous_hmon _).comp hc).mul (by fun_prop)
  · have h := Decay.norm_gauss_le n (WithLp.ofLp w)
    have e : ‖w‖ ^ 2 = ∑ i, ‖(WithLp.ofLp w) i‖ ^ 2 := EuclideanSpace.norm_sq_eq w
    rw [e]; exact h

end GlobalTheory.HeckeTheta.GaussBound
