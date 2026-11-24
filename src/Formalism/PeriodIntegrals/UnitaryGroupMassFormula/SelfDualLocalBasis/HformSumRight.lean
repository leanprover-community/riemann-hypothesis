module

public import Formalism.PeriodIntegrals.SelfDualLoc
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

noncomputable section

namespace PI.SelfDualLoc.W

open PI.SelfDualLoc

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (σ : A →+* A) (J : Matrix n n A)

theorem hform_add_right (x y y' : n → A) :
    hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [PI.SelfDualLoc.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right (x : n → A) (c : A) (y : n → A) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [PI.SelfDualLoc.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_add_left (x x' y : n → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [PI.SelfDualLoc.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_left (c : A) (x y : n → A) :
    hform σ J (c • x) y = σ c * hform σ J x y := by
  simp only [PI.SelfDualLoc.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_zero_left (y : n → A) : hform σ J 0 y = 0 := by
  simp [PI.SelfDualLoc.hform]

theorem hform_zero_right (x : n → A) : hform σ J x 0 = 0 := by
  simp [PI.SelfDualLoc.hform]

theorem hform_sum_right {ι : Type} (s : Finset ι) (x : n → A) (f : ι → n → A) :
    hform σ J x (∑ k ∈ s, f k) = ∑ k ∈ s, hform σ J x (f k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact hform_zero_right σ J x
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_right, ih]

theorem hform_sum_left {ι : Type} (s : Finset ι) (f : ι → n → A) (y : n → A) :
    hform σ J (∑ k ∈ s, f k) y = ∑ k ∈ s, hform σ J (f k) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact hform_zero_left σ J y
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_left, ih]

theorem hform_map {B : Type} [CommRing B] (τ : B →+* B) (f : A →+* B)
    (hf : ∀ a, f (σ a) = τ (f a)) (x y : n → A) :
    hform τ (J.map f) (fun i => f (x i)) (fun i => f (y i)) = f (hform σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PI.SelfDualLoc.hform, map_sum, map_mul, hf, Matrix.map_apply]

end PI.SelfDualLoc.W
