module

public import Mathlib.RingTheory.TensorProduct.Basic
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

namespace GlobalTheory.TensorRingHomExtensionality

open scoped TensorProduct

theorem ringHom_ext_tensor {R S B C : Type} [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] (φ ψ : TensorProduct R S B →+* C)
    (h₁ : ∀ s : S, φ (s ⊗ₜ[R] (1 : B)) = ψ (s ⊗ₜ[R] (1 : B)))
    (h₂ : ∀ b : B, φ ((1 : S) ⊗ₜ[R] b) = ψ ((1 : S) ⊗ₜ[R] b)) : φ = ψ := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s b =>
    have h : s ⊗ₜ[R] b = (s ⊗ₜ[R] (1 : B)) * ((1 : S) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.TensorRingHomExtensionality
