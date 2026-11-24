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

namespace GlobalTheory.RingHomTensorExtensionality

theorem ringHom_ext_tensor {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] {g h : TensorProduct R A B →+* C}
    (ha : ∀ a : A, g (a ⊗ₜ[R] (1 : B)) = h (a ⊗ₜ[R] (1 : B)))
    (hb : ∀ b : B, g ((1 : A) ⊗ₜ[R] b) = h ((1 : A) ⊗ₜ[R] b)) : g = h := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    have e : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, ha, hb]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.RingHomTensorExtensionality
