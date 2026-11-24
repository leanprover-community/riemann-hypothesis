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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.Qk3

theorem aux1 {A : Type} [CommRing A] : RingHomInvPair (RingHom.id A) (RingHom.id A) :=
  RingHomInvPair.ids

noncomputable def unopS (A E S : Type) [CommRing A] [Ring E] [Algebra A E]
    [CommRing S] [Algebra A S] : TensorProduct A S Eᵐᵒᵖ →ₗ[S] TensorProduct A S E :=
  LinearMap.baseChange S (MulOpposite.opLinearEquiv A).symm.toLinearMap

theorem unopS_mul {A E : Type} [CommRing A] [Ring E] [Algebra A E]
    (S : Type) [CommRing S] [Algebra A S] (x y : TensorProduct A S Eᵐᵒᵖ) :
    unopS A E S (x * y) = unopS A E S y * unopS A E S x := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add (f := _), map_add (f := _), h₁, h₂, mul_add]
  | tmul s e =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add (f := _), map_add (f := _), h₁, h₂, add_mul]
    | tmul t f => simp [unopS, Algebra.TensorProduct.tmul_mul_tmul, mul_comm s t]

end UpperTheory.Reformulated.B.Qk3
