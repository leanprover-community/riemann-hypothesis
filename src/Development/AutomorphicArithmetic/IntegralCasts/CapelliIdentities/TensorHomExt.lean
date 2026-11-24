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

theorem UpperTheory.Reformulated.B.Qk54.tensor_hom_ext :
    ∀ {A A' C Ω : Type}
    [inst : CommRing A] [inst_1 : CommRing A'] [inst_2 : CommRing C] [inst_3 : Algebra A A'] [inst_4 : Algebra A C]
    [inst_5 : CommRing Ω] {u v : TensorProduct A C A' →+* Ω},
    (∀ (c : C), (u : TensorProduct A C A' → Ω) (c ⊗ₜ[A] (1 : A')) = (v : TensorProduct A C A' → Ω) (c ⊗ₜ[A] (1 : A'))) →
      (∀ (b : A'), (u : TensorProduct A C A' → Ω) ((1 : C) ⊗ₜ[A] b) = (v : TensorProduct A C A' → Ω) ((1 : C) ⊗ₜ[A] b)) →
        u = v := by
  intro A A' C Ω _ _ _ _ _ _ u v h₁ h₂
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c b =>
    have e : c ⊗ₜ[A] b = (c ⊗ₜ[A] (1 : A')) * ((1 : C) ⊗ₜ[A] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
