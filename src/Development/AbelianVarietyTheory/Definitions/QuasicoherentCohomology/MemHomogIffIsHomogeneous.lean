module

public import Mathlib.LinearAlgebra.Dual.BaseChange
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Contraction

@[expose] public section

open TensorProduct Module
open scoped DirectSum

namespace GlobalTheory
namespace SymAlg

variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

section BaseChange

variable {S : Type*} [CommRing S] [Algebra R S] {W : Type*} [AddCommGroup W] [Module R W]
  [Module S W] [IsScalarTower R S W]

theorem isBaseChange_dual [Module.Finite R M] [Module.Projective R M] {j : M →ₗ[R] W}
    (h : IsBaseChange S j) : IsBaseChange S h.toDual := by
  let Φ : S ⊗[R] Dual R M →ₗ[S] Dual S W := h.toDual.liftBaseChange S
  let e := lTensorHomEquivHomLTensor R M S R
  have key : ∀ (t : S ⊗[R] Dual R M) (m : M), Φ t (j m) = TensorProduct.rid R S (e t m) := by
    intro t m
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
    | tmul s ξ =>
      simp [Φ, e, h.toDual_comp_apply, Algebra.smul_def, mul_comm]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨?_, ?_⟩)
    (fun ξ => by change Φ _ = _; simp [Φ])
  · rw [injective_iff_map_eq_zero]
    intro t ht
    apply e.injective
    ext m
    apply (TensorProduct.rid R S).injective
    rw [← key, ht]
    simp
  · intro φ
    refine ⟨e.symm ((TensorProduct.rid R S).symm.toLinearMap ∘ₗ φ.restrictScalars R ∘ₗ j), ?_⟩
    refine h.algHom_ext _ _ fun m => ?_
    rw [key]
    simp

end BaseChange

end SymAlg
end GlobalTheory
