module

public import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct PiTensorProduct

namespace GlobalTheory

noncomputable section

universe u v w

variable {A : Type u} [CommRing A] {σ : Type w} [Fintype σ] [DecidableEq σ] {X : σ → Type v}
  [∀ s, CommRing (X s)] [∀ s, Algebra A (X s)] {S : Type*} [CommRing S] [Algebra A S]

def piTensorLift (f : ∀ s, X s →ₐ[A] S) : (⨂[A] s, X s) →ₐ[A] S :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra A σ S).compLinearMap fun s => (f s).toLinearMap)
    (by simp) (fun x y => by simp [Finset.prod_mul_distrib])


omit [DecidableEq σ] in
@[simp] theorem piTensorLift_tprod (f : ∀ s, X s →ₐ[A] S) (x : ∀ s, X s) :
    piTensorLift f (tprod A x) = ∏ s, f s (x s) := by
  refine (PiTensorProduct.lift.tprod x).trans ?_
  simp

@[simp] theorem piTensorLift_comp_single (f : ∀ s, X s →ₐ[A] S) (s : σ) :
    (piTensorLift f).comp (singleAlgHom s) = f s := by
  ext x
  rw [AlgHom.comp_apply, singleAlgHom_apply, piTensorLift_tprod,
    Finset.prod_eq_single s (fun t _ ht => by simp [Pi.mulSingle_eq_of_ne ht]) (by simp)]
  simp

theorem piTensorLift_single (f : ∀ s, X s →ₐ[A] S) (s : σ) (x : X s) :
    piTensorLift f (singleAlgHom s x) = f s x := congr($(piTensorLift_comp_single f s) x)


end

end GlobalTheory
