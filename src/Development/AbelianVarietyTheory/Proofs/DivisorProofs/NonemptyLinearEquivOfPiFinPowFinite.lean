module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfCardHomStatement
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.PowCancel

def linMapPiEquiv (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (l : ℕ) :
    (X →ₗ[R] (Fin l → M)) ≃ (Fin l → (X →ₗ[R] M)) where
  toFun f i := (LinearMap.proj i).comp f
  invFun g := LinearMap.pi g
  left_inv f := by ext x i; rfl
  right_inv g := by funext i; ext x; rfl

theorem card_linMap_pow (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (l : ℕ) :
    Nat.card (X →ₗ[R] (Fin l → M)) = Nat.card (X →ₗ[R] M) ^ l := by
  rw [Nat.card_congr (linMapPiEquiv R X M l), Nat.card_fun, Nat.card_fin]

theorem cancel_pow : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M]
    [AddCommGroup N] [Module R N] [Finite N] (l : ℕ), 0 < l →
    Nonempty ((Fin l → M) ≃ₗ[R] (Fin l → N)) → Nonempty (M ≃ₗ[R] N) := by
  intro R _ M N _ _ _ _ _ _ l hl ⟨e⟩
  refine GlobalTheory.T.nonempty_linearEquiv_of_card_hom_eq R M N ?_
  intro X _ _ _
  have h1 : Nat.card (X →ₗ[R] (Fin l → M)) = Nat.card (X →ₗ[R] (Fin l → N)) :=
    Nat.card_congr
      { toFun := fun f => e.toLinearMap.comp f
        invFun := fun g => e.symm.toLinearMap.comp g
        left_inv := fun f => by ext x; simp
        right_inv := fun g => by ext x; simp }
  rw [card_linMap_pow, card_linMap_pow] at h1
  exact Nat.pow_left_injective hl.ne' h1

end GlobalTheory.PowCancel
