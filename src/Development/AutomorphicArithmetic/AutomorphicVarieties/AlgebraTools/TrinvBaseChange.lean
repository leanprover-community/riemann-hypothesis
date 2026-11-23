module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.trinv_baseChange :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) (B' : Type) [CommRing B'] [Algebra B B'], ∃ T' : TrInv B' (B' ⊗[B] E), (∀ y, T'.st (1 ⊗ₜ y) = 1 ⊗ₜ T.st y) ∧ ∀ y, T'.tr (1 ⊗ₜ y) = algebraMap B B' (T.tr y) := by
  intro B E _ _ _ T B' _ _
  let s : B' ⊗[B] E →ₗ[B'] B' ⊗[B] E := T.st.baseChange B'
  let t : B' ⊗[B] E →ₗ[B'] B' :=
    (AlgebraTensorModule.rid B B' B').toLinearMap ∘ₗ T.tr.baseChange B'
  have hs : ∀ (a : B') (y : E), s (a ⊗ₜ y) = a ⊗ₜ T.st y := fun a y => by simp [s]
  have ht : ∀ (a : B') (y : E), t (a ⊗ₜ y) = T.tr y • a := fun a y => by simp [t]
  refine ⟨⟨s, ?_, ?_, t, ?_, ?_⟩, fun y => hs 1 y, fun y => ?_⟩
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, map_add (f := _), ha, hb]
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd => simp only [add_mul, mul_add, map_add (f := _), hc, hd]
      | tmul b v =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, hs, T.st_mul, mul_comm a b]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a u => simp only [hs, T.st_st]
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, map_add (f := _), ha, hb]
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd => simp only [add_mul, mul_add, map_add (f := _), hc, hd]
      | tmul b v =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, ht, T.tr_comm u v, mul_comm a b]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a u => simp only [hs, ht, T.tr_st]
  · show t (1 ⊗ₜ y) = _
    rw [ht, Algebra.algebraMap_eq_smul_one]
