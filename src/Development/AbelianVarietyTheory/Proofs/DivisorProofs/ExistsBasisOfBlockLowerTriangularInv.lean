module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Basis.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace GlobalTheory

open Matrix

theorem exists_basis_of_blockLowerTriangular_inv (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]
    (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M)
    (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O)
    (h1 : P * P' = 1) (h2 : P' * P = 1) (hz : ∀ i j, P (Sum.inl i) (Sum.inr j) = 0) :
    ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  have hAA : P.toBlocks₁₁ * P'.toBlocks₁₁ = 1 := by
    ext i i'
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl i')
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁] using this
  have hA'A : P'.toBlocks₁₁ * P.toBlocks₁₁ = 1 := mul_eq_one_comm.mp hAA
  have hAB : P.toBlocks₁₁ * P'.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂] using this
  have hB : P'.toBlocks₁₂ = 0 := by
    calc P'.toBlocks₁₂ = (P'.toBlocks₁₁ * P.toBlocks₁₁) * P'.toBlocks₁₂ := by rw [hA'A, Matrix.one_mul]
      _ = P'.toBlocks₁₁ * (P.toBlocks₁₁ * P'.toBlocks₁₂) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hAB, Matrix.mul_zero]
  have hb : ∀ a j, P' (Sum.inl a) (Sum.inr j) = 0 := fun a j => by
    simpa [Matrix.toBlocks₁₂] using congrFun (congrFun hB a) j
  have hDD : P.toBlocks₂₂ * P'.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h1 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hb, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  have hD'D : P'.toBlocks₂₂ * P.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h2 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  set D := P.toBlocks₂₂ with hDdef
  set D' := P'.toBlocks₂₂
  let L : (Fin k → O) ≃ₗ[O] (Fin k' → O) :=
    LinearEquiv.ofLinear (Matrix.toLin' Dᵀ) (Matrix.toLin' D'ᵀ)
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hD'D, Matrix.transpose_one, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hDD, Matrix.transpose_one, Matrix.toLin'_one])
  refine ⟨Module.Basis.ofEquivFun (lbs.equivFun.trans L.symm), fun j => ?_⟩
  rw [Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  congr 1
  simp [L, Matrix.mulVec, dotProduct, Pi.single_apply, hDdef, Matrix.toBlocks₂₂]

end GlobalTheory
