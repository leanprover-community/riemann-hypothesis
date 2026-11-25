module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.DefiniteUnitaryCasimir

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.UnitaryLieComplexification

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

theorem mul_single_mul (U V : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    U * single a b (1 : ℂ) * V = ∑ c, ∑ d, (U c a * V b d) • single c d (1 : ℂ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single (U * single a b (1 : ℂ) * V)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem casimir_move {A : Type} [Ring A] [Algebra ℂ A] (R R' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A)
    (U V : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, R (U * single a b 1 * V) * R' (single b a 1) =
      ∑ c, ∑ d, R (single c d 1) * R' (V * single d c 1 * U) := by

  simp only [mul_single_mul, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type' (f := fun c d => ∑ b, ∑ a, (V b d * U c a) • (R (single c d 1) * R' (single b a 1)))]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _))) _ _
    fun q => ?_
  simp [mul_comm]

theorem casimir_conj {A : Type} [Ring A] [Algebra ℂ A] (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) :
    ∑ a, ∑ b, R (single a b 1) * R (single b a 1) =
      ∑ a, ∑ b, R (B⁻¹ * single a b 1 * B) * R (B⁻¹ * single b a 1 * B) := by
  have := casimir_move R (R ∘ₗ (LinearMap.mulRight ℂ B) ∘ₗ (LinearMap.mulLeft ℂ B⁻¹)) B⁻¹ B
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at this
  rw [this]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul B hB, Matrix.mul_one]

end GlobalTheory.DefiniteUnitaryCasimir
