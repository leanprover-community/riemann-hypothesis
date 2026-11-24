module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

private theorem isUnit_det_and_eq_inv_of_conjTranspose_mul_eq_one {n : ℕ} (A B D : Matrix (Fin n) (Fin n) ℂ) (h1 : Aᴴ * D = 1)
    (h3 : Bᴴ * D = Dᴴ * B) : IsUnit A.det ∧ D = (Aᴴ)⁻¹ ∧ (B * Aᴴ)ᴴ = B * Aᴴ := by
  have hDA : D * Aᴴ = 1 := mul_eq_one_comm.mp h1
  have hAD : A * Dᴴ = 1 := by simpa using congrArg conjTranspose hDA
  refine ⟨?_, (inv_eq_right_inv h1).symm, ?_⟩
  · have h := congrArg det h1
    rw [det_mul, det_one, det_conjTranspose] at h
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, star_zero, zero_mul] at h
    exact zero_ne_one h
  · rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc A * Bᴴ = A * (Bᴴ * D) * Aᴴ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hDA, Matrix.mul_one]
      _ = A * (Dᴴ * B) * Aᴴ := by rw [h3]
      _ = B * Aᴴ := by rw [← Matrix.mul_assoc A Dᴴ B, hAD, Matrix.one_mul]

theorem siegelP_data (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) :
    IsUnit (mR q).toBlocks₁₁.det ∧ (mR q).toBlocks₂₂ = ((mR q).toBlocks₁₁ᴴ)⁻¹ ∧
      ((mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ)ᴴ = (mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ := by
  have hG : InG (mR q) := q.2
  rw [InG, ← fromBlocks_toBlocks (mR q), hq, JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at hG
  simp at hG
  exact isUnit_det_and_eq_inv_of_conjTranspose_mul_eq_one _ _ _ hG.1 (neg_add_eq_zero.mp hG.2.2).symm

theorem siegelP_actZ (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (Z : Matrix (Fin n) (Fin n) ℂ) :
    actZ q Z = (mR q).toBlocks₁₁ * Z * (mR q).toBlocks₁₁ᴴ + (mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ := by
  obtain ⟨hu, hD, -⟩ := siegelP_data q hq
  have hu' : IsUnit ((mR q).toBlocks₁₁ᴴ).det := by
    rw [det_conjTranspose]
    exact hu.star
  rw [actZ, hq, Matrix.zero_mul, zero_add, hD, Matrix.nonsing_inv_nonsing_inv _ hu', Matrix.add_mul]

theorem siegelP_jF (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (e : ℤ) (p p' : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    jF e p p' q Z = (mR q).toBlocks₁₁.det ^ e * (star (mR q).toBlocks₁₁.det) ^ (((p + p' : ℕ) : ℤ) - e) := by
  obtain ⟨hu, hD, -⟩ := siegelP_data q hq
  have hdet : det (mR q) = (mR q).toBlocks₁₁.det * (mR q).toBlocks₂₂.det := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR q), hq]
    exact det_fromBlocks_zero₂₁ _ _ _
  have hs : star (mR q).toBlocks₁₁.det ≠ 0 := hu.star.ne_zero
  rw [jF, hq, Matrix.zero_mul, Matrix.zero_mul, zero_add, hdet, hD, det_nonsing_inv,
    det_conjTranspose, Ring.inverse_eq_inv']
  generalize (mR q).toBlocks₁₁.det = a at hs ⊢
  generalize star a = s at hs ⊢
  rw [mul_zpow, _root_.inv_zpow', _root_.inv_zpow', _root_.inv_zpow', neg_neg, neg_neg, mul_assoc,
    mul_assoc, ← zpow_add₀ hs, ← zpow_add₀ hs]
  congr 2
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH
