module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcIndep_det_ne_zero_of_rank {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (h : B.rank = n) :
    B.det ≠ 0 := by
  have hs : Function.Surjective B.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa [← Matrix.finrank_range_mulVecLin] using h
  have hu : IsUnit B := Matrix.mulVec_surjective_iff_isUnit.mp hs
  exact ((Matrix.isUnit_iff_isUnit_det B).mp hu).ne_zero

theorem fcIndep : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (Φ : Matrix (Fin q ⊕ Fin p) (Fin q) ℂ), A * Φ = 0 → A.rank = p → Φ.rank = q → (Φᴴ * Φ).det ≠ 0 ∧ (fromRows Φᴴ A).det ≠ 0 ∧ ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ, (fromRows N A).det * (Φᴴ * Φ).det = (fromRows Φᴴ A).det * (N * Φ).det := by
  intro p q A Φ h0 hA hΦ
  have h1 : (Φᴴ * Φ).det ≠ 0 := by
    apply fcIndep_det_ne_zero_of_rank
    open ComplexOrder in rw [Matrix.rank_conjTranspose_mul_self, hΦ]
  have h2 : (A * Aᴴ).det ≠ 0 := by
    apply fcIndep_det_ne_zero_of_rank
    open ComplexOrder in rw [Matrix.rank_self_mul_conjTranspose, hA]
  have key : ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ,
      (fromRows N A).det * (fromCols Φ Aᴴ).det = (N * Φ).det * (A * Aᴴ).det := by
    intro N
    rw [← Matrix.det_mul, Matrix.fromRows_mul_fromCols, h0, Matrix.det_fromBlocks_zero₂₁]
  have h3 : (fromRows Φᴴ A).det * (fromCols Φ Aᴴ).det ≠ 0 := by
    rw [key]; exact mul_ne_zero h1 h2
  refine ⟨h1, left_ne_zero_of_mul h3, fun N => ?_⟩
  apply mul_right_cancel₀ (right_ne_zero_of_mul h3)
  have a := key N
  have b := key Φᴴ
  linear_combination (Φᴴ * Φ).det * a - (N * Φ).det * b

end GlobalTheory.CompanionTheory.Ar.Flat
