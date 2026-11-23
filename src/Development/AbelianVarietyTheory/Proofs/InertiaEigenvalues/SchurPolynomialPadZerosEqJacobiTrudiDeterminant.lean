module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.JSW

theorem jacobi_trudi_det_pad_zeros {A : Type*} [CommRing A] (h : ℕ → A) (h0 : h 0 = 1) {m n : ℕ} (hmn : m ≤ n)
    (l : Fin m → ℕ) : jtDet n h (padTo hmn l) = jtDet m h l := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  unfold jtDet
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  set M := (Matrix.of fun i j : Fin (m + k) =>
    if ((padTo hmn l i : ℤ) - i + j) < 0 then 0 else h (((padTo hmn l i : ℤ) - i + j).toNat)).submatrix
      finSumFinEquiv finSumFinEquiv with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hM, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply, padTo]
    have hj := j.2
    simp
    omega
  have h22 : M.toBlocks₂₂.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_eq_one
      intro i _
      simp [hM, Matrix.toBlocks₂₂, padTo, h0]
    · intro i j hij
      simp only [hM, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_right, padTo]
      have : (j : ℕ) < i := hij
      simp
      omega
  have h11 : M.toBlocks₁₁ = Matrix.of fun i j : Fin m =>
      if ((l i : ℤ) - i + j) < 0 then 0 else h (((l i : ℤ) - i + j).toNat) := by
    ext i j
    simp [hM, Matrix.toBlocks₁₁, padTo]
  rw [← Matrix.fromBlocks_toBlocks M, h21, Matrix.det_fromBlocks_zero₂₁, h22, h11, mul_one]

theorem schur_padTo_eq_jtDet {m n : ℕ} (hmn : m ≤ n) (l : Fin m → ℕ) :
    schur n (padTo hmn l) = jtDet m (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := by
  rw [schur_eq_jtDet]
  exact jacobi_trudi_det_pad_zeros _ (MvPolynomial.hsymm_zero _ _) hmn l

end GlobalTheory.JSW
