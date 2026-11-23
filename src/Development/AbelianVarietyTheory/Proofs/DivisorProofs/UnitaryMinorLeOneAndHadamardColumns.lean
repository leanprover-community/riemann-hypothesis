module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
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

@[expose] public section

open scoped Matrix

namespace GlobalTheory.UnitaryMinor

theorem sum_norm_sq_col {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i, ‖u.1 i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 u.2) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ i, ‖u.1 i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  exact_mod_cast h2

theorem norm_det_submatrix_le_one (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (I J : Fin s → Fin n) : ‖(u.1.submatrix I J).det‖ ≤ 1 := by
  by_cases hI : Function.Injective I
  · have h : ‖(u.1.submatrix I J).det‖ ^ 2 ≤ 1 := by
      refine (GlobalTheory.Hadamard.norm_det_sq_le_prod_col (u.1.submatrix I J)).trans ?_
      refine Finset.prod_le_one₀ (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
        fun j _ => ?_
      rw [← sum_norm_sq_col u (J j)]
      simp only [Matrix.submatrix_apply]
      rw [← Finset.sum_image (s := Finset.univ) (g := I) (f := fun i => ‖u.1 i (J j)‖ ^ 2)
        (fun a _ b _ h => hI h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => by positivity
    exact (sq_le_one_iff₀ (norm_nonneg _)).1 h
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hI
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hab])]
    simp

theorem unitary_minor_and_hadamard :
    (∀ (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : Fin s → Fin n),
      ‖(u.1.submatrix I J).det‖ ≤ 1) ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ),
      ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 :=
  ⟨norm_det_submatrix_le_one, fun _ _ _ M => GlobalTheory.Hadamard.norm_det_sq_le_prod_col M⟩

end GlobalTheory.UnitaryMinor
