module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

open Matrix Polynomial

namespace GlobalTheory

theorem norm_multiset_prod_near_one (s : Multiset ℂ) (hs : ∀ μ ∈ s, ‖μ - 1‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ Multiset.card s ≤ ‖s.prod‖ ∧ ‖s.prod‖ ≤ (3 / 2 : ℝ) ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    obtain ⟨h1, h2⟩ := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
    have hlo : (1 / 2 : ℝ) ≤ ‖a‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - a)
      rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
      linarith
    have hhi : ‖a‖ ≤ 3 / 2 := by
      have := norm_add_le (a - 1) 1
      rw [sub_add_cancel, norm_one] at this
      linarith
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ, pow_succ]
    constructor
    · rw [mul_comm ((1 / 2 : ℝ) ^ _)]
      exact mul_le_mul hlo h1 (by positivity) (norm_nonneg _)
    · rw [mul_comm ((3 / 2 : ℝ) ^ _)]
      exact mul_le_mul hhi h2 (norm_nonneg _) (by norm_num)

theorem det_near_one_bounds (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ε) (hn : (n : ℝ) * ε ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ n ≤ ‖A.det‖ ∧ ‖A.det‖ ≤ 2 ^ n := by
  have hroot : ∀ μ ∈ A.charpoly.roots, ‖μ - 1‖ ≤ 1 / 2 := by
    intro μ hμ
    have hr : A.charpoly.IsRoot μ := isRoot_of_mem_roots hμ
    have hev : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']; exact hr
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
    rw [Metric.mem_closedBall, dist_eq_norm] at hk
    have hdiag : ‖A k k - 1‖ ≤ ε := by simpa using hA k k
    have h1n : 1 ≤ n := Fin.pos k
    have hoff : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ((n : ℝ) - 1) * ε := by
      have hle : ∀ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ε := by
        intro j hj
        have hjk : k ≠ j := (Finset.ne_of_mem_erase hj).symm
        simpa [Matrix.one_apply_ne hjk] using hA k j
      calc _ ≤ ∑ _j ∈ Finset.univ.erase k, ε := Finset.sum_le_sum hle
        _ = ((n : ℝ) - 1) * ε := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub h1n, Nat.cast_one]
    calc ‖μ - 1‖ = ‖(μ - A k k) + (A k k - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖μ - A k k‖ + ‖A k k - 1‖ := norm_add_le _ _
      _ ≤ ((n : ℝ) - 1) * ε + ε := add_le_add (hk.trans hoff) hdiag
      _ = n * ε := by ring
      _ ≤ 1 / 2 := hn
  have hcard : Multiset.card A.charpoly.roots = n := by
    rw [(splits_iff_card_roots).mp (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  obtain ⟨h1, h2⟩ := norm_multiset_prod_near_one _ hroot
  rw [hcard, ← Matrix.det_eq_prod_roots_charpoly] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

end GlobalTheory
