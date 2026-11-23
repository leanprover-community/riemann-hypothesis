module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem hsymm_isHomogeneous (σ : Type*) [Fintype σ] [DecidableEq σ] (n : ℕ) :
    (hsymm σ ℚ n).IsHomogeneous n := by
  rw [Schur.hsymm_eq_sum_finsuppAntidiag]
  refine IsHomogeneous.sum _ _ _ fun l hl => ?_
  have hsum : ∑ i, l i = n := (mem_finsuppAntidiag.mp hl).1
  rw [← hsum]
  exact IsHomogeneous.prod _ _ _ fun i _ => by
    simpa using (isHomogeneous_X ℚ i).pow (l i)

theorem SchSchurHomogeneous.proof : SchSchurHomogeneous.Statement := by
  intro σ _ _ r lam
  unfold schur
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun π _ => ?_
  rw [Units.smul_def]
  have hmem : (∏ i, (Matrix.of fun i j : Fin r =>
      completeSymmetric σ ((lam i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ))) (π i) i) ∈
      homogeneousSubmodule σ ℚ (∑ i, lam i) := by
    rw [mem_homogeneousSubmodule]
    by_cases h : ∀ i, 0 ≤ (lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)
    · have hdeg : ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)).toNat = ∑ i, lam i := by
        have h1 : ((∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)).toNat : ℕ) : ℤ) =
            ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)) := by
          push_cast
          exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h i)
        have h2 : ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)) = ∑ i, (lam i : ℤ) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Equiv.sum_comp π (fun i => (lam i : ℤ)), Equiv.sum_comp π (fun i => ((i : ℕ) : ℤ))]
          ring
        exact_mod_cast h1.trans h2
      rw [← hdeg]
      refine IsHomogeneous.prod _ _ _ fun i _ => ?_
      simp only [Matrix.of_apply, completeSymmetric, if_pos (h i)]
      exact hsymm_isHomogeneous σ _
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [completeSymmetric, not_le.mpr hi])]
      exact isHomogeneous_zero _ _ _
  exact zsmul_mem hmem _

end GroundTheory.Heights₂.Heights.RestTerms
