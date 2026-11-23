module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.SatakeDualWeyl.Statement

@[expose] public section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

theorem adjoin_range_GL_eq_top (R : Type) [CommRing R] (n : ℕ) :
    Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ) = ⊤ := by
  set S := Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ)
  have hoff : ∀ i j : Fin n, i ≠ j → Matrix.single i j (1:R) ∈ S := by
    intro i j hij
    have hu : IsUnit (Matrix.transvection i j (1:R)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transvection_of_ne _ _ hij]; exact isUnit_one)
    have hmem : Matrix.transvection i j (1:R) ∈ S :=
      Algebra.subset_adjoin ⟨hu.unit, Set.mem_univ _, rfl⟩
    have : Matrix.single i j (1:R) = Matrix.transvection i j 1 - 1 := by
      simp [Matrix.transvection]
    rw [this]; exact S.sub_mem hmem S.one_mem
  have hall : ∀ i j : Fin n, Matrix.single i j (1:R) ∈ S := by
    intro i j
    by_cases hij : i = j
    · subst hij
      by_cases h : ∃ k, k ≠ i
      · obtain ⟨k, hk⟩ := h
        have : Matrix.single i i (1:R) = Matrix.single i k 1 * Matrix.single k i 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        rw [this]; exact S.mul_mem (hoff _ _ (Ne.symm hk)) (hoff _ _ hk)
      · push_neg at h
        have : Matrix.single i i (1:R) = 1 := by
          ext a b
          rw [h a, h b]; simp
        rw [this]; exact S.one_mem
    · exact hoff i j hij
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  have : Matrix.single i j (M i j) = M i j • Matrix.single i j 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]; exact S.smul_mem (hall i j) _

end GlobalTheory
