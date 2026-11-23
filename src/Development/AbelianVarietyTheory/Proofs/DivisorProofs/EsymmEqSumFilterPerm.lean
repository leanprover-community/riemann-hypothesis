module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
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

@[expose] public section

open scoped Classical

namespace GlobalTheory.JSW

theorem esymm_eq_sum_filter_perm (n j : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.esymm (Fin n) ℤ j =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
        ∏ k ∈ J, (MvPolynomial.X (σ k) : MvPolynomial (Fin n) ℤ) := by
  rw [← MvPolynomial.rename_esymm (Fin n) ℤ j σ]

  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.rename_X,
  Finset.powersetCard_eq_filter, Finset.powerset_univ]

theorem esymm_mul_alternant (n : ℕ) (m : Fin n → ℕ) (j : ℕ) :
    MvPolynomial.esymm (Fin n) ℤ j *
        Matrix.det (Matrix.of fun i k : Fin n =>
          (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m k) =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
        Matrix.det (Matrix.of fun i k : Fin n =>
          (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (m k + if k ∈ J then 1 else 0)) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [esymm_eq_sum_filter_perm n j σ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [mul_smul_comm]
  congr 1
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_mem, Finset.univ_inter]
  ring

end GlobalTheory.JSW
