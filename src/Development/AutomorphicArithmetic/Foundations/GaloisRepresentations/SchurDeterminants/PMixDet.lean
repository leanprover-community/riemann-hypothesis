module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset MvPolynomial UpperTheory.Gal.Schur

private theorem prod_ite_eq_mul_prod_erase {R : Type} [CommRing R] {n : ℕ} (d d' : Fin n → R) (a : Fin n) :
    ∏ b, (if b = a then d b else d' b) = d a * ∏ b ∈ univ.erase a, d' b := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ a), if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [if_neg (Finset.ne_of_mem_erase hb)]

theorem UpperTheory.Gal.Schur.mixDet :
    MixDet := by
  intro R _ n M d d'
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Units.smul_def, zsmul_eq_mul]
  have key : ∀ i, (∏ j, if j = i then d (σ j) else d' (σ j)) =
      ∏ b, (if b = σ i then d b else d' b) := by
    intro i
    rw [← Equiv.prod_comp σ (fun b => if b = σ i then d b else d' b)]
    simp only [σ.injective.eq_iff]
  calc _ = (∑ i, ∏ b, (if b = σ i then d b else d' b)) *
        ((Equiv.Perm.sign σ : ℤ) * ∏ x, M (σ x) x) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [key]
        ring
    _ = _ := by
        congr 1
        rw [Equiv.sum_comp σ (fun a => ∏ b, if b = a then d b else d' b)]
        exact Finset.sum_congr rfl fun a _ => prod_ite_eq_mul_prod_erase d d' a
