module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset MvPolynomial UpperTheory.Gal.Schur

namespace UpperTheory.Gal.Schur

private lemma vdm_X_ne (n : ℕ) : vdm (X : Fin n → MvPolynomial (Fin n) ℚ) ≠ 0 := by
  unfold vdm
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  exact sub_ne_zero.2 (MvPolynomial.X_injective.ne (Finset.mem_Ioi.1 hj).ne)

private lemma aeval_sch {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (lam : Fin n → ℕ)
    (g : Fin n → R) :
    aeval g (sch lam (X : Fin n → MvPolynomial (Fin n) ℚ)) = sch lam g := by
  unfold sch
  rw [MvPolynomial.aeval_X_left_apply]

private lemma altn_zero {R : Type} [CommRing R] {n : ℕ} (g : Fin n → R) :
    altn (shift fun _ => 0) g = vdm g := by
  have h := GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_staircase_eq_vandermondeOf g
  have h' : vdm g = GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf g := rfl
  unfold altn
  rw [h']
  simpa [shift] using h

private lemma altn_add {R : Type} [CommRing R] {n : ℕ} (lam : Fin n → ℕ) (m : ℕ) (g : Fin n → R) :
    altn (shift fun i => lam i + m) g = (∏ k, g k) ^ m * altn (shift lam) g := by
  unfold altn
  have h : (Matrix.of fun i j : Fin n => g j ^ (shift (fun i => lam i + m)) i) =
      Matrix.of fun i j : Fin n =>
        g j ^ m * (Matrix.of fun i j : Fin n => g j ^ (shift lam) i) i j := by
    ext i j
    simp only [Matrix.of_apply, shift]
    rw [← pow_add]
    congr 1
    omega
  rw [h, Matrix.det_mul_row, Finset.prod_pow]

private lemma sch_zero_X (tie : Comparison₂) (n : ℕ) :
    sch (fun _ => 0) (X : Fin n → MvPolynomial (Fin n) ℚ) = 1 := by
  have h := tie (MvPolynomial (Fin n) ℚ) n (fun _ => 0) X
  rw [altn_zero] at h
  exact mul_right_cancel₀ (vdm_X_ne n) (h.trans (one_mul _).symm)

private lemma sch_add_X (tie : Comparison₂) (n : ℕ) (lam : Fin n → ℕ) (m : ℕ) :
    sch (fun i => lam i + m) (X : Fin n → MvPolynomial (Fin n) ℚ) =
      (∏ k, (X k : MvPolynomial (Fin n) ℚ)) ^ m * sch lam X := by
  have h := tie (MvPolynomial (Fin n) ℚ) n (fun i => lam i + m) X
  rw [altn_add, ← tie (MvPolynomial (Fin n) ℚ) n lam X, ← mul_assoc] at h
  exact mul_right_cancel₀ (vdm_X_ne n) h

theorem schurDet_of :
    Comparison₂ → SchurDet := by
  intro tie R _ _ n g
  refine ⟨?_, fun lam m => ?_⟩
  · rw [← aeval_sch, sch_zero_X tie, map_one]
  · rw [← aeval_sch, sch_add_X tie, map_mul, map_pow, map_prod, aeval_sch]
    simp only [aeval_X]

end UpperTheory.Gal.Schur
