import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeGtDvdEval
import BuildAid.ForwardExisting

section
open scoped TensorProduct Polynomial

namespace GlobalTheory

open Polynomial in

theorem exists_prime_gt_dvd_eval :
    ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
  first
  | exact @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | (apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval ..)

end GlobalTheory
end

open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval : ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
  atlas_forward_decl GlobalTheory.exists_prime_gt_dvd_eval
