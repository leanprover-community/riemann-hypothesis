import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Model

open Matrix
open scoped ComplexOrder



instance uniq1 : Unique {a : Fin 2 // (a : ℕ) < 1} where
  default := ⟨0, by simp⟩
  uniq := by rintro ⟨a, ha⟩; apply Subtype.ext; apply Fin.ext; simp only [Fin.val_zero]; omega

def eqv2 : {a : Fin 2 // (a : ℕ) < 2} ≃ Fin 2 := Equiv.subtypeUnivEquiv (fun a => a.2)

theorem det_head_one (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (gramHead hd 1 g).det = gramOf hd g 0 0 := by
  rw [det_unique]; rfl

theorem det_head_two (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (gramHead hd 2 g).det = (gramOf hd g).det := by
  rw [← det_submatrix_equiv_self eqv2 (gramOf hd g)]; rfl

theorem det_head_zero {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) :
    (gramHead hd 0 g).det = 1 := by
  haveI : IsEmpty {a : Fin N // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩
  exact det_isEmpty

theorem gram_signature_two_one_entry_zero_zero (z : ℂ) : gramOf (sigForm 2 1) !![1, 0; z, 1] 0 0 = -((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
  simp [gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']
  ring


theorem inFlagDomain_disc (z : ℂ) : InFlagDomain 2 1 !![1, 0; z, 1] ↔ ‖z‖ < 1 := by
  have h : -gramHead (sigForm 2 1) (2 - 1) !![1, 0; z, 1]
      = diagonal (fun _ : {a : Fin 2 // (a : ℕ) < 1} => ((1 - ‖z‖ ^ 2 : ℝ) : ℂ)) := by
    ext a b
    have ha : a = default := Subsingleton.elim (α := {a : Fin 2 // (a : ℕ) < 1}) _ _
    have hb : b = default := Subsingleton.elim (α := {a : Fin 2 // (a : ℕ) < 1}) _ _
    subst ha; rw [hb]
    rw [diagonal_apply_eq, Matrix.neg_apply]
    change -(gramOf (sigForm 2 1) !![1, 0; z, 1] 0 0) = _
    rw [gram_signature_two_one_entry_zero_zero, neg_neg]
  unfold InFlagDomain
  rw [h, posDef_diagonal_iff]
  have hu : IsUnit (!![1, 0; z, 1] : Matrix (Fin 2) (Fin 2) ℂ).det := by simp [det_fin_two_of]
  simp only [hu, true_and, Complex.zero_lt_real, forall_const]
  constructor
  · intro h; nlinarith [norm_nonneg z]
  · intro h; nlinarith [norm_nonneg z]



theorem stepPot_pos_zero (z : ℂ) :
    stepPot 2 2 0 !![1, 0; z, 1] = (1 / 2) * Real.log (1 + ‖z‖ ^ 2) := by
  have : stepPot 2 2 0 !![1, 0; z, 1]
      = gramLog (sigForm 2 2) 1 !![1, 0; z, 1] - gramLog (sigForm 2 2) 0 !![1, 0; z, 1] := by
    simp [stepPot]
  have h : gramOf (sigForm 2 2) !![1, 0; z, 1] 0 0 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
    simp [gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']
  rw [this, gramLog, gramLog, det_head_one, det_head_zero, h, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  simp







theorem gramLog_top (N j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    gramLog (sigForm N j) N g = Real.log ‖g.det‖ := by
  have h : (gramHead (sigForm N j) N g).det = (gramOf (sigForm N j) g).det := by
    rw [← det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun a : Fin N => (a : ℕ) < N) (fun a => a.2))
      (gramOf (sigForm N j) g)]; rfl
  have h2 : ‖∏ i : Fin N, ((sigForm N j i : ℝ) : ℂ)‖ = 1 := by
    rw [norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    unfold sigForm; split_ifs <;> simp
  rw [gramLog, h, gramOf, det_mul, det_mul, det_diagonal, det_conjTranspose, norm_mul, norm_mul, h2, norm_star,
    mul_one, ← sq, Real.log_pow]
  push_cast; ring

end GlobalTheory.CompanionTheory.Ar.PB.Model
