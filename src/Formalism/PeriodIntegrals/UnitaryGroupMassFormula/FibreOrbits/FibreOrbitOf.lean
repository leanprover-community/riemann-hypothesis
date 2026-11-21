import Mathlib
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.FibOrbAsmW

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

def sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ i.val ∧ i.val ≤ r + k ∧ i.val = r + k then -1 else 1

lemma Hpk_apply (k r : ℕ) (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l = sig k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hl := l.isLt
  simp only [Hpk, sig, sgn, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | (simp_all; omega)

lemma sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sig k r (sig k r i) = i := by
  have hi := i.isLt
  unfold sig
  split_ifs <;> first | rfl | (ext; simp only at *; omega)

lemma sgn_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by
  have hi := i.isLt
  unfold sgn sig
  split_ifs <;> first | rfl | (simp only at *; omega)

lemma sgn_mul_self (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma Hpk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [mul_apply, Finset.sum_eq_single (sig k r i)]
  · rw [Hpk_apply, Hpk_apply, if_pos rfl, sig_sig, sgn_sig, one_apply]
    by_cases h : j = i
    · subst h; rw [if_pos rfl, if_pos rfl, sgn_mul_self]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  · intro l _ hl
    rw [Hpk_apply, if_neg hl, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma det_Hpk (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h := congrArg Matrix.det (Hpk_mul_self k r)
  rw [det_mul, det_one] at h
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

section Group

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma UH_mul {H a b : Matrix ι ι ℂ} (ha : a ∈ UH H) (hb : b ∈ UH H) : a * b ∈ UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

lemma UH_det {H g : Matrix ι ι ℂ} (hH : IsUnit H.det) (hg : g ∈ UH H) : IsUnit g.det := by
  have hg' : gᴴ * H * g = H := hg
  have := congrArg Matrix.det hg'
  rw [det_mul, det_mul, det_conjTranspose] at this
  rw [isUnit_iff_ne_zero] at hH ⊢
  intro h0
  rw [h0, mul_zero] at this
  exact hH this.symm

lemma UH_inv {H g : Matrix ι ι ℂ} (hH : IsUnit H.det) (hg : g ∈ UH H) : g⁻¹ ∈ UH H := by
  have hd := UH_det hH hg
  have hg' : gᴴ * H * g = H := hg
  have hd' : IsUnit gᴴ.det := by
    rw [det_conjTranspose, isUnit_iff_ne_zero, star_ne_zero, ← isUnit_iff_ne_zero]; exact hd
  show g⁻¹ᴴ * H * g⁻¹ = H
  rw [conjTranspose_nonsing_inv]
  calc gᴴ⁻¹ * H * g⁻¹ = gᴴ⁻¹ * (gᴴ * H * g) * g⁻¹ := by rw [hg']
    _ = (gᴴ⁻¹ * gᴴ) * H * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [nonsing_inv_mul _ hd', mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]

end Group



end PI.UnitaryGroupMassFormula.FibOrbAsmW
