import Mathlib
import Formalism.PeriodIntegrals.LatCountG

open Matrix
open scoped ENNReal

noncomputable section

namespace PI.MultFromLatWork

open Formalism.REAL

lemma kset_unitary {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ * k = 1 ∧ k * kᴴ = 1 := by
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  exact ⟨by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hk'.1,
    by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hk'.1⟩

lemma kset_conjTranspose {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  obtain ⟨h1, h2⟩ := kset_unitary hk
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  show kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ kᴴ * Jm ε = Jm ε * kᴴ
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact h1
  · calc kᴴ * Jm ε = kᴴ * Jm ε * (k * kᴴ) := by rw [h2, Matrix.mul_one]
      _ = kᴴ * (Jm ε * k) * kᴴ := by simp only [Matrix.mul_assoc]
      _ = kᴴ * (k * Jm ε) * kᴴ := by rw [hk'.2]
      _ = (kᴴ * k) * Jm ε * kᴴ := by simp only [Matrix.mul_assoc]
      _ = Jm ε * kᴴ := by rw [h1, Matrix.one_mul]

lemma hs_eq_trace {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

lemma inP_conj {n : ℕ} {ε : Fin n → Bool} {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hX : inP ε X) : inP ε (k * X * kᴴ) := by
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  have hkh : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ kᴴ * Jm ε = Jm ε * kᴴ := kset_conjTranspose hk
  have hJkh := hkh.2
  have hJk := hk'.2
  have hG : Xᴴ * Jm ε + Jm ε * X = 0 := hX.1
  have hX2 : X * Jm ε = -(Jm ε * X) := hX.2
  have e1 : (k * X * kᴴ)ᴴ * Jm ε = k * (Xᴴ * Jm ε) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hJkh]
  have e2 : Jm ε * (k * X * kᴴ) = k * (Jm ε * X) * kᴴ := by
    calc Jm ε * (k * X * kᴴ) = (Jm ε * k) * X * kᴴ := by simp only [Matrix.mul_assoc]
      _ = (k * Jm ε) * X * kᴴ := by rw [← hJk]
      _ = k * (Jm ε * X) * kᴴ := by simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · show (k * X * kᴴ)ᴴ * Jm ε + Jm ε * (k * X * kᴴ) = 0
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hG, Matrix.mul_zero, Matrix.zero_mul]
  · calc k * X * kᴴ * Jm ε = k * (X * Jm ε) * kᴴ := by simp only [Matrix.mul_assoc, hJkh]
      _ = k * (-(Jm ε * X)) * kᴴ := by rw [hX2]
      _ = -(k * (Jm ε * X) * kᴴ) := by rw [Matrix.mul_neg, Matrix.neg_mul]
      _ = -(Jm ε * (k * X * kᴴ)) := by rw [e2]

lemma hs_conj {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ} (hk1 : kᴴ * k = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    hs (k * X * kᴴ) = hs X := by
  rw [hs_eq_trace, hs_eq_trace]
  congr 1
  have e : (k * X * kᴴ)ᴴ * (k * X * kᴴ) = k * (Xᴴ * X) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᴴ k, hk1, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hk1, Matrix.one_mul]




lemma const_eq (I : Formalism.MainNotions.S.AutInst) (r : NumberField.InfinitePlace I.F → ℝ) (t : ℝ) :
    (3 * Real.sqrt (I.n : ℝ) / (t * t)) ^ (2 * I.n ^ 2 * I.f) *
        Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, (2 * r v)) =
      PI.LatCountG.COm I r / t ^ (4 * I.n ^ 2 * I.f) := by
  have he : ∑ v, (2 * r v) = 2 * ∑ v, r v := by rw [Finset.mul_sum]
  have hp : t ^ (4 * I.n ^ 2 * I.f) = (t * t) ^ (2 * I.n ^ 2 * I.f) := by ring
  have hx : 2 * (I.n : ℝ) ^ 2 * (2 * ∑ v, r v) = 4 * (I.n : ℝ) ^ 2 * ∑ v, r v := by ring
  rw [PI.LatCountG.COm, hp, he, hx, div_pow]
  ring



end PI.MultFromLatWork

end
