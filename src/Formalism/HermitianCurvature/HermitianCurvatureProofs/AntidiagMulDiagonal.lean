import Formalism.HermitianCurvature.StatementK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecText

namespace Formalism.FourierDecayAlt.P.K

open Matrix Finset Real Formalism.FourierDecayAlt.K

variable {K : Type} [Field K] {n : ℕ}

theorem diag_mul {a b : Matrix (Fin n) (Fin n) K} (ha : a.BlockTriangular id)
    (hb : b.BlockTriangular id) (i : Fin n) : (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [ha h, zero_mul]
    · rw [hb h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem upUni_mul {a b : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) (hb : IsUpUni b) :
    IsUpUni (a * b) := ⟨Matrix.BlockTriangular.mul ha.1 hb.1, fun i => by rw [diag_mul ha.1 hb.1, ha.2, hb.2, one_mul]⟩

theorem upUni_det {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : a.det = 1 := by
  rw [Matrix.det_of_upperTriangular ha.1]
  simp [ha.2]

theorem upUni_isUnit {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : IsUnit a.det := by
  rw [upUni_det ha]
  exact isUnit_one

theorem upUni_inv {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : IsUpUni a⁻¹ := by
  haveI := Matrix.invertibleOfIsUnitDet a (upUni_isUnit ha)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular ha.1
  refine ⟨hinv, fun i => ?_⟩
  have h := diag_mul hinv ha.1 i
  rw [Matrix.nonsing_inv_mul _ (upUni_isUnit ha), ha.2, mul_one, Matrix.one_apply_eq] at h
  exact h.symm

theorem antidiag_mul_diagonal (d : Fin n → K) :
    w0 n * diagonal d = Matrix.of fun i j => if i = Fin.rev j then d j else 0 := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [w0, Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  have hiff : ((i : ℕ) + (j : ℕ) + 1 = n) ↔ i = Fin.rev j := by
    rw [Fin.ext_iff, Fin.val_rev]
    omega
  by_cases h : i = Fin.rev j
  · rw [if_pos (hiff.mpr h), if_pos h, one_mul]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, zero_mul]

theorem mulW_apply (a : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (i j : Fin n) :
    (a * (w0 n * diagonal d) : Matrix (Fin n) (Fin n) K) i j = a i (Fin.rev j) * d j := by
  rw [antidiag_mul_diagonal, Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ _) h





theorem jointTheoremA : JointTheoremA := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.coarseBound
  refine ⟨2 * C₀, C, ?_⟩
  intro Kx Θ f r e σ hKx hf hΘ hr he hσ hrec
  have hΘ1 : 1 ≤ Θ := by linarith
  have hΘpos : 0 < Θ := by linarith
  have ha0 : 0 ≤ C₀ / Θ := div_nonneg (by linarith) hΘpos.le
  have hq : C₀ / Θ ≤ 1 / 2 := by
    rw [div_le_iff₀ hΘpos]
    linarith
  have ha : (C₀ / Θ) ^ f ≤ 1 / 2 := by
    calc (C₀ / Θ) ^ f ≤ (C₀ / Θ) ^ 1 := pow_le_pow_of_le_one ha0 (by linarith) hf
      _ ≤ 1 / 2 := by rw [pow_one]; exact hq
  have hrp : Θ ^ (-(Kx - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ1 (by linarith)
  have hε0 : 0 ≤ C₀ * Θ ^ (-(Kx - 5 / 2)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hΘpos.le _)
  have hεa : (C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f ≤ (C₀ / Θ) ^ f := by
    apply pow_le_pow_left₀ hε0
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrp (by linarith)
  exact hC r ((C₀ / Θ) ^ f) ((C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f) e σ (pow_nonneg ha0 _) ha
    (pow_nonneg hε0 _) hεa hr he hσ hrec

end Formalism.FourierDecayAlt.P.K


theorem Formalism.FourierDecayAlt.P.joint_theorem_A' : Formalism.FourierDecayAlt.K.JointTheoremA := Formalism.FourierDecayAlt.P.K.jointTheoremA
