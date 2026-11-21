import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL

noncomputable section

namespace GlobalTheory.Published.DSExistsModel

def detPow (n : ℕ) (m : ℤ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ →L[ℂ] ℂ :=
  (g.det ^ m) • ContinuousLinearMap.id ℂ ℂ

theorem detPow_apply (n : ℕ) (m : ℤ) (g : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) :
    detPow n m g v = g.det ^ m * v := by simp [detPow]

theorem norm_det {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ‖g.det‖ = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h1 := congrArg Matrix.det h
  have h2 : (Formalism.REAL.Jm ε).det * (Formalism.REAL.Jm ε).det = 1 := by
    rw [← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
  have h3 : (Formalism.REAL.Jm ε).det ≠ 0 := left_ne_zero_of_mul_eq_one h2
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have h4 : star g.det * g.det = 1 := by
    apply mul_left_cancel₀ h3
    linear_combination h1
  have h5 := congrArg norm h4
  rw [norm_mul, norm_star, norm_one] at h5
  nlinarith [norm_nonneg g.det]

def lamDet (n : ℕ) (m : ℤ) : Fin n → ℝ := fun a => (m : ℝ) + Formalism.QuantumDeterminants.rhoStd n a

theorem lamDet_hc (n : ℕ) (m : ℤ) : Formalism.QuantumDeterminants.IsHCParam (lamDet n m) := by
  refine ⟨fun a b h => ?_, fun a => ⟨m - (a : ℕ), ?_⟩⟩
  · have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast h
    simp only [lamDet, Formalism.QuantumDeterminants.rhoStd]; linarith
  · simp only [lamDet, Formalism.QuantumDeterminants.rhoStd]; push_cast; ring

theorem lowK_lamDet (n : ℕ) (s : Bool) (m : ℤ) :
    Formalism.QuantumDeterminants.lowK (fun _ : Fin n => s) (lamDet n m) = fun _ => (m : ℝ) := by
  funext a
  rw [GlobalTheory.DefiniteCheck.lowK_const]
  simp only [lamDet, Formalism.QuantumDeterminants.rhoStd]; ring

theorem detPow_diag (n : ℕ) (m : ℤ) (θ : Fin n → ℝ) (v : ℂ) :
    detPow n m (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) v =
      Complex.exp (((∑ a, (m : ℝ) * θ a : ℝ) : ℂ) * Complex.I) • v := by
  rw [detPow_apply, Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul, smul_eq_mul]
  congr 2
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem isDS_detPow (n : ℕ) (s : Bool) (m : ℤ) : IsDS (fun _ : Fin n => s) (lamDet n m) (detPow n m) := by
  rw [GlobalTheory.RealPar.isDS_const_iff]
  refine ⟨inferInstance, inferInstance, ⟨⟨?_, fun a _ b _ => ?_⟩, fun g hg v => ?_, fun v => ?_⟩,
    inferInstance, fun _ _ _ _ => trivial, fun S _ _ => eq_bot_or_eq_top S, ?_, ?_⟩
  · ext; simp [detPow_apply]
  · ext; simp [detPow_apply, mul_zpow]
  · rw [detPow_apply, norm_mul, norm_zpow, norm_det hg]; simp
  · simp only [detPow_apply]
    refine ContinuousOn.mul (ContinuousOn.zpow₀ (continuous_id.matrix_det.continuousOn) m fun g hg => Or.inl ?_)
      continuousOn_const
    intro h0
    have := norm_det hg
    simp only [id] at h0
    rw [h0] at this
    simp at this
  · refine ⟨1, trivial, one_ne_zero, fun θ _ => ?_⟩
    unfold allPos
    rw [lowK_lamDet]
    exact detPow_diag n m θ 1
  · intro μ v _ hv hw
    refine ⟨0, fun a b h => absurd rfl h, ?_⟩
    unfold allPos at *
    rw [lowK_lamDet]
    have hK : ∀ θ : Fin n → ℝ, Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈
        Formalism.REAL.Kset (fun _ : Fin n => true) := by
      intro θ
      refine ⟨?_, by simp [GlobalTheory.DefiniteCheck.jm_const]⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.norm_exp_ofReal_mul_I]
      simp
    funext a
    simp only [Pi.zero_apply, Nat.cast_zero, zero_smul, Finset.sum_const_zero, Pi.sub_apply]
    by_contra hne
    have h := hw (Pi.single a (Real.pi / ((m : ℝ) - μ a))) (hK _)
    rw [detPow_diag] at h
    have h2 := smul_left_injective ℂ hv h
    simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    have h3 : Complex.exp (Real.pi * Complex.I) = 1 := by
      have e : (Real.pi : ℂ) * Complex.I = (((m : ℝ) * (Real.pi / ((m : ℝ) - μ a)) : ℝ) : ℂ) * Complex.I -
          ((μ a * (Real.pi / ((m : ℝ) - μ a)) : ℝ) : ℂ) * Complex.I := by
        rw [← sub_mul, ← Complex.ofReal_sub, ← sub_mul, mul_div_cancel₀ _ hne]
      rw [e, Complex.exp_sub, h2, div_self (Complex.exp_ne_zero _)]
    rw [Complex.exp_pi_mul_I] at h3
    norm_num at h3



theorem card_split {N : ℕ} (ε : Fin N → Bool) (a : Fin N) :
    (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) + ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) +
    ((univ.filter fun b => a < b ∧ ε b ≠ ε a).card : ℝ) + ((univ.filter fun b => b < a ∧ ε b ≠ ε a).card : ℝ)) =
      (N : ℝ) - 1 := by
  have h : ∑ b : Fin N, ((if a < b ∧ ε b = ε a then (1 : ℝ) else 0) + (if b < a ∧ ε b = ε a then (1 : ℝ) else 0) +
      (if a < b ∧ ε b ≠ ε a then (1 : ℝ) else 0) + (if b < a ∧ ε b ≠ ε a then (1 : ℝ) else 0)) =
      ∑ b : Fin N, ((1 : ℝ) - if b = a then 1 else 0) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy a b with h | h | h
    · by_cases e : ε b = ε a <;> simp [h, h.ne', not_lt_of_gt h, e]
    · subst h; simp
    · by_cases e : ε b = ε a <;> simp [h, h.ne, not_lt_of_gt h, e]
  simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib] using h





theorem diag_mem {N : ℕ} (ε : Fin N → Bool) (θ : Fin N → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  refine ⟨?_, by simp [Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  simp



end GlobalTheory.Published.DSExistsModel
