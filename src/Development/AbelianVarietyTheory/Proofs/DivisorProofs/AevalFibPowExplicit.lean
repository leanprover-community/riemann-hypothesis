import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HPolyAddTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivFractionsBilinearFormula

section
open MeasureTheory MvPolynomial GlobalTheory.FibLine

noncomputable section

namespace GlobalTheory.FibLine

theorem integral_comp_fsDens (g : ℝ → ℂ) (_hg : ContinuousOn g (Set.Icc 0 1)) :
    ∫ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * (fsDens x : ℂ) = ∫ t in (0 : ℝ)..1, g t := by
  set F : ℝ → ℂ := fun r => g (1 / (1 + r ^ 2)) * ((1 / (Real.pi * (1 + r ^ 2) ^ 2) : ℝ) : ℂ) with hF
  have h1 : ∫ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * (fsDens x : ℂ) = ∫ x : ℂ, F ‖x‖ := rfl
  rw [h1, integral_fun_norm_addHaar (volume : Measure ℂ) F]
  set f : ℝ → ℝ := fun r => (1 + r ^ 2)⁻¹ with hf
  set f' : ℝ → ℝ := fun r => -(2 * r) / (1 + r ^ 2) ^ 2 with hf'
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivWithinAt f (f' x) (Set.Ioi 0) x := by
    intro x _
    have h : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add 1)
    have hne : (1 + x ^ 2) ≠ 0 := by positivity
    exact (h.inv hne).hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    intro a ha b hb hab
    simp only [hf, inv_inj, add_right_inj] at hab
    have ha' : (0:ℝ) < a := ha
    have hb' : (0:ℝ) < b := hb
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have himg : f '' Set.Ioi 0 = Set.Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : (0:ℝ) < r := hr
      refine ⟨by positivity, ?_⟩
      exact inv_lt_one_of_one_lt₀ (by nlinarith)
    · rintro ⟨h0, h1⟩
      have ht : 1 < t⁻¹ := one_lt_inv_iff₀.2 ⟨h0, h1⟩
      refine ⟨Real.sqrt (t⁻¹ - 1), Real.sqrt_pos.2 (by linarith), ?_⟩
      simp only [hf]
      rw [Real.sq_sqrt (by linarith)]
      simp
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
  rw [himg] at hcv
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, hcv]
  have hvol : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  rw [hvol, Complex.finrank_real_complex, nsmul_eq_mul, ← integral_smul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0:ℝ) < r := hr
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpos : (0:ℝ) < 1 + r ^ 2 := by positivity
  have habs : |f' r| = 2 * r / (1 + r ^ 2) ^ 2 := by
    simp only [hf']
    rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rw [habs]
  simp only [hF, hf, one_div, pow_one, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hpi' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpi
  have hpos' : ((1 : ℂ) + (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp
  ring

end GlobalTheory.FibLine
end
end

section
set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine

theorem eq_zero_of_eval_real {σ : Type} (Q : MvPolynomial σ ℂ)
    (h : ∀ x : σ → ℝ, eval (fun i => (x i : ℂ)) Q = 0) : Q = 0 := by
  refine MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) ?_
  intro x hx
  have hx' : ∀ i, ∃ r : ℝ, (r : ℂ) = x i := fun i => hx i (Set.mem_univ i)
  choose r hr using hx'
  have : x = fun i => (r i : ℂ) := funext fun i => (hr i).symm
  rw [this, h, map_zero]

def hermSubst (ab : Fin 2 × Fin 2) : MvPolynomial (Fin 2 × Fin 2) ℂ :=
  !![X (0, 0), X (0, 1) + C Complex.I * X (1, 0); X (0, 1) - C Complex.I * X (1, 0), X (1, 1)] ab.1 ab.2

theorem eval_bind_hermSubst (P : MvPolynomial (Fin 2 × Fin 2) ℂ) (x : Fin 2 × Fin 2 → ℂ) :
    eval x (bind₁ hermSubst P) =
      eval (entries !![x (0, 0), x (0, 1) + Complex.I * x (1, 0); x (0, 1) - Complex.I * x (1, 0), x (1, 1)]) P := by
  have h1 : (fun i => eval x (hermSubst i)) =
      entries !![x (0, 0), x (0, 1) + Complex.I * x (1, 0); x (0, 1) - Complex.I * x (1, 0), x (1, 1)] := by
    funext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [hermSubst, entries]
  rw [← h1]
  exact eval₂Hom_bind₁ (RingHom.id ℂ) x hermSubst P

theorem eq_zero_of_eval_hermitian (P : MvPolynomial (Fin 2 × Fin 2) ℂ)
    (h : ∀ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian → MvPolynomial.eval (entries H) P = 0) : P = 0 := by
  have hQ : bind₁ hermSubst P = 0 := by
    refine eq_zero_of_eval_real _ fun x => ?_
    rw [eval_bind_hermSubst]
    refine h _ ?_
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.conjTranspose_apply, sub_eq_add_neg]
  refine MvPolynomial.funext fun y => ?_
  have h2 := eval_bind_hermSubst P
    (entries !![y (0, 0), (y (0, 1) + y (1, 0)) / 2; (y (0, 1) - y (1, 0)) / (2 * Complex.I), y (1, 1)])
  rw [hQ] at h2
  rw [map_zero] at h2 ⊢
  rw [h2]
  congr 2
  funext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> simp [entries] <;> field_simp <;> ring

end GlobalTheory.FibLine
end
end

section
set_option autoImplicit false

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine

theorem sub_mul_eval_hPoly (a b : ℂ) (k : ℕ) :
    (a - b) * MvPolynomial.eval ![a + b, a * b] (hPoly k) = a ^ (k + 1) - b ^ (k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [hPoly_zero]
  | one => simp [hPoly_one]; ring
  | more k h0 h1 =>
    rw [hPoly_add_two]
    simp only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination (a + b) * h1 - (a * b) * h0

theorem eval_hPoly_diag (a : ℂ) (k : ℕ) :
    MvPolynomial.eval ![a + a, a * a] (hPoly k) = ((k : ℂ) + 1) * a ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [hPoly_zero]
  | one => simp [hPoly_one]; ring
  | more k h0 h1 =>
    rw [hPoly_add_two]
    simp only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [h0, h1]
    push_cast
    ring

theorem integral_affine_pow_eq_hPoly (k : ℕ) (a b : ℂ) :
    ∫ t in (0 : ℝ)..1, ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k
      = MvPolynomial.eval ![a + b, a * b] (hPoly k) / ((k : ℂ) + 1) := by
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  by_cases hab : a = b
  · subst hab
    have : ∀ t : ℝ, ((t : ℂ) * a + (1 - (t : ℂ)) * a) ^ k = a ^ k := fun t => by ring
    simp only [this]
    rw [eval_hPoly_diag]
    simp
    field_simp
  · have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
        (fun t : ℝ => ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ (k + 1) / (((k : ℂ) + 1) * (a - b)))
        (((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k) t := by
      intro t _
      have h1 : HasDerivAt (fun z : ℂ => z * a + (1 - z) * b) (a - b) (t : ℂ) := by
        have := ((hasDerivAt_id (t : ℂ)).mul_const a).add
          (((hasDerivAt_id (t : ℂ)).const_sub 1).mul_const b)
        exact this.congr_deriv (by ring)
      have h2 := ((h1.pow (k + 1)).div_const (((k : ℂ) + 1) * (a - b))).comp_ofReal
      refine h2.congr_deriv ?_
      simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    have h := sub_mul_eval_hPoly a b k
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, sub_self, zero_mul, add_zero, zero_add, sub_zero]
    rw [← sub_div, ← h]
    field_simp

end GlobalTheory.FibLine
end

section
set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine.Intg

theorem integrable_fsDens : Integrable fsDens := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine (h.const_mul (1 / Real.pi)).congr (Filter.Eventually.of_forall fun x => ?_)
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have e : (-4 / 2 : ℝ) = -((2 : ℕ) : ℝ) := by norm_num
  simp only [fsDens]
  rw [e, Real.rpow_neg hx.le, Real.rpow_natCast]
  have := Real.pi_pos
  field_simp

theorem continuous_lineVec (a : Fin 2) : Continuous fun x : ℂ => lineVec x a := by
  fin_cases a
  · simpa [lineVec] using continuous_const
  · simpa [lineVec] using continuous_id'

theorem continuous_qCoef (ab : Fin 2 × Fin 2) : Continuous fun x : ℂ => qCoef x ab := by
  unfold qCoef
  refine Continuous.div ((continuous_lineVec _).mul (Complex.continuous_conj.comp (continuous_lineVec _)))
    (Complex.continuous_ofReal.comp (by fun_prop)) fun x => ?_
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  exact_mod_cast hx.ne'

theorem norm_lineVec_sq_le (x : ℂ) (a : Fin 2) : ‖lineVec x a‖ ^ 2 ≤ 1 + ‖x‖ ^ 2 := by
  fin_cases a
  · simp [lineVec]
  · simp [lineVec]

theorem norm_qCoef_le (x : ℂ) (ab : Fin 2 × Fin 2) : ‖qCoef x ab‖ ≤ 1 := by
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  unfold qCoef
  rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hx.le, div_le_one hx]
  have h1 := norm_lineVec_sq_le x ab.1
  have h2 := norm_lineVec_sq_le x ab.2
  nlinarith [sq_nonneg (‖lineVec x ab.2‖ - ‖lineVec x ab.1‖)]

theorem integrable_prod_qCoef_mul_fsDens (k : ℕ) (f : Fin k → Fin 2 × Fin 2) :
    Integrable (fun x : ℂ => (∏ i, qCoef x (f i)) * (fsDens x : ℂ)) := by
  have h : Integrable (fun x : ℂ => (fsDens x : ℂ)) := integrable_fsDens.ofReal
  refine h.bdd_mul (c := 1) (continuous_finset_prod _ fun i _ => continuous_qCoef (f i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => norm_qCoef_le x (f i)

end GlobalTheory.FibLine.Intg
end
end

section
set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine

theorem eval_fibPow (H : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    MvPolynomial.eval (entries H) (fibPow k) = ∫ x : ℂ, qMat H x ^ k * (fsDens x : ℂ) := by
  have e : ∀ x : ℂ, qMat H x ^ k * (fsDens x : ℂ) =
      ∑ f : Fin k → Fin 2 × Fin 2, (∏ i, qCoef x (f i)) * (fsDens x : ℂ) * ∏ i, entries H (f i) := by
    intro x
    rw [qMat, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [smul_eq_mul, Finset.prod_mul_distrib]
    ring
  simp only [fibPow, map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  simp_rw [e]
  rw [integral_finset_sum _ fun f _ => ((Intg.integrable_prod_qCoef_mul_fsDens k f).mul_const _)]
  simp only [integral_mul_const]

theorem qMat_diagonal (a b x : ℂ) : qMat (Matrix.diagonal ![a, b]) x =
    ((1 / (1 + ‖x‖ ^ 2) : ℝ) : ℂ) * a + (1 - ((1 / (1 + ‖x‖ ^ 2) : ℝ) : ℂ)) * b := by
  have h0 : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hx : x * starRingEnd ℂ x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [qMat, entries, Fintype.sum_prod_type, Fin.sum_univ_two, qCoef, lineVec, Matrix.diagonal_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, if_true, if_false, smul_zero, add_zero,
    zero_add, smul_eq_mul, map_one, mul_one, hx]
  simp
  left
  have h1 : (1 + (‖x‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h0
  field_simp
  ring

theorem fibPow_diagonal (a b : ℂ) (k : ℕ) : MvPolynomial.eval (entries (Matrix.diagonal ![a, b])) (fibPow k) =
    ∫ t in (0 : ℝ)..1, ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k := by
  rw [eval_fibPow]
  simp_rw [qMat_diagonal]
  exact integral_comp_fsDens (fun t : ℝ => ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k) (by fun_prop)

theorem eval_trDet {R : Type} [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (p : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.aeval (entries H) (MvPolynomial.aeval trDet p) = MvPolynomial.aeval ![H.trace, H.det] p := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have e : (fun i => MvPolynomial.aeval (entries H) (trDet i)) = ![H.trace, H.det] := by
    funext i
    fin_cases i <;> simp [trDet, entries, Matrix.trace_fin_two, Matrix.det_fin_two]
  rw [e]

theorem fibPow_eq (k : ℕ) : fibPow k = (1 / ((k : ℂ) + 1)) • MvPolynomial.aeval trDet (hPoly k) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_eval_hermitian _ fun H hH => ?_
  have hR : MvPolynomial.eval (entries H) (MvPolynomial.aeval trDet (hPoly k)) =
      MvPolynomial.eval ![H.trace, H.det] (hPoly k) := by
    simpa [MvPolynomial.coe_aeval_eq_eval] using eval_trDet H (hPoly k)
  rw [map_sub, sub_eq_zero, MvPolynomial.smul_eval, hR, eval_fibPow]
  set l₀ := (hH.eigenvalues 0 : ℂ)
  set l₁ := (hH.eigenvalues 1 : ℂ)
  have hD : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) = Matrix.diagonal ![l₀, l₁] := by
    congr 1; funext i; fin_cases i <;> rfl
  have hs := hH.spectral_theorem
  rw [hD, Unitary.conjStarAlgAut_apply] at hs
  have htr : H.trace = l₀ + l₁ := by rw [hH.trace_eq_sum_eigenvalues, Fin.sum_univ_two]; rfl
  have hdet : H.det = l₀ * l₁ := by rw [hH.det_eq_prod_eigenvalues, Fin.prod_univ_two]; rfl
  rw [htr, hdet]
  conv_lhs => rw [hs]
  rw [UnitaryInv.integral_qMat_unitary_conj _ (hH.eigenvectorUnitary).2, ← eval_fibPow, fibPow_diagonal, integral_affine_pow_eq_hPoly]
  ring

theorem eq_zero_of_eval_symm (P : MvPolynomial (Fin 2) ℂ) (h : ∀ a b : ℂ, MvPolynomial.eval ![a + b, a * b] P = 0) :
    P = 0 := by
  refine MvPolynomial.funext fun y => ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y 0 ^ 2 - 4 * y 1) two_pos
  have e : ![(y 0 + z) / 2 + (y 0 - z) / 2, (y 0 + z) / 2 * ((y 0 - z) / 2)] = y := by
    funext i
    fin_cases i
    · simp; ring
    · simp; linear_combination (-1 / 4 : ℂ) * hz
  simpa [e] using h ((y 0 + z) / 2) ((y 0 - z) / 2)

theorem aeval_fibPow {R : Type} [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    MvPolynomial.aeval (entries H) (fibPow k) =
      (1 / ((k : ℂ) + 1)) • MvPolynomial.aeval ![H.trace, H.det] (hPoly k) := by
  rw [fibPow_eq, map_smul, eval_trDet]


end GlobalTheory.FibLine
end
end
