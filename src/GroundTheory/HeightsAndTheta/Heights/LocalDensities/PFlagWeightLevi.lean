import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import ReciprocityTheory.AnalyticForms.MaIntEmpty

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm Filter Topology Polynomial

noncomputable section

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_apply_eq_deriv_deriv {φ : E → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (v : E) :
    fderiv ℝ (fderiv ℝ φ) 0 v v = deriv (deriv fun t : ℝ => φ (t • v)) 0 := by
  have hev : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t • v) v t := fun t => by
    simpa using (hasDerivAt_id t).smul_const v
  have hline : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
    have : Continuous fun t : ℝ => t • v := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hder : (deriv fun t : ℝ => φ (t • v)) =ᶠ[𝓝 0] fun t => fderiv ℝ φ (t • v) v := by
    filter_upwards [hline.eventually hev] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hlin t)).deriv
  rw [hder.deriv_eq]
  have h2 : DifferentiableAt ℝ (fderiv ℝ φ) 0 :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have h3 : HasDerivAt ((fderiv ℝ φ) ∘ fun t : ℝ => t • v) (fderiv ℝ (fderiv ℝ φ) 0 v) 0 :=
    h2.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hlin 0) (by simp)
  have h4 := h3.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simpa using h4.deriv.symm

end Line

section Levi

variable {ι : Type*} [Fintype ι]

theorem levi_finset_sum {κ : Type*} (s : Finset κ) (F : κ → (ι → ℂ) → ℝ)
    (hF : ∀ j ∈ s, ContDiffAt ℝ 2 (F j) 0) (w : ι → ℂ) :
    levi (fun z => ∑ j ∈ s, F j z) 0 w = ∑ j ∈ s, levi (F j) 0 w := by
  have hev : ∀ᶠ z in 𝓝 (0 : ι → ℂ), ∀ j ∈ s, DifferentiableAt ℝ (F j) z := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact ((hF j hj).eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have h1 : fderiv ℝ (fun z => ∑ j ∈ s, F j z) =ᶠ[𝓝 0] fun z => ∑ j ∈ s, fderiv ℝ (F j) z := by
    filter_upwards [hev] with z hz
    simpa only [Finset.sum_fn] using fderiv_sum hz
  have h2 : fderiv ℝ (fderiv ℝ fun z => ∑ j ∈ s, F j z) 0 =
      ∑ j ∈ s, fderiv ℝ (fderiv ℝ (F j)) 0 := by
    rw [h1.fderiv_eq]
    simpa only [Finset.sum_fn] using fderiv_sum fun j hj =>
      ((hF j hj).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  simp only [levi, h2, _root_.sum_apply]
  rw [← Finset.sum_add_distrib, Finset.sum_div]

theorem levi_eq_deriv_deriv {φ : (ι → ℂ) → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (w : ι → ℂ) :
    levi φ 0 w = (deriv (deriv fun t : ℝ => φ (t • w)) 0 +
      deriv (deriv fun t : ℝ => φ (t • (Complex.I • w))) 0) / 4 := by
  simp only [levi, fderiv_fderiv_apply_eq_deriv_deriv hφ]

end Levi

section LogPoly

theorem deriv_deriv_log_norm_eval (Q : ℂ[X]) (h0 : Q.coeff 0 = 1) (h1 : Q.coeff 1 = 0) :
    deriv (deriv fun t : ℝ => Real.log ‖Q.eval (t : ℂ)‖) 0 = 2 * (Q.coeff 2).re := by
  set f : ℝ → ℂ := fun t => Q.eval (t : ℂ) with hfdef
  have hf : ∀ t : ℝ, HasDerivAt f (Q.derivative.eval (t : ℂ)) t := fun t =>
    (Q.hasDerivAt (t : ℂ)).comp_ofReal
  have hf' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Q.derivative.eval (t : ℂ))
      (Q.derivative.derivative.eval (t : ℂ)) t := fun t =>
    (Q.derivative.hasDerivAt (t : ℂ)).comp_ofReal
  have hf0 : f 0 = 1 := by simp [f, ← Polynomial.coeff_zero_eq_eval_zero, h0]
  have hslit : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ Complex.slitPlane := by
    have hc : Continuous f := Q.continuous.comp Complex.continuous_ofReal
    exact hc.continuousAt.eventually
      (Complex.isOpen_slitPlane.mem_nhds (by rw [hf0]; exact Complex.one_mem_slitPlane))
  have hD : (deriv fun t : ℝ => Real.log ‖f t‖) =ᶠ[𝓝 0]
      fun t => Complex.reCLM (Q.derivative.eval (t : ℂ) / f t) := by
    filter_upwards [hslit] with t ht
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hf t).clog_real ht)
    have he : (fun t : ℝ => Real.log ‖f t‖) = Complex.reCLM ∘ fun t => Complex.log (f t) := by
      funext t; simp [Complex.log_re]
    rw [he]; exact h2.deriv
  rw [hD.deriv_eq]
  have hq := (hf' 0).div (hf 0) (by rw [hf0]; exact one_ne_zero)
  have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  rw [show (fun t : ℝ => Complex.reCLM (Q.derivative.eval (t : ℂ) / f t)) =
    Complex.reCLM ∘ ((fun t : ℝ => Q.derivative.eval (t : ℂ)) / f) from rfl, h3.deriv]
  have e1 : Q.derivative.eval ((0 : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp [h1]
  have e2 : Q.derivative.derivative.eval ((0 : ℝ) : ℂ) = 2 * Q.coeff 2 := by
    rw [Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
      Polynomial.coeff_derivative]
    norm_num [mul_comm]
  rw [hf0, e1, e2]
  simp

end LogPoly

end

end GroundTheory.Heights₂.Heights.FourB
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open Polynomial Matrix

noncomputable section

theorem sum_fin_split_castLE {M : Type*} [AddCommMonoid M] {i N : ℕ} (hi : i ≤ N)
    (f : Fin N → M) :
    ∑ c, f c = ∑ c : Fin i, f (Fin.castLE hi c) + ∑ c, if i ≤ c.val then f c else 0 := by
  have h1 : (Finset.univ.filter fun c : Fin N => c.val < i) =
      Finset.univ.map (Fin.castLEEmb hi) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro h; exact ⟨⟨c.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨c', rfl⟩; exact c'.isLt
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : Fin N => c.val < i), h1,
    Finset.sum_map, Finset.sum_filter]
  simp only [Fin.castLEEmb_apply, not_lt]

theorem contDiff_det_of_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Type*} [Fintype m] [DecidableEq m] {M : E → Matrix m m ℂ}
    (h : ∀ a b, ContDiff ℝ 2 fun x => M x a b) : ContDiff ℝ 2 fun x => (M x).det := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  exact (contDiff_prod fun a _ => h _ _).const_smul _

variable {N : ℕ}

def sigSign (p : ℕ) (a : Fin N) : ℝ := if a.val < p then 1 else -1

theorem signatureForm_eq (p : ℕ) :
    signatureForm N p = diagonal fun a => ((sigSign p a : ℝ) : ℂ) := by
  unfold signatureForm
  congr 1
  funext a
  unfold sigSign
  split_ifs <;> simp

def tailSum (p i : ℕ) (L : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ b : Fin N, ∑ c : Fin N,
    if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0

section Poly

variable (p i : ℕ) (hi : i ≤ N) (L : Matrix (Fin N) (Fin N) ℂ)

def colPoly : Matrix (Fin N) (Fin i) ℂ[X] :=
  Matrix.of fun c b => (if c = Fin.castLE hi b then 1 else 0) + X * C (L c (Fin.castLE hi b))

def rowPoly : Matrix (Fin i) (Fin N) ℂ[X] :=
  Matrix.of fun a c =>
    (if c = Fin.castLE hi a then 1 else 0) + X * C (star (L c (Fin.castLE hi a)))

def topPoly : Matrix (Fin i) (Fin i) ℂ[X] := (colPoly i hi L).submatrix (Fin.castLE hi) id

def topPoly' : Matrix (Fin i) (Fin i) ℂ[X] := (rowPoly i hi L).submatrix id (Fin.castLE hi)

def sigTop : Matrix (Fin i) (Fin i) ℂ :=
  diagonal fun a => ((sigSign p (Fin.castLE hi a) : ℝ) : ℂ)

def tailForm : Matrix (Fin i) (Fin i) ℂ :=
  Matrix.of fun a b => ∑ c : Fin N, if i ≤ c.val then
    star (L c (Fin.castLE hi a)) * ((sigSign p c : ℝ) : ℂ) * L c (Fin.castLE hi b) else 0

def kerPoly : Matrix (Fin i) (Fin i) ℂ[X] :=
  (sigTop p i hi).map C * (topPoly' i hi L).adjugate * (tailForm p i hi L).map C *
    (topPoly i hi L).adjugate

theorem gram_eq : rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L =
    topPoly' i hi L * (sigTop p i hi).map C * topPoly i hi L +
      (X ^ 2 : ℂ[X]) • (tailForm p i hi L).map C := by
  rw [signatureForm_eq]
  refine Matrix.ext fun a b => ?_
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply]
  simp only [Matrix.diagonal_map (map_zero C), Matrix.mul_diagonal]
  rw [sum_fin_split_castLE hi]
  congr 1
  · rw [sigTop, Matrix.diagonal_map (map_zero C), Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    rfl
  · simp only [tailForm, Matrix.of_apply, map_sum, Finset.mul_sum, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · have h1 : ∀ a : Fin i, c ≠ Fin.castLE hi a := fun a h => by
        have := congrArg Fin.val h
        simp at this
        omega
      simp only [rowPoly, colPoly, Matrix.of_apply, h1, if_false, zero_add, map_mul]
      ring
    · simp

theorem sigTop_mul_self : sigTop p i hi * sigTop p i hi = 1 := by
  rw [sigTop, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  unfold sigSign
  split_ifs <;> simp

variable {L}

theorem det_topPoly (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) : (topPoly i hi L).det = 1 := by
  rw [det_of_isLowerTriangular _ ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [topPoly, colPoly, hL _ _ (lt_irrefl _)]
  · intro a b hab
    have hab' : a < b := by simpa using hab
    have h1 : Fin.castLE hi a ≠ Fin.castLE hi b := fun h =>
      (ne_of_lt hab') (Fin.castLE_injective hi h)
    have h2 : L (Fin.castLE hi a) (Fin.castLE hi b) = 0 :=
      hL _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; exact fun h => absurd hab' (by
        rw [Fin.lt_def]; omega))
    simp [topPoly, colPoly, h1, h2]

theorem det_topPoly' (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) : (topPoly' i hi L).det = 1 := by
  rw [det_of_isUpperTriangular ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [topPoly', rowPoly, hL _ _ (lt_irrefl _)]
  · intro a b hab
    have hab' : b < a := by simpa using hab
    have h1 : Fin.castLE hi b ≠ Fin.castLE hi a := fun h =>
      (ne_of_lt hab') (Fin.castLE_injective hi h)
    have h2 : L (Fin.castLE hi b) (Fin.castLE hi a) = 0 :=
      hL _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; exact fun h => absurd hab' (by
        rw [Fin.lt_def]; omega))
    simp [topPoly', rowPoly, h1, h2]

theorem det_gram (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) :
    (rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L).det =
      C (sigTop p i hi).det * (1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi L).det := by
  have hSS : (sigTop p i hi).map C * (sigTop p i hi).map C = 1 := by
    rw [← Matrix.map_mul, sigTop_mul_self]; simp
  have hK : topPoly' i hi L * (sigTop p i hi).map C * kerPoly p i hi L * topPoly i hi L =
      (tailForm p i hi L).map C := by
    calc topPoly' i hi L * (sigTop p i hi).map C * kerPoly p i hi L * topPoly i hi L
        = (topPoly' i hi L * ((sigTop p i hi).map C * (sigTop p i hi).map C) *
            (topPoly' i hi L).adjugate) * (tailForm p i hi L).map C *
            ((topPoly i hi L).adjugate * topPoly i hi L) := by
          simp only [kerPoly, Matrix.mul_assoc]
      _ = (tailForm p i hi L).map C := by
          rw [hSS, Matrix.mul_one, Matrix.mul_adjugate, Matrix.adjugate_mul, det_topPoly i hi hL,
            det_topPoly' i hi hL, one_smul, Matrix.one_mul, Matrix.mul_one]
  have hfac : rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L =
      topPoly' i hi L * (sigTop p i hi).map C * (1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi L) *
        topPoly i hi L := by
    rw [gram_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
      Matrix.smul_mul, hK]
  rw [hfac, det_mul, det_mul, det_mul, det_topPoly i hi hL, det_topPoly' i hi hL, one_mul,
    mul_one]
  rw [show ((sigTop p i hi).map C).det = C (sigTop p i hi).det from
    ((C : ℂ →+* ℂ[X]).map_det _).symm]

end Poly

theorem coeff_det_one_add_X_sq_smul {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ[X]) :
    (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 0 = 1 ∧ (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 1 = 0 ∧
      (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 2 = K.trace.coeff 0 := by
  rw [det_one_add_smul]
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_one, ← pow_mul, coeff_mul_X_pow']

end

end GroundTheory.Heights₂.Heights.FourB
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open Polynomial Matrix

noncomputable section

variable {N : ℕ} (p i : ℕ) (hi : i ≤ N)

theorem lowerMatrix_strict (u : LowerPair N → ℂ) :
    ∀ a b : Fin N, ¬ b < a → lowerMatrix u a b = 0 := by
  intro a b h
  simp [lowerMatrix, h]

theorem coeff_trace_kerPoly (L : Matrix (Fin N) (Fin N) ℂ) :
    (kerPoly p i hi L).trace.coeff 0 = (sigTop p i hi * tailForm p i hi L).trace := by
  have hV : (topPoly i hi L).map (evalRingHom 0) = 1 := by
    refine Matrix.ext fun a b => ?_
    simp [topPoly, colPoly, Matrix.one_apply, Fin.castLE_inj] <;> split_ifs <;> simp
  have hV' : (topPoly' i hi L).map (evalRingHom 0) = 1 := by
    refine Matrix.ext fun a b => ?_
    simp [topPoly', rowPoly, Matrix.one_apply, Fin.castLE_inj, eq_comm] <;> split_ifs <;> simp
  have hadj : ∀ M : Matrix (Fin i) (Fin i) ℂ[X],
      M.adjugate.map (evalRingHom 0) = (M.map (evalRingHom 0)).adjugate := fun M =>
    (evalRingHom (0 : ℂ)).map_adjugate M
  have hC : ∀ M : Matrix (Fin i) (Fin i) ℂ, (M.map C).map (evalRingHom 0) = M := fun M => by
    refine Matrix.ext fun a b => ?_
    simp
  have hmap : (kerPoly p i hi L).map (evalRingHom 0) = sigTop p i hi * tailForm p i hi L := by
    simp only [kerPoly, Matrix.map_mul, hadj, hV, hV', adjugate_one, Matrix.mul_one, hC]
  rw [coeff_zero_eq_eval_zero, ← hmap]
  simp [Matrix.trace, eval_finsetSum]

theorem re_trace_sigTop_tail (L : Matrix (Fin N) (Fin N) ℂ) :
    (sigTop p i hi * tailForm p i hi L).trace.re = tailSum p i L := by
  rw [tailSum, sum_fin_split_castLE hi (fun b => ∑ c : Fin N,
    if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0)]
  have h2 : (∑ b : Fin N, if i ≤ b.val then (∑ c : Fin N,
      if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0) else 0) =
      0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · exact Finset.sum_eq_zero fun c _ => if_neg (by omega)
    · rfl
  rw [h2, add_zero, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.diag_apply, sigTop, tailForm, Matrix.diagonal_mul, Matrix.of_apply,
    Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have ha : (Fin.castLE hi a).val < i := by simp
  by_cases hc : i ≤ c.val
  · rw [if_pos hc, if_pos ⟨ha, hc⟩]
    have : star (L c (Fin.castLE hi a)) * ((sigSign p c : ℝ) : ℂ) * L c (Fin.castLE hi a) =
        ((sigSign p c * ‖L c (Fin.castLE hi a)‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm (star _), mul_assoc, Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  · rw [if_neg hc, if_neg (fun h => hc h.2)]
    simp

theorem colPoly_eval (u : LowerPair N → ℂ) (t : ℝ) :
    (colPoly i hi (lowerMatrix u)).map (evalRingHom (t : ℂ)) =
      ((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id (Fin.castLE hi) := by
  refine Matrix.ext fun c b => ?_
  by_cases h : Fin.castLE hi b < c
  · simp [colPoly, lowerMatrix, Matrix.one_apply, h, Complex.real_smul] <;> split_ifs <;>
      simp [mul_comm]
  · simp [colPoly, lowerMatrix, Matrix.one_apply, h] <;> split_ifs <;> simp

theorem rowPoly_eval (u : LowerPair N → ℂ) (t : ℝ) :
    (rowPoly i hi (lowerMatrix u)).map (evalRingHom (t : ℂ)) =
      (((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id
        (Fin.castLE hi)).conjTranspose := by
  refine Matrix.ext fun a c => ?_
  by_cases h : Fin.castLE hi a < c
  · have h2 : c ≠ Fin.castLE hi a := fun h' => by rw [h'] at h; exact lt_irrefl _ h
    simp only [Matrix.map_apply, rowPoly, Matrix.of_apply, coe_evalRingHom, eval_add, eval_mul,
      eval_X, eval_C, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq,
      Matrix.add_apply, Matrix.one_apply, lowerMatrix, dif_pos h, if_neg h2, eval_zero, zero_add]
    simp [Complex.real_smul, mul_comm]
  · by_cases h2 : c = Fin.castLE hi a
    · subst h2; simp [rowPoly, lowerMatrix]
    · simp [rowPoly, lowerMatrix, h, h2]

theorem det_flag_eval (u : LowerPair N → ℂ) (t : ℝ) :
    ((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id
        (Fin.castLE hi)).conjTranspose * signatureForm N p *
        ((1 + lowerMatrix (t • u)).submatrix id (Fin.castLE hi))).det =
      (sigTop p i hi).det *
        ((1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi (lowerMatrix u)).det).eval (t : ℂ) := by
  have hS : signatureForm N p = ((signatureForm N p).map C).map (evalRingHom (t : ℂ)) := by
    refine Matrix.ext fun a b => ?_
    simp
  rw [← rowPoly_eval, ← colPoly_eval, hS, ← Matrix.map_mul, ← Matrix.map_mul]
  rw [show ∀ M : Matrix (Fin i) (Fin i) ℂ[X], (M.map (evalRingHom (t : ℂ))).det =
      evalRingHom (t : ℂ) M.det from fun M => ((evalRingHom (t : ℂ)).map_det M).symm]
  rw [det_gram p i hi (lowerMatrix_strict u)]
  simp

theorem norm_det_sigTop : ‖(sigTop p i hi).det‖ = 1 := by
  rw [sigTop, det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sigSign
  split_ifs <;> simp

theorem flagPs_smul (u : LowerPair N → ℂ) (t : ℝ) :
    flagPs N p i hi (t • u) =
      Real.log ‖((1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi (lowerMatrix u)).det).eval (t : ℂ)‖ := by
  rw [flagPs, det_flag_eval, norm_mul, norm_det_sigTop, one_mul]

theorem deriv_deriv_flagPs (u : LowerPair N → ℂ) :
    deriv (deriv fun t : ℝ => flagPs N p i hi (t • u)) 0 = 2 * tailSum p i (lowerMatrix u) := by
  simp only [flagPs_smul]
  obtain ⟨h0, h1, h2⟩ := coeff_det_one_add_X_sq_smul (kerPoly p i hi (lowerMatrix u))
  rw [deriv_deriv_log_norm_eval _ h0 h1, h2, coeff_trace_kerPoly, re_trace_sigTop_tail]

theorem contDiffAt_flagPs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → (LowerPair N → ℂ)} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0) :
    ContDiffAt ℝ 2 (fun z => flagPs N p i hi (g z)) 0 := by
  have hent : ∀ a b, ContDiff ℝ 2 fun z =>
      ((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (g z)) a b := by
    intro a b
    by_cases h : b < a
    · simp only [Matrix.add_apply, lowerMatrix, Matrix.of_apply, h, dif_pos]
      exact contDiff_const.add
        ((by fun_prop : ContDiff ℝ 2 fun f : LowerPair N → ℂ => f ⟨(a, b), h⟩).comp hg)
    · simp only [Matrix.add_apply, lowerMatrix, Matrix.of_apply, h, dif_neg, not_false_eq_true,
        add_zero]
      exact contDiff_const
  have hdet : ContDiff ℝ 2 fun z => ((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (g z)).submatrix
      id (Fin.castLE hi)).conjTranspose * signatureForm N p *
      ((1 + lowerMatrix (g z)).submatrix id (Fin.castLE hi))).det := by
    refine contDiff_det_of_entries fun a b => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
    refine ContDiff.sum fun c _ => ContDiff.mul (ContDiff.sum fun d _ => ContDiff.mul ?_
      contDiff_const) (hent _ _)
    simpa [Function.comp_def] using Complex.conjCLE.contDiff.comp (hent d (Fin.castLE hi a))
  have h0 : ((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (g 0)).submatrix id
      (Fin.castLE hi)).conjTranspose * signatureForm N p *
      ((1 + lowerMatrix (g 0)).submatrix id (Fin.castLE hi))).det ≠ 0 := by
    have h := det_flag_eval p i hi (0 : LowerPair N → ℂ) 0
    rw [zero_smul] at h
    rw [hg0, h, Complex.ofReal_zero, ← coeff_zero_eq_eval_zero,
      (coeff_det_one_add_X_sq_smul _).1, mul_one]
    intro h'
    have := norm_det_sigTop p i hi
    rw [h', norm_zero] at this
    exact zero_ne_one this
  unfold flagPs
  exact (ContDiffAt.norm ℝ hdet.contDiffAt h0).log (norm_ne_zero_iff.mpr h0)

end

end GroundTheory.Heights₂.Heights.FourB
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm

noncomputable section

def flagTerm (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (j : Fin f × Fin N)
    (z : (Σ _ : Fin f, LowerPair N) → ℂ) : ℝ :=
  if h : j.2.val + 1 < N then
    (lam j.1 j.2 - lam j.1 ⟨j.2.val + 1, h⟩) * flagPs N p (j.2.val + 1) h.le fun q => z ⟨j.1, q⟩
  else 0

theorem flagWeightProd_eq (f N p : ℕ) (lam : Fin f → Fin N → ℝ) :
    flagWeightProd f N p lam = fun z => ∑ j : Fin f × Fin N, flagTerm f N p lam j z := by
  funext z
  simp only [flagWeightProd, flagWeight, flagTerm, Fintype.sum_prod_type]

theorem contDiff_factor {f N : ℕ} (τ : Fin f) :
    ContDiff ℝ 2 fun z : (Σ _ : Fin f, LowerPair N) → ℂ => fun q : LowerPair N => z ⟨τ, q⟩ := by
  fun_prop

theorem contDiffAt_flagTerm (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (j : Fin f × Fin N) :
    ContDiffAt ℝ 2 (flagTerm f N p lam j) 0 := by
  unfold flagTerm
  by_cases h : j.2.val + 1 < N
  · simp only [h, dif_pos]
    exact contDiffAt_const.mul (contDiffAt_flagPs p _ h.le (contDiff_factor j.1) rfl)
  · simp only [h, dif_neg, not_false_eq_true]
    exact contDiffAt_const

theorem tailSum_I {N : ℕ} (p i : ℕ) (u : LowerPair N → ℂ) :
    tailSum p i (lowerMatrix (Complex.I • u)) = tailSum p i (lowerMatrix u) := by
  have : ∀ c b, ‖lowerMatrix (Complex.I • u) c b‖ = ‖lowerMatrix u c b‖ := by
    intro c b
    simp only [lowerMatrix, Matrix.of_apply]
    split_ifs <;> simp
  simp only [tailSum, this]

theorem deriv_deriv_term {f N : ℕ} (p : ℕ) (c : ℝ) (i : ℕ) (hi : i ≤ N) (τ : Fin f)
    (v : (Σ _ : Fin f, LowerPair N) → ℂ) :
    deriv (deriv fun t : ℝ => c * flagPs N p i hi fun q => (t • v) ⟨τ, q⟩) 0 =
      c * (2 * tailSum p i (lowerMatrix fun q => v ⟨τ, q⟩)) := by
  rw [deriv_const_mul_field', deriv_const_mul_field']
  exact congrArg (c * ·) (deriv_deriv_flagPs p i hi fun q => v ⟨τ, q⟩)

theorem levi_flagTerm (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (j : Fin f × Fin N)
    (w : (Σ _ : Fin f, LowerPair N) → ℂ) :
    levi (flagTerm f N p lam j) 0 w = if h : j.2.val + 1 < N then
      (lam j.1 j.2 - lam j.1 ⟨j.2.val + 1, h⟩) * tailSum p (j.2.val + 1)
        (lowerMatrix fun q => w ⟨j.1, q⟩) else 0 := by
  rw [levi_eq_deriv_deriv (contDiffAt_flagTerm f N p lam j) w]
  by_cases h : j.2.val + 1 < N
  · simp only [flagTerm, h, dif_pos]
    rw [deriv_deriv_term, deriv_deriv_term,
      show (fun q => (Complex.I • w) ⟨j.1, q⟩) = Complex.I • (fun q => w ⟨j.1, q⟩) from rfl,
      tailSum_I]
    ring
  · simp only [flagTerm, h, dif_neg, not_false_eq_true]
    simp

theorem sum_Ico_telescope (Λ : ℕ → ℝ) (b m : ℕ) :
    ∑ k ∈ Finset.Ico b (b + m), (Λ k - Λ (k + 1)) = Λ b - Λ (b + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show b + (m + 1) = b + m + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]
    ring

theorem sum_fin_telescope {N : ℕ} (Λ : ℕ → ℝ) (b c : ℕ) (hbc : b < c) (hc : c ≤ N) :
    ∑ k : Fin N, (if b ≤ k.val ∧ k.val < c then Λ k - Λ (k.val + 1) else 0) = Λ b - Λ c := by
  rw [show (∑ k : Fin N, (if b ≤ k.val ∧ k.val < c then Λ k - Λ (k.val + 1) else 0)) =
      ∑ k ∈ Finset.range N, (if b ≤ k ∧ k < c then Λ k - Λ (k + 1) else 0) from
    Fin.sum_univ_eq_sum_range (fun k => if b ≤ k ∧ k < c then Λ k - Λ (k + 1) else 0) N]
  rw [← Finset.sum_filter]
  have : (Finset.range N).filter (fun k => b ≤ k ∧ k < c) = Finset.Ico b (b + (c - b)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, sum_Ico_telescope, Nat.add_sub_cancel' hbc.le]

theorem sum_steps_eq_rootPairing (N p : ℕ) (lam : Fin N → ℝ) (u : LowerPair N → ℂ) :
    ∑ k : Fin N, (if h : k.val + 1 < N then
      (lam k - lam ⟨k.val + 1, h⟩) * tailSum p (k.val + 1) (lowerMatrix u) else 0) =
      ∑ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 := by
  set Λ : ℕ → ℝ := fun n => if h : n < N then lam ⟨n, h⟩ else 0 with hΛ
  set A : Fin N → Fin N → ℝ := fun a b => sigSign p b * sigSign p a * ‖lowerMatrix u a b‖ ^ 2
    with hA
  have step1 : ∀ k : Fin N, (if h : k.val + 1 < N then
      (lam k - lam ⟨k.val + 1, h⟩) * tailSum p (k.val + 1) (lowerMatrix u) else 0) =
      ∑ b : Fin N, ∑ a : Fin N,
        (if b.val ≤ k.val ∧ k.val < a.val then Λ k - Λ (k.val + 1) else 0) * A a b := by
    intro k
    by_cases h : k.val + 1 < N
    · rw [dif_pos h, tailSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have e1 : Λ k = lam k := by simp [hΛ, k.isLt]
      have e2 : Λ (k.val + 1) = lam ⟨k.val + 1, h⟩ := by simp [hΛ, h]
      by_cases hba : b.val ≤ k.val ∧ k.val < a.val
      · rw [if_pos (by omega), if_pos hba, e1, e2, hA]
      · rw [if_neg (by omega), if_neg hba]
        simp
    · rw [dif_neg h]
      symm
      refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => ?_
      rw [if_neg (by have := a.isLt; omega)]
      simp
  have step2 : (∑ k : Fin N, ∑ b : Fin N, ∑ a : Fin N,
      (if b.val ≤ k.val ∧ k.val < a.val then Λ k - Λ (k.val + 1) else 0) * A a b) =
      ∑ a : Fin N, ∑ b : Fin N, if b < a then (Λ b - Λ a) * A a b else 0 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul]
    by_cases hba : b < a
    · rw [if_pos hba, sum_fin_telescope Λ b.val a.val hba a.isLt.le]
    · have hba' : ¬ b.val < a.val := fun h' => hba h'
      rw [if_neg hba, Finset.sum_eq_zero (fun k _ => if_neg (by omega)), zero_mul]
  have step3 : ∑ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 =
      ∑ a : Fin N, ∑ b : Fin N, if b < a then (Λ b - Λ a) * A a b else 0 := by
    have e : ∀ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 =
        (fun x : Fin N × Fin N => if x.2 < x.1 then (Λ x.2 - Λ x.1) * A x.1 x.2 else 0) q.1 := by
      rintro ⟨⟨a, b⟩, hab⟩
      show _ = if b < a then (Λ b - Λ a) * A a b else 0
      rw [if_pos hab]
      have hl : lowerMatrix u a b = u ⟨(a, b), hab⟩ := by simp [lowerMatrix, hab]
      have hab' : b.val < a.val := hab
      simp only [hA, hΛ, hl, rootPairing, sigSign, dif_pos a.isLt, dif_pos b.isLt, Fin.eta]
      split_ifs <;> first | ring1 | (exfalso; omega)
    rw [Fintype.sum_congr _ _ e]
    rw [← Finset.sum_subtype (Finset.univ.filter fun x : Fin N × Fin N => x.2 < x.1) (by simp)
      (fun x : Fin N × Fin N => if x.2 < x.1 then (Λ x.2 - Λ x.1) * A x.1 x.2 else 0)]
    rw [Finset.sum_filter_of_ne (fun x _ hx => by by_contra h; exact hx (if_neg h)),
      Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun k _ => step1 k, step2, step3]

theorem FlagWeightLevi.proof : FlagWeightLevi.Statement := by
  intro f N p lam w
  rw [flagWeightProd_eq,
    levi_finset_sum _ _ (fun j _ => contDiffAt_flagTerm f N p lam j)]
  simp only [levi_flagTerm]
  rw [Fintype.sum_prod_type, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact sum_steps_eq_rootPairing N p (lam τ) (fun q => w ⟨τ, q⟩)

end

end GroundTheory.Heights₂.Heights.FourB
end
