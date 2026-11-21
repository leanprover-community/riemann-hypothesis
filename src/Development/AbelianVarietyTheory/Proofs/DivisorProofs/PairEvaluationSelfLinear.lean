import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecompositionStatement
import BuildAid.ForwardExisting

section
section
open scoped ContDiff

namespace GlobalTheory.ExpDivision

theorem hasTemperateGrowth_of_closed (S : Set (ℝ → ℂ))
    (hd : ∀ f ∈ S, Differentiable ℝ f) (hc : ∀ f ∈ S, deriv f ∈ S)
    (hb : ∀ f ∈ S, ∃ (k : ℕ) (C : ℝ), ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    {f : ℝ → ℂ} (hf : f ∈ S) : f.HasTemperateGrowth := by
  have hi : ∀ n, iteratedDeriv n f ∈ S := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih => rw [iteratedDeriv_succ]; exact hc _ ih
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => hd _ (hi m), fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hb _ (hi n)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact h x⟩

theorem hasTemperateGrowth_deriv {f : ℝ → ℂ} (hf : f.HasTemperateGrowth) :
    (deriv f).HasTemperateGrowth := by
  refine ⟨(contDiff_infty_iff_deriv.1 hf.1).2, fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  refine ⟨k, C, fun x => ?_⟩
  have := h x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at this ⊢
  rwa [iteratedDeriv_succ'] at this

theorem hasTemperateGrowth_div {E g : ℝ → ℂ} (hE : E.HasTemperateGrowth)
    (h0 : ∀ x, E x ≠ 0) {N : ℕ} {M : ℝ} (hM : ∀ x, ‖(E x)⁻¹‖ ≤ M * (1 + ‖x‖) ^ N)
    (hg : g.HasTemperateGrowth) : (fun x => g x / E x).HasTemperateGrowth := by
  have hEd : Differentiable ℝ E := hE.1.differentiable (by simp)
  refine hasTemperateGrowth_of_closed
    {f | ∃ (m : ℕ) (u : ℝ → ℂ), u.HasTemperateGrowth ∧ f = fun x => u x / E x ^ m} ?_ ?_ ?_
    ⟨1, g, hg, by simp⟩
  · rintro f ⟨m, u, hu, rfl⟩
    have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
    exact hud.div (hEd.pow m) fun x => pow_ne_zero _ (h0 x)
  · rintro f ⟨m, u, hu, rfl⟩
    have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
    have hp : (fun x => E x ^ m).HasTemperateGrowth := hE.pow m
    have hpd : Differentiable ℝ (fun x => E x ^ m) := hp.1.differentiable (by simp)
    refine ⟨m * 2, fun x => deriv u x * E x ^ m - u x * deriv (fun x => E x ^ m) x,
      ((hasTemperateGrowth_deriv hu).mul hp).sub (hu.mul (hasTemperateGrowth_deriv hp)), ?_⟩
    funext x
    rw [pow_mul]
    exact deriv_fun_div (hud x) (hpd x) (pow_ne_zero _ (h0 x))
  · rintro f ⟨m, u, hu, rfl⟩
    obtain ⟨k, C, h⟩ := hu.2 0
    refine ⟨k + N * m, C * M ^ m, fun x => ?_⟩
    have h1 : ‖u x‖ ≤ C * (1 + ‖x‖) ^ k := by simpa using h x
    have h2 := hM x
    have h3 : 0 ≤ C * (1 + ‖x‖) ^ k := (norm_nonneg _).trans h1
    calc ‖u x / E x ^ m‖ = ‖u x‖ * ‖(E x)⁻¹‖ ^ m := by
          rw [div_eq_mul_inv, norm_mul, ← inv_pow, norm_pow]
      _ ≤ (C * (1 + ‖x‖) ^ k) * (M * (1 + ‖x‖) ^ N) ^ m := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

theorem hasTemperateGrowth_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ R → ‖F z‖ ≤ C) :
    (fun t : ℝ => F t).HasTemperateGrowth := by
  refine hasTemperateGrowth_of_closed
    {f | ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ R → ‖G z‖ ≤ C) ∧
      f = fun t : ℝ => G t} ?_ ?_ ?_ ⟨F, hF, hb, rfl⟩
  · rintro f ⟨G, hG, -, rfl⟩ x
    exact (hG x).hasDerivAt.comp_ofReal.differentiableAt
  · rintro f ⟨G, hG, hB, rfl⟩
    refine ⟨deriv G, hG.deriv, fun R => ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hB (R + 1)
      refine ⟨C / 1, fun z hz => ?_⟩
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hG.diffContOnCl ?_
      intro w hw
      apply hC
      have h1 : ‖w - z‖ = 1 := by simpa [dist_eq_norm] using hw
      have h2 := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im, h1] at h2
      have h3 := abs_add_le (w.im - z.im) z.im
      rw [sub_add_cancel] at h3
      linarith
    · funext x
      exact (hG x).hasDerivAt.comp_ofReal.deriv
  · rintro f ⟨G, -, hB, rfl⟩
    obtain ⟨C, hC⟩ := hB 0
    exact ⟨0, C, fun x => by simpa using hC x (by simp)⟩

noncomputable def quot (a : ℝ) : ℂ → ℂ := dslope (fun z => Complex.exp (Complex.I * (a * z))) 0

theorem mul_quot (a : ℝ) (z : ℂ) : z * quot a z = Complex.exp (Complex.I * (a * z)) - 1 := by
  have := sub_smul_dslope (fun z : ℂ => Complex.exp (Complex.I * (a * z))) 0 z
  simpa [quot] using this

theorem quot_zero (a : ℝ) : quot a 0 = Complex.I * a := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * (a * z)))
      (Complex.exp (Complex.I * (a * 0)) * (Complex.I * (a * 1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).const_mul (a : ℂ)).const_mul Complex.I).cexp
  rw [quot, dslope_same, h.deriv]; simp

theorem differentiable_quot (a : ℝ) : Differentiable ℂ (quot a) := by
  rw [← differentiableOn_univ, quot, Complex.differentiableOn_dslope Filter.univ_mem]
  fun_prop

theorem hasTemperateGrowth_quot (a : ℝ) : (fun t : ℝ => quot a t).HasTemperateGrowth := by
  refine hasTemperateGrowth_of_entire (differentiable_quot a) fun R => ?_
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (differentiable_quot a).continuous.continuousOn
  refine ⟨max C (Real.exp (|a| * R) + 1), fun z hz => ?_⟩
  by_cases h : ‖z‖ ≤ 1
  · exact (hC z (by simpa using h)).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    push Not at h
    have h1 : ‖z‖ * ‖quot a z‖ ≤ Real.exp (|a| * R) + 1 := by
      rw [← norm_mul, mul_quot]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_exp, norm_one]
      gcongr
      have : (Complex.I * (a * z)).re = -(a * z.im) := by simp
      rw [this]
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      gcongr
    nlinarith [norm_nonneg (quot a z)]

theorem quot_neg (a t : ℝ) : quot (-a) t = (starRingEnd ℂ) (quot a t) := by
  by_cases ht : t = 0
  · subst ht; simp [quot_zero]
  · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    apply mul_left_cancel₀ ht'
    have := congrArg (starRingEnd ℂ) (mul_quot a t)
    rw [map_mul, Complex.conj_ofReal] at this
    rw [this, mul_quot, map_sub, ← Complex.exp_conj]
    simp

theorem norm_exp_sub_one_ge (x : ℝ) :
    4 * |x - round x| ≤ ‖Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ := by
  have h1 : Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * (x - round x) : ℝ) : ℂ)) := by
    have : Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) =
        Complex.I * ((2 * Real.pi * (x - round x) : ℝ) : ℂ) + (round x : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h2 := abs_sub_round x
  set d := x - round x
  have hp := Real.pi_pos
  have e : 2 * Real.pi * d / 2 = Real.pi * d := by ring
  have h3 : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hp]; nlinarith
  have h4 := Real.mul_abs_le_abs_sin h3
  rw [abs_mul, abs_of_pos hp] at h4
  have e2 : 2 / Real.pi * (Real.pi * |d|) = 2 * |d| := by field_simp
  rw [e2] at h4
  rw [e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  linarith

theorem dioph (t : ℝ) (hp : round t ≠ 0) :
    1 ≤ 6 * (1 + |t|) * (|t - round t| + |√2 * t - round (√2 * t)|) := by
  set p := round t with hpdef
  set q := round (√2 * t) with hqdef
  have h1 : |t - p| ≤ 1 / 2 := abs_sub_round t
  have h2 : |√2 * t - q| ≤ 1 / 2 := abs_sub_round _
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hs2 : √2 ≤ 3 / 2 := by nlinarith
  have hne : (2 * p ^ 2 - q ^ 2 : ℤ) ≠ 0 := by
    intro h
    have hr : (2 : ℝ) * p ^ 2 - q ^ 2 = 0 := by exact_mod_cast h
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    have : (√2 * p - q) * (√2 * p + q) = 0 := by nlinarith
    have hirr := irrational_sqrt_two
    rcases mul_eq_zero.1 this with h' | h'
    · exact hirr ⟨(q : ℚ) / p, by push_cast; field_simp; linarith⟩
    · exact hirr ⟨-(q : ℚ) / p, by push_cast; field_simp; linarith⟩
  have h3 : (1 : ℝ) ≤ |(2 : ℝ) * p ^ 2 - q ^ 2| := by
    have := Int.one_le_abs hne
    exact_mod_cast this
  have h4 : (2 : ℝ) * p ^ 2 - q ^ 2 = (√2 * p - q) * (√2 * p + q) := by nlinarith
  rw [h4, abs_mul] at h3
  have h5 : |√2 * p - q| ≤ 2 * (|t - p| + |√2 * t - q|) := by
    have : √2 * p - q = (√2 * t - q) - √2 * (t - p) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos hs0]
    nlinarith [abs_nonneg (t - p), abs_nonneg (√2 * t - q)]
  have h6 : |√2 * p + q| ≤ 3 * (1 + |t|) := by
    have : √2 * p + q = 2 * √2 * t - (√2 * t - q) - √2 * (t - p) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    have := abs_sub (2 * √2 * t) (√2 * t - q)
    rw [abs_mul, abs_mul, abs_of_pos hs0, abs_two] at this
    rw [abs_mul, abs_of_pos hs0]
    nlinarith [abs_nonneg (t - p), abs_nonneg t]
  calc (1 : ℝ) ≤ _ := h3
    _ ≤ (2 * (|t - p| + |√2 * t - q|)) * (3 * (1 + |t|)) := by gcongr
    _ = _ := by ring

theorem lower (t : ℝ) :
    1 ≤ 2 * (1 + |t|) ^ 2 * (‖quot (2 * Real.pi) t‖ + ‖quot (2 * Real.pi * √2) t‖) := by
  have a0 := abs_nonneg t
  have n1 := norm_nonneg (quot (2 * Real.pi) t)
  have n2 := norm_nonneg (quot (2 * Real.pi * √2) t)
  have e1 : 4 * |t - round t| ≤ |t| * ‖quot (2 * Real.pi) t‖ := by
    have := norm_exp_sub_one_ge t
    rwa [Complex.ofReal_mul _ t, ← mul_quot, norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
  have e2 : 4 * |√2 * t - round (√2 * t)| ≤ |t| * ‖quot (2 * Real.pi * √2) t‖ := by
    have := norm_exp_sub_one_ge (√2 * t)
    rwa [← mul_assoc, Complex.ofReal_mul _ t, ← mul_quot, norm_mul, Complex.norm_real,
      Real.norm_eq_abs] at this
  by_cases hp : round t = 0
  · have h1 : 1 ≤ ‖quot (2 * Real.pi) t‖ := by
      by_cases ht : t = 0
      · subst ht
        rw [Complex.ofReal_zero, quot_zero, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith [Real.pi_gt_three]
      · rw [hp] at e1
        simp only [Int.cast_zero, sub_zero] at e1
        have : 0 < |t| := abs_pos.2 ht
        by_contra hh
        nlinarith
    have h2 : 1 ≤ (1 + |t|) ^ 2 := by nlinarith
    nlinarith
  · have h := dioph t hp
    set s := ‖quot (2 * Real.pi) t‖ + ‖quot (2 * Real.pi * √2) t‖ with hs
    have hs0 : 0 ≤ s := by positivity
    have h1 : 4 * (|t - round t| + |√2 * t - round (√2 * t)|) ≤ (1 + |t|) * s := by
      rw [hs]; nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + |t| by positivity)
    have h3 : 0 ≤ (1 + |t|) ^ 2 * s := by positivity
    nlinarith

theorem exists_division : ∃ (n : ℕ) (a : Fin n → ℝ) (A : Fin n → ℝ → ℂ),
    (∀ j, Function.HasTemperateGrowth (A j)) ∧
    ∀ t : ℝ, (t : ℂ) = ∑ j, (Complex.exp (Complex.I * ((a j * t : ℝ) : ℂ)) - 1) * A j t := by
  set a : ℝ := 2 * Real.pi with ha
  set b : ℝ := 2 * Real.pi * √2 with hb
  set E : ℝ → ℂ := fun t => quot a t * quot (-a) t + quot b t * quot (-b) t with hE
  have hEt : E.HasTemperateGrowth :=
    ((hasTemperateGrowth_quot a).mul (hasTemperateGrowth_quot (-a))).add
      ((hasTemperateGrowth_quot b).mul (hasTemperateGrowth_quot (-b)))
  have hn : ∀ t, ‖E t‖ = ‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2 := by
    intro t
    have : E t = ((‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2 : ℝ) : ℂ) := by
      simp only [hE, quot_neg, Complex.mul_conj']
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hl : ∀ t, 1 ≤ 8 * (1 + ‖t‖) ^ 4 * ‖E t‖ := by
    intro t
    have h := lower t
    rw [← ha, ← hb] at h
    rw [hn, Real.norm_eq_abs]
    have h2 := one_le_pow₀ (n := 2) h
    have h3 : (‖quot a t‖ + ‖quot b t‖) ^ 2 ≤ 2 * (‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2) := by
      nlinarith [sq_nonneg (‖quot a t‖ - ‖quot b t‖)]
    calc (1 : ℝ) ≤ _ := h2
      _ = 4 * (1 + |t|) ^ 4 * (‖quot a t‖ + ‖quot b t‖) ^ 2 := by ring
      _ ≤ 4 * (1 + |t|) ^ 4 * (2 * (‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2)) := by gcongr
      _ = _ := by ring
  have h0 : ∀ t, E t ≠ 0 := by
    intro t h
    have := hl t
    rw [h] at this
    norm_num at this
  have hM : ∀ t, ‖(E t)⁻¹‖ ≤ 8 * (1 + ‖t‖) ^ 4 := by
    intro t
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.2 (h0 t))]
    exact hl t
  refine ⟨2, ![a, b], ![fun t => quot (-a) t / E t, fun t => quot (-b) t / E t], ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hasTemperateGrowth_div hEt h0 hM (hasTemperateGrowth_quot _)
    · exact hasTemperateGrowth_div hEt h0 hM (hasTemperateGrowth_quot _)
  · intro t
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Complex.ofReal_mul a t, Complex.ofReal_mul b t, ← mul_quot, ← mul_quot]
    have := h0 t
    field_simp
    simp only [hE]

end GlobalTheory.ExpDivision
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identity_as_sum_exp_minus_one : ∃ (n : ℕ) (a : Fin n → ℝ) (A : Fin n → ℝ → ℂ), (∀ j, Function.HasTemperateGrowth (A j)) ∧
    ∀ t : ℝ, (t : ℂ) = ∑ j, (Complex.exp (Complex.I * ((a j * t : ℝ) : ℂ)) - 1) * A j t := by
  atlas_forward_decl GlobalTheory.ExpDivision.exists_division
end

section
section
namespace GlobalTheory.CharInvForm

theorem iteratedDeriv_exp_I (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (Complex.I * y)) =
      fun y : ℝ => Complex.I ^ n * Complex.exp (Complex.I * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => Complex.I ^ n * Complex.exp (Complex.I * y))
        (Complex.I ^ n * (Complex.exp (Complex.I * y) * (Complex.I * 1))) y :=
      ((h1.const_mul Complex.I).cexp).const_mul (Complex.I ^ n)
    rw [h.deriv]; ring

theorem temperate_exp_I : Function.HasTemperateGrowth (fun y : ℝ => Complex.exp (Complex.I * y)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (Complex.I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_I, pow_zero, mul_one, norm_mul, norm_pow,
    mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
  simp

theorem kills_linear_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := by
  intro V _ _ _ T hT L h g hg
  obtain ⟨n, a, A, hA, hdiv⟩ := GlobalTheory.T.identity_as_sum_exp_minus_one
  have hAL : ∀ j, Function.HasTemperateGrowth (fun x : V => A j (L x)) := fun j =>
    (hA j).comp L.hasTemperateGrowth
  have hE : ∀ j, Function.HasTemperateGrowth
      (fun x : V => Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ))) := fun j =>
    temperate_exp_I.comp (a j • L).hasTemperateGrowth
  let k : Fin n → SchwartzMap V ℂ := fun j => SchwartzMap.smulLeftCLM ℂ (fun x : V => A j (L x)) h
  let f' : Fin n → SchwartzMap V ℂ := fun j =>
    SchwartzMap.smulLeftCLM ℂ (fun x : V => Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ))) (k j)
  have hk : ∀ j x, k j x = A j (L x) * h x := fun j x => by
    simp only [k]
    rw [SchwartzMap.smulLeftCLM_apply_apply (hAL j), smul_eq_mul]
  have hf : ∀ j x, f' j x = Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ)) * k j x := fun j x => by
    simp only [f']
    rw [SchwartzMap.smulLeftCLM_apply_apply (hE j), smul_eq_mul]
  have hsum : g = ∑ j, (f' j - k j) := by
    ext x
    rw [SchwartzMap.sum_apply, hg x]
    conv_lhs => rw [hdiv (L x)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SchwartzMap.sub_apply, hf, hk, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_sub, hT (a j • L) (k j) (f' j) (hf j), sub_self]

end GlobalTheory.CharInvForm
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulation_invariant_functional_kills_linear_multiple : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := by
  atlas_forward_decl GlobalTheory.CharInvForm.kills_linear_mul
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SvNLinear

theorem kills_linear_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := GlobalTheory.T.modulation_invariant_functional_kills_linear_multiple

theorem arch (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ)
    (hT : ∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.CharInvForm.exists_schwartz_one V
  refine ⟨T f₀, fun f => ?_⟩
  have h0 : (f - f 0 • f₀) 0 = 0 := by simp [hf₀]
  obtain ⟨n, L, h, g, hg, hsum⟩ := GlobalTheory.T.schwartz_vanishing_decomposition V _ h0
  have e : f - f 0 • f₀ = ∑ i, g i := by
    ext x
    rw [hsum x, SchwartzMap.sum_apply]
  have : T (f - f 0 • f₀) = 0 := by
    rw [e, map_sum]
    exact Finset.sum_eq_zero fun i _ => kills_linear_mul V T hT (L i) (h i) (g i) (hg i)
  rw [map_sub, map_smul, sub_eq_zero] at this
  rw [this, smul_eq_mul, mul_comm]

open scoped Classical

open GlobalTheory.CharInvForm in

theorem charInv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ),
    (∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * φ x) = l φ) →
    ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * φ 0 := by
  intro F _ _ ψ hψ κ _ l hinv

  have harch : ∀ g ∈ SB (κ → Af F), ∃ α : ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = α * f 0 := by
    intro g hg
    let T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun f => l (pureA F f g)
        map_add' := fun f f' => by
          rw [← map_add]
          congr 1
          funext x
          simp only [pureA, SchwartzMap.add_apply, Pi.add_apply]
          ring
        map_smul' := fun s f => by
          rw [RingHom.id_apply, ← map_smul]
          congr 1
          funext x
          simp only [pureA, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]
          ring }
    obtain ⟨α, hα⟩ := arch _ T (by
      intro L f f' hff'
      obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ L
      show l (pureA F f' g) = l (pureA F f g)
      rw [← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
        (pureA F f g) (mem_schA f hg)]
      congr 1
      funext x
      simp only [pureA, hff', psi_dot_inf hψ, hY]
      ring)
    exact ⟨α, hα⟩

  obtain ⟨f₀, hf₀⟩ := exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)
  let a : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => l (pureA F f₀ g)
      map_add' := fun g g' => by
        rw [← map_add]
        congr 1
        funext x
        simp only [pureA, Pi.add_apply]
        ring
      map_smul' := fun s g => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        funext x
        simp only [pureA, Pi.smul_apply, smul_eq_mul]
        ring }
  obtain ⟨c, hc⟩ := GlobalTheory.CharForm.exists_eq_mul_apply_zero (κ → Af F) {χ | ∃ y : κ → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))}
    (by
      intro N hN
      obtain ⟨U, hUo, hUc, hUN, hsep⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ N hN
      refine ⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩
      obtain ⟨y, hyU, hy⟩ := hsep x₀ hx₀
      refine ⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩
      show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))
      rw [add_dotProduct, pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one])
    a
    (by
      rintro χ ⟨y, rfl⟩ g hg
      show l (pureA F f₀ _) = l (pureA F f₀ g)
      rw [← hinv (fun i => pairA F 0 (y i)) (pureA F f₀ g) (mem_schA f₀ hg)]
      congr 1
      funext x
      simp only [pureA, dot_pairA_fin]
      ring)
  refine ⟨c, fun φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    obtain ⟨α, hα⟩ := harch g hg
    have hαc : α = c * g 0 := by
      have e1 := hα f₀
      rw [hf₀, mul_one] at e1
      rw [← e1]
      exact hc g hg
    rw [hα f, hαc, pureA_zero]
    ring
  | zero => simp
  | add φ φ' _ _ h h' => rw [map_add, h, h', Pi.add_apply, mul_add]
  | smul s φ _ h => rw [map_smul, h, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring

theorem eval_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    SchwartzMap.toBoundedContinuousFunction_apply, smul_eq_mul]
  ring

end GlobalTheory.SvNLinear

namespace GlobalTheory.SvNLinear

open GlobalTheory.AdelicSvN

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F L = Fintype.card κ → ∀ (l₁ l₂ : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ),
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ := by
  intro _ F _ _ ψ hψ κ _ L hL hdim l₁ l₂ hi₁ hi₂ ⟨φ₀, hφ₀, hne⟩
  classical
  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := realised_of_mem_closure ψ hψ hg

  have hlin : ∀ (a b : ℂ), ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, S (a • φ + b • φ') = a • S φ + b • S φ' := by
    intro a b φ hφ φ' hφ'
    funext x
    obtain ⟨l', _, e⟩ := hSa _ (eval_mem_adm x)
    have hm : a • φ + b • φ' ∈ schA F κ := add_mem (Submodule.smul_mem _ a hφ) (Submodule.smul_mem _ b hφ')
    have e1 := e _ hm
    have e2 := e φ hφ
    have e3 := e φ' hφ'
    simp only [LinearMap.proj_apply] at e1 e2 e3
    rw [← e1, map_add, map_smul, map_smul, e2, e3]
    rfl
  have key : ∀ l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) →
      ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0 := by
    intro l hi
    let f : schA F κ →ₗ[ℂ] ℂ :=
      { toFun := fun φ => l (S φ.1)
        map_add' := fun φ φ' => by
          have := hlin 1 1 φ.1 φ.2 φ'.1 φ'.2
          simp only [one_smul] at this
          simp only [Submodule.coe_add, this, map_add]
        map_smul' := fun s φ => by
          have := hlin s 0 φ.1 φ.2 0 (Submodule.zero_mem _)
          simp only [zero_smul, add_zero] at this
          simp only [Submodule.coe_smul, this, map_smul, RingHom.id_apply, smul_eq_mul] }
    obtain ⟨l', hl'⟩ := LinearMap.exists_extend f
    have e : ∀ φ (hφ : φ ∈ schA F κ), l' φ = l (S φ) := fun φ hφ => LinearMap.congr_fun hl' ⟨φ, hφ⟩
    obtain ⟨c, hc⟩ := charInv F ψ hψ κ l' (fun y φ hφ => by
      have hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
      rw [hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, act_zero_eq_sum]
      exact inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
    exact ⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩
  obtain ⟨c₁, h₁⟩ := key l₁ hi₁
  obtain ⟨c₂, h₂⟩ := key l₂ hi₂
  obtain ⟨ψ₀, hψ₀, rfl⟩ := hSs φ₀ hφ₀
  have hc₂ : c₂ ≠ 0 := fun h => hne (by rw [h₂ ψ₀ hψ₀, h, zero_mul])
  refine ⟨c₁ / c₂, fun φ hφ => ?_⟩
  obtain ⟨φ', hφ', rfl⟩ := hSs φ hφ
  rw [h₁ φ' hφ', h₂ φ' hφ']
  field_simp

end GlobalTheory.SvNLinear
end
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThK.EvChangeUniq

def ratInc (F R κ : Type) [Field F] [CommRing R] [Algebra F R] : ((κ → F) × (κ → F)) →ₗ[F] ((κ → R) × (κ → R)) where
  toFun w := (fun i => algebraMap F R (w.1 i), fun i => algebraMap F R (w.2 i))
  map_add' a b := by ext <;> simp
  map_smul' a b := by ext <;> simp [Algebra.smul_def]

theorem ratInc_injective (F R κ : Type) [Field F] [CommRing R] [Algebra F R] (h : Function.Injective (algebraMap F R)) :
    Function.Injective (ratInc F R κ) := by
  intro a b hab
  have h1 := congrArg Prod.fst hab
  have h2 := congrArg Prod.snd hab
  exact Prod.ext (funext fun i => h (congrFun h1 i)) (funext fun i => h (congrFun h2 i))

theorem exists_rat {F R κ V : Type} [Field F] [CommRing R] [Algebra F R] [AddCommGroup V] [Module F V]
    (h : Function.Injective (algebraMap F R)) (c : V →ₗ[F] ((κ → R) × (κ → R)))
    (hc : ∀ x, ∃ w, c x = ratInc F R κ w) :
    ∃ q : V →ₗ[F] ((κ → F) × (κ → F)), ∀ x, ratInc F R κ (q x) = c x := by
  have hmem : ∀ x, c x ∈ LinearMap.range (ratInc F R κ) := fun x => by
    obtain ⟨w, hw⟩ := hc x
    exact ⟨w, hw.symm⟩
  refine ⟨(LinearEquiv.ofInjective _ (ratInc_injective F R κ h)).symm.toLinearMap ∘ₗ c.codRestrict _ hmem, fun x => ?_⟩
  have := LinearEquiv.ofInjective_apply (ratInc F R κ) (h := ratInc_injective F R κ h)
    ((LinearEquiv.ofInjective _ (ratInc_injective F R κ h)).symm (c.codRestrict _ hmem x))
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem exists_lagrangian {F R κ V : Type} [Field F] [CommRing R] [Algebra F R] [AddCommGroup V] [Module F V] [Fintype κ]
    [FiniteDimensional F V] (hV : Module.finrank F V = Fintype.card κ + Fintype.card κ)
    (h : Function.Injective (algebraMap F R)) (c c₁ : V →ₗ[F] ((κ → R) × (κ → R)))
    (hc : ∀ x, ∃ w, c x = ratInc F R κ w) (hc₁ : ∀ x, ∃ w, c₁ x = ratInc F R κ w)
    (hi : Function.Injective c) (hi₁ : Function.Injective c₁)
    (hf : ∀ x y, (c x).1 ⬝ᵥ (c y).2 - (c y).1 ⬝ᵥ (c x).2 = (c₁ x).1 ⬝ᵥ (c₁ y).2 - (c₁ y).1 ⬝ᵥ (c₁ x).2) :
    ∃ L : Submodule F ((κ → F) × (κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card κ ∧ ∀ w ∈ L, ∃ x, ratInc F R κ w = c x ∧ (c₁ x).1 = 0 := by
  obtain ⟨q, hq⟩ := exists_rat h c hc
  obtain ⟨q₁, hq₁⟩ := exists_rat h c₁ hc₁
  have hqi : Function.Injective q := fun a b hab => hi (by rw [← hq, ← hq, hab])
  have hqi₁ : Function.Injective q₁ := fun a b hab => hi₁ (by rw [← hq₁, ← hq₁, hab])
  have hqs : Function.Surjective q₁ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hV])).1 hqi₁
  let K : Submodule F V := LinearMap.ker (LinearMap.fst F _ _ ∘ₗ q₁)
  have hK : Module.finrank F K = Fintype.card κ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.fst F _ _ ∘ₗ q₁)
    have h2 : LinearMap.range (LinearMap.fst F _ _ ∘ₗ q₁) = ⊤ :=
      LinearMap.range_eq_top.2 (Prod.fst_surjective.comp hqs)
    rw [h2, finrank_top, hV, Module.finrank_fintype_fun_eq_card] at h1
    exact Nat.add_left_cancel h1
  have hL : ∀ w ∈ K.map q, ∃ x, ratInc F R κ w = c x ∧ (c₁ x).1 = 0 := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, hq x, ?_⟩
    have hx' : (q₁ x).1 = 0 := hx
    rw [← hq₁]
    funext i
    simp [ratInc, hx']
  refine ⟨K.map q, fun a ha b hb => ?_, ?_, hL⟩
  · obtain ⟨x, hx, hx0⟩ := hL a ha
    obtain ⟨y, hy, hy0⟩ := hL b hb
    have h1 := hf x y
    rw [hx0, hy0, ← hx, ← hy, zero_dotProduct, zero_dotProduct, sub_zero, sub_eq_zero] at h1
    apply h
    simpa [dotProduct, ratInc] using h1
  · rw [← hK]
    exact (Submodule.equivMapOfInjective q hqi K).finrank_eq.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def incL (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n d : ℕ) :
    Matrix (Fin n) (Fin d) E →ₗ[F] Matrix (Fin n) (Fin d) (AE F E) :=
  LinearMap.mapMatrix (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).toLinearMap

theorem incL_injective (n d : ℕ) : Function.Injective (incL F E n d) := by
  intro a b hab
  ext i j
  exact Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F) (congrFun (congrFun hab i) j)

theorem eq_smul_isEv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e → ∀ f : Fn F n d →ₗ[ℂ] Fn F n d,
    (∀ (z : Matrix (Fin n) (Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d), f (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (f Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), f Φ = c • e Φ := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ e hM₁ hev f hfh
  have hψ : IsStd B.ψ := hpair.base.std
  have hM : M.IsGood B.ψ := hpair.good
  have h2 : Module.finrank F E = 2 := hpair.base.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let ev0 : Fn F n d →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ : (Fin n × Fin d → AF F) => ℂ) 0
  have hmem : ∀ (w : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d), Φ ∈ schA F (Fin n × Fin d) →
      M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
    fun w Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ hΦ
  have hrec : ∀ S : Fn F n d →ₗ[ℂ] Fn F n d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (S Φ)) →
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ y, S Φ y = ev0 (S (M.co.rho B.ψ (M₁.co.e.symm (y, 0)) Φ)) := by
    intro S hS Φ hΦ y
    rw [hS _ Φ hΦ]
    simp [ev0, Darboux.rho, schr]
  obtain ⟨L, hiso, hrk, hL⟩ := exists_lagrangian (F := F) (R := AF F) (κ := Fin n × Fin d) (V := Matrix (Fin n) (Fin d) E)
    (by rw [Module.finrank_matrix, h2]; simp; ring) (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)
    (M.co.e.toLinearMap.restrictScalars F ∘ₗ incL F E n d) (M₁.co.e.toLinearMap.restrictScalars F ∘ₗ incL F E n d)
    (fun x => by obtain ⟨y, z, h⟩ := hM.rat x; exact ⟨(y, z), h⟩)
    (fun x => by obtain ⟨y, z, h⟩ := hM₁.rat x; exact ⟨(y, z), h⟩)
    (M.co.e.injective.comp (incL_injective n d)) (M₁.co.e.injective.comp (incL_injective n d))
    (fun x y => (M.co.form _ _).symm.trans (M₁.co.form _ _))
  have inv : ∀ S : Fn F n d →ₗ[ℂ] Fn F n d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (S Φ)) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ Φ ∈ schA F (Fin n × Fin d),
        (ev0 ∘ₗ S) (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) Φ) =
          (ev0 ∘ₗ S) Φ := by
    intro S hS t w hw Φ hΦ
    obtain ⟨x, hx, hx0⟩ := hL w hw
    have hx' : ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) = M.co.e (incM F x) := hx
    have hx1 : (M₁.co.e (incM F x)).1 = 0 := hx0
    have hz : (M₁.co.e (t • incM F x)).1 = 0 := by rw [map_smul, Prod.smul_fst, hx1, smul_zero]
    have he : schr B.ψ (t • M.co.e (incM F x)) Φ = M.co.rho B.ψ (t • incM F x) Φ := by
      rw [Darboux.rho, map_smul]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hx', he, hS _ Φ hΦ]
    generalize t • incM F x = z at hz
    simp [ev0, Darboux.rho, schr, hz]
  have hevh : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (e Φ) := by
    intro z Φ hΦ
    have := hev.Heisenberg₂ z Φ hΦ
    have h1 : ∀ m : ℕ, incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := fun m => by simp [incM]
    rwa [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  obtain ⟨ei, ev, hei, hloc0, hloc⟩ := hev.loc
  have hex : ∀ v : Pl F, ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (M₁.vac v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = M.vac v) := by
    intro v
    by_cases h : M₁.vac v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem' : Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin n × Fin d → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem'
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨g, hg⟩ : ∃ g, ei g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  have hΦ₀ : pure g φ ∈ schA F (Fin n × Fin d) := (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφSB hstd).2
  have hne : e (pure g φ) ≠ 0 := by
    rw [hloc g φ hφSB hcof, show (fun v => ev v (φ v)) = fun v =>
      Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 from funext hφev]
    intro h0
    apply hg
    apply GlobalTheory.ThK.EvUniqInf.eq_of_pure_std (ei g) 0
    rw [h0]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := GlobalTheory.SvNLinear.main hK.base F B.ψ hψ (Fin n × Fin d) L hiso hrk (ev0 ∘ₗ f) (ev0 ∘ₗ e) (inv f hfh) (inv e hevh)
    ⟨M.co.rho B.ψ (M₁.co.e.symm (y₀, 0)) (pure g φ), hmem _ _ hΦ₀, by
      rw [LinearMap.comp_apply, ← hrec e hevh _ hΦ₀ y₀]; exact hy₀⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  rw [hrec f hfh Φ hΦ y, Pi.smul_apply, hrec e hevh Φ hΦ y, smul_eq_mul]
  exact hc _ (hmem _ _ hΦ)

end GlobalTheory.ThK.EvChangeUniq
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_evaluation_self_linear : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e → ∀ f : Fn F n d →ₗ[ℂ] Fn F n d,
    (∀ (z : Matrix (Fin n) (Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d), f (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (f Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), f Φ = c • e Φ := by
  atlas_forward_decl GlobalTheory.ThK.EvChangeUniq.eq_smul_isEv
end
