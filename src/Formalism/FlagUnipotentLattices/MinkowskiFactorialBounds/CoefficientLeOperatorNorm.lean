import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder

namespace Formalism.HermitianLatticeCounting.P


theorem coefficient_le_operator_norm : CoeffLeOp := by
  intro H _ _ E U w hE hw hn
  have : inner ℂ w (U w) = inner ℂ w ((E ∘L U ∘L E) w) := by
    simp only [ContinuousLinearMap.comp_apply, hw]
    rw [← hE, hw]
  rw [this]
  calc ‖inner ℂ w ((E ∘L U ∘L E) w)‖ ≤ ‖w‖ * ‖(E ∘L U ∘L E) w‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖E ∘L U ∘L E‖ * ‖w‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hn]; ring


theorem minimum_linear_form : MinLinear := by
  intro q ε s hq hε h1 hs
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hs0 : 0 < Real.sqrt (2 * (q:ℝ)) := Real.sqrt_pos.mpr (by linarith)
  refine le_min (by nlinarith) ?_
  rw [le_div_iff₀ hs0]
  have : 0 < s := by linarith
  nlinarith



theorem trace_diagonal_bis : TraceDiag := by
  intro X ι _ μ _ _ F h
  have e : ∀ w x, star (F w x) * F w x = ((‖F w x‖^2 : ℝ) : ℂ) := by
    intro w x
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have h1 : ∀ w, (∫ x, ((‖F w x‖^2 : ℝ) : ℂ) ∂μ) = 1 := by
    intro w
    have := h w w
    simp only [e, if_true] at this
    exact this
  have hint : ∀ w, Integrable (fun x => ‖F w x‖^2) μ := by
    intro w
    by_contra hn
    have h2 : ¬ Integrable (fun x => ((‖F w x‖^2 : ℝ) : ℂ)) μ := fun hi => hn (by
      have h4 := hi.re
      simpa [← Complex.ofReal_pow] using h4)
    have h3 := integral_undef h2
    rw [h1 w] at h3
    exact one_ne_zero h3
  rw [integral_finsetSum _ (fun w _ => hint w)]
  have h2 : ∀ w, ∫ x, ‖F w x‖^2 ∂μ = 1 := by
    intro w
    have := h1 w
    rw [integral_complex_ofReal] at this
    exact_mod_cast this
  simp [h2]


theorem diagonal_splitting : DiagSplit := by
  intro X _ μ _ K Rm Mod k0 hM hK hKR
  rw [← integral_add_compl hM hK]
  congr 1
  have hR : IntegrableOn Rm Mod μ := by
    have : IntegrableOn (fun x => K x - k0) Mod μ := hK.integrableOn.sub (integrable_const _)
    refine this.congr_fun (fun x hx => ?_) hM
    simp only
    rw [hKR x hx]; ring
  rw [setIntegral_congr_fun hM hKR, integral_add (integrable_const _) hR]
  simp [mul_comm, Measure.real]

theorem rank_one_case : RankOne := by
  intro G H _ _ U P m hP hPU v hv hcyc v' hv'
  have h1 : ∀ g, P (U g v) = m g • v := by
    intro g
    have h1 := congrArg (fun T : H →L[ℂ] H => T v) (hPU g)
    simpa [hv] using h1
  have hle : Submodule.span ℂ (Set.range fun g => U g v) ≤ (Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, h1]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have hclosed : IsClosed (((Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) := by
    have : IsClosed ((Submodule.span ℂ {v} : Submodule ℂ H) : Set H) := Submodule.closed_of_finiteDimensional _
    exact this.preimage P.continuous
  have htop := Submodule.topologicalClosure_minimal _ hle hclosed
  rw [hcyc] at htop
  have : v' ∈ (Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H) := htop trivial
  simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hv'] at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
  exact ⟨c, hc.symm⟩

theorem threshold_head_region : ThreshHead := by
  intro C₂
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(120 + |C₂|) / Real.log 2, by positivity, ?_⟩
  intro n q f b rd h hn hf hq hb hrd hh
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hqn : (q:ℝ)^2 ≤ n := by exact_mod_cast hq
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hqn1 : (q:ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hq
    exact_mod_cast this
  have hlog : Real.log 2 ≤ Real.log (b * rd) := Real.log_le_log (by norm_num) (by nlinarith)
  have h19 : 0 < (n:ℝ)^19 := by positivity
  have hK : (120 + |C₂|) * (n:ℝ)^19 ≤ h := by
    refine le_trans ?_ hh
    have h1 : (1:ℝ) ≤ (f:ℝ)^5 := one_le_pow₀ hf'
    have hA : 0 ≤ 120 + |C₂| := by positivity
    calc (120 + |C₂|) * (n:ℝ)^19 = (120 + |C₂|) / Real.log 2 * (n:ℝ)^19 * 1 * Real.log 2 := by
          field_simp
      _ ≤ (120 + |C₂|) / Real.log 2 * (n:ℝ)^19 * (f:ℝ)^5 * Real.log (b*rd) := by gcongr
  have hq32 : (q:ℝ)^((3:ℝ)/2) ≤ n := by
    rcases Nat.eq_zero_or_pos q with rfl | hqp
    · rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]; positivity
    · have h1 : (1:ℝ) ≤ q := by exact_mod_cast hqp
      calc (q:ℝ)^((3:ℝ)/2) ≤ (q:ℝ)^((2:ℝ)) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = (q:ℝ)^2 := Real.rpow_two _
        _ ≤ n := hqn
  have hsq : Real.sqrt q ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hp2 : (n:ℝ)^2 ≤ (n:ℝ)^19 := pow_le_pow_right₀ hn' (by norm_num)
  have hp3 : (n:ℝ)^3 ≤ (n:ℝ)^19 := pow_le_pow_right₀ hn' (by norm_num)
  have hC : 0 ≤ |C₂| * (n:ℝ)^19 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc 120 * (n:ℝ) * (q:ℝ)^((3:ℝ)/2) ≤ 120 * (n:ℝ) * n := by gcongr
      _ = 120 * (n:ℝ)^2 := by ring
      _ ≤ h := by linarith
  · calc C₂ * (n:ℝ)^2 * Real.sqrt q ≤ |C₂| * (n:ℝ)^2 * n := by
          gcongr
          exact le_abs_self _
      _ = |C₂| * (n:ℝ)^3 := by ring
      _ ≤ |C₂| * (n:ℝ)^19 := by gcongr
      _ ≤ h := by linarith
  · calc 32 * (n:ℝ) * q ≤ 32 * (n:ℝ) * n := by gcongr
      _ = 32 * (n:ℝ)^2 := by ring
      _ < h := by linarith






theorem far_region_prefactor : FarPrefactor := by
  intro n f τs hn hf hτ hnτ
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hss : Real.sqrt (n:ℝ) ^ 2 = n := Real.sq_sqrt (by linarith)
  have hfm : f ≤ n ^ 2 * f := Nat.le_mul_of_pos_left _ (by positivity)
  have e1 : (3 * Real.sqrt n / τs ^ 2) ^ (2 * n ^ 2 * f) = (9 * n / τs ^ 4) ^ (n ^ 2 * f) := by
    rw [mul_assoc 2, pow_mul]
    congr 1
    rw [div_pow, mul_pow, hss]; ring
  have e2 : (3 / τs) ^ (5 * n ^ 2 * f) = (243 / τs ^ 5) ^ (n ^ 2 * f) := by
    rw [mul_assoc 5, pow_mul]
    congr 1
    rw [div_pow]; norm_num
  rw [e1, e2]
  calc (9 * (n:ℝ) / τs ^ 4) ^ (n ^ 2 * f) * 4 ^ f
      ≤ (9 * (n:ℝ) / τs ^ 4) ^ (n ^ 2 * f) * 4 ^ (n ^ 2 * f) := by
        gcongr
        · norm_num
    _ = (9 * (n:ℝ) / τs ^ 4 * 4) ^ (n ^ 2 * f) := (mul_pow _ _ _).symm
    _ ≤ (243 / τs ^ 5) ^ (n ^ 2 * f) := by
        apply pow_le_pow_left₀ (by positivity)
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : 9 * (n:ℝ) * 4 * τs ^ 5 = 36 * (n * τs) * τs ^ 4 := by ring
        rw [this]
        have h4 : 0 < τs ^ 4 := by positivity
        nlinarith



theorem final_sum_near_far : FinalSum := by
  intro c A hc hA
  set c2 := min c 1 with hc2
  have hc20 : 0 < c2 := lt_min hc one_pos
  set L := 2 * Real.log (2 * (1 + 2 * A)) / c2 with hL
  refine ⟨c2 / 2, by positivity, max 3 ⌈L⌉₊, ?_⟩
  intro n f D Ds pr E₁ E₂ hn hf hD hDs hpr hpr2 hE1 hE2 hDeq
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hnL : L ≤ n := Nat.ceil_le.mp ((le_max_right _ _).trans hn)
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hn0 : (0:ℝ) < n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9; linarith
  have hlogn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  set x := (n:ℝ) * f * Real.log n with hx
  have hxn : (n:ℝ) ≤ x := by
    have : (n:ℝ) * 1 * 1 ≤ n * f * Real.log n := by gcongr
    linarith
  have hx0 : 0 ≤ x := by linarith
  set G := Real.exp (-(c2 / 2 * x)) with hG
  have hG0 : 0 < G := Real.exp_pos _
  have hG1 : G ≤ 1 := by
    rw [hG]; apply Real.exp_le_one_iff.mpr
    have : 0 ≤ c2 / 2 * x := by positivity
    linarith
  have hGA : 2 * (1 + 2 * A) * G ≤ 1 := by
    have hp : 0 < 2 * (1 + 2 * A) := by positivity
    have : 2 * (1 + 2 * A) = Real.exp (Real.log (2 * (1 + 2 * A))) := (Real.exp_log hp).symm
    rw [this, hG, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have h1 : L ≤ x := hnL.trans hxn
    rw [hL, div_le_iff₀ hc20] at h1
    linarith
  have he1 : Real.exp (-(c * n * f * Real.log n)) ≤ G * G := by
    rw [hG, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : c2 * x ≤ c * x := by
      apply mul_le_mul_of_nonneg_right (min_le_left _ _) hx0
    have e : c * n * f * Real.log n = c * x := by rw [hx]; ring
    rw [e]; linarith
  have he2 : Real.exp (-((n:ℝ) ^ 2 * f)) ≤ G * G := by
    rw [hG, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : c2 * x ≤ 1 * x := by
      apply mul_le_mul_of_nonneg_right (min_le_right _ _) hx0
    have h2 : x ≤ (n:ℝ) ^ 2 * f := by
      rw [hx]
      calc (n:ℝ) * f * Real.log n ≤ n * f * n := by gcongr
        _ = _ := by ring
    linarith
  have e3 : Real.exp (-(c2 / 2 * n * f * Real.log n)) = G := by
    rw [hG, hx]; congr 1; ring
  rw [e3]
  generalize Real.exp (-(c * n * f * Real.log n)) = e1 at *
  generalize Real.exp (-((n:ℝ) ^ 2 * f)) = e2 at *
  have hGG : 0 ≤ G * G := by positivity
  have b1 : |E₁| ≤ A * (G * G) * Ds := hE1.trans (by gcongr)
  have b2 : |E₂| ≤ A * (G * G) * D := hE2.trans (by gcongr)
  have b3 : |Ds * (pr - 1)| ≤ G * G * Ds := by
    rw [abs_mul, abs_of_nonneg hDs, mul_comm]
    apply mul_le_mul_of_nonneg_right _ hDs
    rw [abs_le]; constructor <;> linarith
  have hdiff : D - Ds = Ds * (pr - 1) + E₁ + E₂ := by rw [hDeq]; ring
  have b4 : |D - Ds| ≤ G * G * Ds + A * (G * G) * Ds + A * (G * G) * D := by
    rw [hdiff]
    calc _ ≤ |Ds * (pr - 1) + E₁| + |E₂| := abs_add_le _ _
      _ ≤ |Ds * (pr - 1)| + |E₁| + |E₂| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith
  have b5 : D ≤ Ds + |D - Ds| := by have := le_abs_self (D - Ds); linarith
  have hAG : A * (G * G) ≤ 1 / 4 := by
    have : A * G ≤ 1 / 4 := by nlinarith
    have h0 : 0 ≤ A * G := by positivity
    nlinarith
  have hAGG0 : 0 ≤ A * (G * G) := by positivity
  have b6 : A * (G * G) * D ≤ A * (G * G) * Ds + 1 / 4 * |D - Ds| := by
    calc A * (G * G) * D ≤ A * (G * G) * (Ds + |D - Ds|) := by gcongr
      _ = A * (G * G) * Ds + A * (G * G) * |D - Ds| := by ring
      _ ≤ _ := by gcongr
  have b7 : |D - Ds| ≤ 2 * (1 + 2 * A) * G * (G * Ds) := by
    have h0 : 0 ≤ G * G * Ds := by positivity
    have h1 : 0 ≤ A * (G * G) * Ds := by positivity
    nlinarith
  calc |D - Ds| ≤ 2 * (1 + 2 * A) * G * (G * Ds) := b7
    _ ≤ 1 * (G * Ds) := by gcongr
    _ = G * Ds := one_mul _

lemma le_rpow_two_mul {Y C : ℝ} (hY : 2 ≤ Y) (hC : 0 ≤ C) : C ≤ Y ^ (2 * C) := by
  have hY0 : 0 < Y := by linarith
  rw [Real.rpow_def_of_pos hY0]
  have hlog : 1 / 2 ≤ Real.log Y := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    linarith
  have := Real.add_one_le_exp (Real.log Y * (2 * C))
  nlinarith

lemma ydat_facts {n f : ℕ} {rd g b : ℝ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hrd : 1 ≤ rd) (hg : 1 ≤ g)
    (hb : 2 ≤ b) : 2 ≤ Ydat n f rd g b ∧ (n:ℝ) ≤ Ydat n f rd g b ∧ (f:ℝ) ≤ Ydat n f rd g b ∧
      rd ≤ Ydat n f rd g b ∧ g ≤ Ydat n f rd g b ∧ b ≤ Ydat n f rd g b := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hb1 : (1:ℝ) ≤ b := by linarith
  unfold Ydat
  have hbY : b ≤ (n:ℝ) * f * rd * g * b := by
    calc b = 1 * 1 * 1 * 1 * b := by ring
      _ ≤ _ := by gcongr
  refine ⟨hb.trans hbY, ?_, ?_, ?_, ?_, hbY⟩
  · calc (n:ℝ) = n * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc (f:ℝ) = 1 * f * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc rd = 1 * 1 * rd * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc g = 1 * 1 * 1 * g * 1 := by ring
      _ ≤ _ := by gcongr

lemma b1_bound_le_power {n q f : ℕ} {b Y : ℝ} (hqn : q ≤ n) (hY : 2 ≤ Y) (hnY : (n:ℝ) ≤ Y) (hfY : (f:ℝ) ≤ Y)
    (hb0 : 0 ≤ b) (hbY : b ≤ Y) : b1 n q f b ≤ Y ^ 10 := by
  unfold b1 P0
  push_cast
  have hq' : (q:ℝ) ≤ Y := le_trans (by exact_mod_cast hqn) hnY
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have h1 : b ^ 2 ≤ Y ^ 2 := by gcongr
  have h2 : 2 * (8 * (q:ℝ) * (n:ℝ) ^ 2 * f) * n ≤ Y * (Y ^ 3 * Y * Y ^ 2 * Y) * Y := by
    have h8 : (8:ℝ) ≤ Y ^ 3 := by
      calc (8:ℝ) = 2 ^ 3 := by norm_num
        _ ≤ Y ^ 3 := by gcongr
    gcongr
  have h3 : Y ^ 2 ≤ Y ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h9 : 0 < Y ^ 9 := by positivity
  nlinarith


theorem deep_region_bound_height : DeepBoundY := by
  intro C hC
  refine ⟨2 * C + 2, by linarith, ?_⟩
  intro n q f Y hq hY
  have hY0 : 0 < Y := by linarith
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0, Real.rpow_def_of_pos hY0]
  apply Real.exp_le_exp.mpr
  have hlog : 1 / 2 ≤ Real.log Y := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    linarith
  have hm0 : 0 ≤ (n:ℝ) ^ 2 * f := by positivity
  have hE : (16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f
      + -((2 * C + 2) * q) * ((12 * n ^ 2 * f : ℕ) : ℝ) ≤ -2 * ((n:ℝ) ^ 2 * f) := by
    push_cast
    have : (16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f + -((2 * C + 2) * q) * (12 * (n:ℝ) ^ 2 * f)
        = (-(8 * q * C) + 2 * C + 16 - 24 * q) * ((n:ℝ) ^ 2 * f) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hm0
    nlinarith
  nlinarith

theorem deep_region_bound : DeepBound := by
  intro C hC
  obtain ⟨C₁, hC₁, H⟩ := deep_region_bound_height (2 * C + 18) (by linarith)
  refine ⟨C₁, hC₁, ?_⟩
  intro n q f rd g b hn hq hqn hf hrd hg hb
  obtain ⟨hY, hnY, hfY, hrdY, hgY, hbY⟩ := ydat_facts hn hf hrd hg hb
  have hqn' : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hqn
  have hb1 := b1_bound_le_power (f := f) hqn' hY hnY hfY (by linarith) hbY
  have H' := H n q f _ hq hY
  generalize Ydat n f rd g b = Y at *
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  refine le_trans ?_ H'
  have hb10 : 0 ≤ b1 n q f b := by unfold b1; positivity
  have hbr : C * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b1 n q f b ≤ Y ^ (2 * C + 18) := by
    have e : Y ^ (2 * C + 18) = Y ^ (2 * C) * Y ^ 4 * Y ^ 2 * Y * Y * Y ^ 10 := by
      rw [Real.rpow_add hY0]
      have : Y ^ (18:ℝ) = Y ^ 18 := by exact_mod_cast Real.rpow_natCast Y 18
      rw [this]; ring
    rw [e]
    have := le_rpow_two_mul hY (by linarith : 0 ≤ C)
    gcongr
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc Y ^ (C * (n:ℝ) ^ 2 * f) * (C * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
      ≤ Y ^ (C * (n:ℝ) ^ 2 * f) * (Y ^ (2 * C + 18)) ^ (16 * q * n ^ 2 * f) := by
        gcongr
    _ = Y ^ (C * (n:ℝ) ^ 2 * f + (2 * C + 18) * ((16 * q * n ^ 2 * f : ℕ) : ℝ)) := by
        rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hY1
        push_cast
        have hm0 : 0 ≤ (n:ℝ) ^ 2 * f := by positivity
        nlinarith


lemma log_ydat {n f : ℕ} {rd g b : ℝ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hrd : 1 ≤ rd) (hg : 1 ≤ g)
    (hb : 2 ≤ b) : Real.log (Ydat n f rd g b)
      = Real.log n + Real.log f + Real.log rd + Real.log g + Real.log b := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  unfold Ydat
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]

theorem threshold_far_region : ThreshFar := by
  intro C' c Cg hC' hc hCg
  refine ⟨C' * (Cg + 6) / c ^ 2, by positivity, ?_⟩
  intro n q f rd g b h hn hf hq hlf hb hrd hg hgb hh
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hqn : (q:ℝ)^2 ≤ n := by exact_mod_cast hq
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hs1 : 1 ≤ Real.sqrt (n:ℝ) := Real.one_le_sqrt.mpr hn'
  have hss : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = n := Real.mul_self_sqrt (by linarith)
  have hqs : (q:ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hqn
  have hlogn : Real.log n ≤ 2 * Real.sqrt n := by
    have h1 : Real.log n = 2 * Real.log (Real.sqrt n) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have h2 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt (n:ℝ) by linarith)
    linarith
  have hlb : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
  have hl2 := Real.log_two_gt_d9
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hlbr : Real.log (b * rd) = Real.log b + Real.log rd :=
    Real.log_mul (by positivity) (by positivity)
  have hlg : Real.log g ≤ Cg * Real.log b := by
    have := Real.log_le_log (by linarith) hgb
    rwa [Real.log_rpow (by linarith)] at this
  rw [hlbr] at hh
  have hY := log_ydat hn hf hrd hg hb
  set ℓ := Real.log b + Real.log rd with hℓ
  have hℓ0 : 0.69 ≤ ℓ := by linarith
  have hlY : Real.log (Ydat n f rd g b) ≤ 3 * Real.sqrt n + (Cg + 1) * ℓ := by
    rw [hY]
    have : Cg * Real.log b ≤ Cg * ℓ := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    linarith
  generalize Real.log (Ydat n f rd g b) = LY at *
  generalize Real.sqrt (n:ℝ) = s at *
  have k1 : (q:ℝ) * LY ≤ (Cg + 6) * (n * ℓ) := by
    calc (q:ℝ) * LY ≤ q * (3 * s + (Cg + 1) * ℓ) := by gcongr
      _ ≤ s * (3 * s + (Cg + 1) * ℓ) := by
          apply mul_le_mul_of_nonneg_right hqs
          have : 0 ≤ (Cg + 1) * ℓ := by positivity
          linarith
      _ = 3 * n + (Cg + 1) * (s * ℓ) := by rw [← hss]; ring
      _ ≤ 3 * n + (Cg + 1) * (n * ℓ) := by
          have : s ≤ n := by nlinarith
          gcongr
      _ ≤ _ := by nlinarith
  have e2 : epsN c n f ^ 2 = c ^ 2 / ((n:ℝ) ^ 16 * (f:ℝ) ^ 4) := by
    unfold epsN; rw [div_pow]; congr 1; ring
  have he0 : 0 ≤ epsN c n f ^ 2 := sq_nonneg _
  calc C' * (n:ℝ) ^ 2 * q * f * LY = C' * (n:ℝ) ^ 2 * f * (q * LY) := by ring
    _ ≤ C' * (n:ℝ) ^ 2 * f * ((Cg + 6) * (n * ℓ)) := by gcongr
    _ = (C' * (Cg + 6) / c ^ 2 * (n:ℝ) ^ 19 * (f:ℝ) ^ 5 * ℓ) * epsN c n f ^ 2 := by
        rw [e2]; field_simp
    _ ≤ h * epsN c n f ^ 2 := by gcongr

theorem far_region_negligible : FarNegligible := by
  intro C C₁ c m hC hC₁ hc
  refine ⟨16 * ((2 * C + C₁) * m + 2 + c), by positivity, ?_⟩
  intro n q f rd g b x hn hq hf hrd hg hb hx
  obtain ⟨hY, hnY, hfY, hrdY, hgY, hbY⟩ := ydat_facts hn hf hrd hg hb
  generalize Ydat n f rd g b = Y at *
  have hY0 : 0 < Y := by linarith
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 1 / 2 ≤ Real.log Y := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    linarith
  have hlogn : Real.log n ≤ Real.log Y := Real.log_le_log (by linarith) hnY
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have h1 : C / Y ^ (-(C₁ * q)) ≤ Real.exp (Real.log Y * (2 * C + C₁ * q)) := by
    rw [Real.rpow_neg hY0.le, div_inv_eq_mul, ← Real.rpow_def_of_pos hY0, Real.rpow_add hY0]
    have := le_rpow_two_mul hY (by linarith : 0 ≤ C)
    gcongr
  have h2 : 2 * (f:ℝ) ≤ Real.exp (Real.log Y * 2) := by
    rw [← Real.rpow_def_of_pos hY0, Real.rpow_two]
    nlinarith
  have h0 : 0 ≤ C / Y ^ (-(C₁ * q)) := by positivity
  calc (C / Y ^ (-(C₁ * q))) ^ (m * n ^ 2 * f) * (2 * f) * Real.exp (-(x / 16))
      ≤ (Real.exp (Real.log Y * (2 * C + C₁ * q))) ^ (m * n ^ 2 * f) * Real.exp (Real.log Y * 2)
          * Real.exp (-(x / 16)) := by gcongr
    _ = Real.exp (((m * n ^ 2 * f : ℕ) : ℝ) * (Real.log Y * (2 * C + C₁ * q)) + Real.log Y * 2
          + -(x / 16)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        push_cast
        generalize Real.log Y = ℓ at *
        generalize Real.log (n:ℝ) = ln at *
        set u := (n:ℝ) ^ 2 * q * f with hu
        have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
        have u1 : (n:ℝ) ^ 2 * f ≤ u := by
          rw [hu]
          calc (n:ℝ) ^ 2 * f = (n:ℝ) ^ 2 * 1 * f := by ring
            _ ≤ _ := by gcongr
        have u2 : (n:ℝ) * f ≤ (n:ℝ) ^ 2 * f := by
          have : (n:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
          gcongr
        have u3 : 1 ≤ (n:ℝ) * f := by nlinarith
        have hx' : ((2 * C + C₁) * m + 2 + c) * (u * ℓ) ≤ x / 16 := by
          have : 16 * ((2 * C + C₁) * m + 2 + c) * (n:ℝ) ^ 2 * q * f * ℓ
              = 16 * (((2 * C + C₁) * m + 2 + c) * (u * ℓ)) := by rw [hu]; ring
          linarith
        have t1 : (m:ℝ) * (n:ℝ) ^ 2 * f * (ℓ * (2 * C + C₁ * q)) ≤ (2 * C + C₁) * m * (u * ℓ) := by
          have e : (m:ℝ) * (n:ℝ) ^ 2 * f * (ℓ * (2 * C + C₁ * q))
              = m * ℓ * (2 * C * ((n:ℝ) ^ 2 * f) + C₁ * u) := by rw [hu]; ring
          rw [e]
          calc (m:ℝ) * ℓ * (2 * C * ((n:ℝ) ^ 2 * f) + C₁ * u) ≤ m * ℓ * (2 * C * u + C₁ * u) := by
                gcongr
            _ = _ := by ring
        have t2 : ℓ * 2 ≤ 2 * (u * ℓ) := by
          have : 1 ≤ u := by linarith
          nlinarith
        have t3 : c * n * f * ln ≤ c * (u * ℓ) := by
          calc c * n * f * ln = c * ((n * f) * ln) := by ring
            _ ≤ c * (u * ℓ) := by
              gcongr
              linarith
        nlinarith



noncomputable def sfac (k : ℕ) : ℝ := ∏ i ∈ range k, (i.factorial : ℝ)

lemma sfac_pos (k : ℕ) : 0 < sfac k := by
  unfold sfac; exact Finset.prod_pos fun l _ => by positivity







theorem fibre_count_alt : FibreCount := by
  classical
  intro α S r β π c hc h0 hr hstep
  have key : ∀ i, i ≤ r → ((S.image (π i)).card : ℝ) ≤ ∏ k ∈ range i, c k := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.prod_empty]
      have : (S.image (π 0)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
        exact h0 x hx y hy
      exact_mod_cast this
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hfib : ∀ b ∈ S.image (π i),
          (((S.filter (fun x => π i x = b)).image (π (i+1))).card : ℝ) ≤ c i := by
        intro b _
        obtain ⟨T, hTF, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
          (f := π (i+1)) (S.filter (fun x => π i x = b))
          ((S.filter (fun x => π i x = b)).image (π (i+1)))
          (by
            intro v hv
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
            exact ⟨x, hx, rfl⟩)
        rw [← himg, Finset.card_image_of_injOn hinj]
        apply hstep i (by omega) T
        · intro x hx; exact (Finset.mem_filter.mp (hTF hx)).1
        · intro y hy z hz
          rw [(Finset.mem_filter.mp (hTF hy)).2, (Finset.mem_filter.mp (hTF hz)).2]
        · intro y hy z hz hyz
          exact hinj hy hz hyz
      have hsub : S.image (π (i+1)) ⊆ (S.image (π i)).biUnion
          (fun b => (S.filter (fun x => π i x = b)).image (π (i+1))) := by
        intro v hv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_biUnion.mpr ⟨π i x, Finset.mem_image_of_mem _ hx,
          Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, rfl⟩)⟩
      calc ((S.image (π (i+1))).card : ℝ)
          ≤ (((S.image (π i)).biUnion
              (fun b => (S.filter (fun x => π i x = b)).image (π (i+1)))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ ∑ b ∈ S.image (π i), (((S.filter (fun x => π i x = b)).image (π (i+1))).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ b ∈ S.image (π i), c i := Finset.sum_le_sum hfib
        _ = (S.image (π i)).card * c i := by simp
        _ ≤ (∏ k ∈ range i, c k) * c i := by
            apply mul_le_mul_of_nonneg_right ih' (hc i)
        _ = _ := (Finset.prod_range_succ _ _).symm
  have := key r le_rfl
  rwa [Finset.card_image_of_injOn (fun x hx y hy h => hr x hx y hy h)] at this

def IsW (t : ℤ) : Prop := t = 0 ∨ ∃ k : ℕ, t = 4 ^ k ∨ t = -(4 ^ k)





theorem positive_type_bound : PosTypeBound := by
  classical
  intro G _ e he x
  have h1 : 0 ≤ e 1 := by
    have := he {1} (fun _ => 1)
    simpa using this
  have h1re : 0 ≤ (e 1).re := (Complex.le_def.mp h1).1
  have h1im : (e 1).im = 0 := ((Complex.le_def.mp h1).2).symm
  by_cases hx : x = 1
  · subst hx
    rw [← Complex.re_add_im (e 1), h1im]
    simp [abs_of_nonneg h1re]
  have hpair : ∀ t : ℂ, 0 ≤ e 1 + t * e x + star t * e x⁻¹ + star t * t * e 1 := by
    intro t
    have := he {1, x} (fun y => if y = 1 then 1 else t)
    rw [Finset.sum_pair (Ne.symm hx), Finset.sum_pair (Ne.symm hx), Finset.sum_pair (Ne.symm hx)] at this
    simp only [if_true, if_neg hx, inv_one, one_mul, mul_one, star_one, inv_mul_cancel] at this
    convert this using 1
    ring
  have ha := hpair 1
  have hb := hpair Complex.I
  rw [Complex.le_def] at ha hb
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.zero_re,
    Complex.zero_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, star_one,
    Complex.star_def, Complex.conj_I, Complex.neg_re, Complex.neg_im] at ha hb
  have him : (e x⁻¹).im = -(e x).im := by linarith [ha.2]
  have hre : (e x⁻¹).re = (e x).re := by linarith [hb.2]
  by_cases h0 : e x = 0
  · rw [h0, norm_zero]; exact h1re
  have hn : 0 < ‖e x‖ := norm_pos_iff.mpr h0
  have hc := hpair (-(star (e x)) / (‖e x‖ : ℂ))
  rw [Complex.le_def] at hc
  have hsq : (e x).re * (e x).re + (e x).im * (e x).im = ‖e x‖ * ‖e x‖ := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]; ring
  have hinv : e x⁻¹ = star (e x) := by
    apply Complex.ext <;> simp [hre, him]
  have hval : e 1 + (-(star (e x)) / (‖e x‖ : ℂ)) * e x
      + star (-(star (e x)) / (‖e x‖ : ℂ)) * e x⁻¹
      + star (-(star (e x)) / (‖e x‖ : ℂ)) * (-(star (e x)) / (‖e x‖ : ℂ)) * e 1
      = 2 * e 1 - 2 * (‖e x‖ : ℂ) := by
    have hne : (‖e x‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm : star (e x) * e x = (‖e x‖ : ℂ) * (‖e x‖ : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; ring
    rw [hinv]
    simp only [star_div₀, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    simp only [Complex.star_def] at hm
    field_simp
    linear_combination (-2 * (‖e x‖ : ℂ) + e 1) * hm
  rw [hval] at hc
  have := hc.1
  simp at this
  linarith


theorem kernel_bound_bis : KernelBound := by
  intro X ι _ μ _ _ F c hF horth y
  have hint : ∀ w w', Integrable (fun x => star (F w x) * F w' x) μ := by
    intro w w'
    exact (hF w).star.integrable_mul (hF w')
  have e : ∀ x, ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ)
      = ∑ w, ∑ w', star (c w) * c w' * (star (F w x) * F w' x) := by
    intro x
    have : ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ) = star (∑ w, c w * F w x) * ∑ w, c w * F w x := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    rw [this, star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro w _
    apply Finset.sum_congr rfl; intro w' _
    rw [star_mul']; ring
  have h1 : (∫ x, ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((∑ w, ‖c w‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [e]
    rw [integral_finsetSum _ (fun w _ => integrable_finsetSum _ (fun w' _ => (hint w w').const_mul _))]
    push_cast
    apply Finset.sum_congr rfl; intro w _
    rw [integral_finsetSum _ (fun w' _ => (hint w w').const_mul _)]
    simp_rw [integral_const_mul, horth]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Complex.star_def, Complex.conj_mul']
  rw [integral_complex_ofReal] at h1
  have h2 : (∫ x, ‖∑ w, c w * F w x‖ ^ 2 ∂μ) = ∑ w, ‖c w‖ ^ 2 := by exact_mod_cast h1
  rw [h2]
  calc ‖∑ w, c w * F w y‖ ^ 2 ≤ (∑ w, ‖c w‖ * ‖F w y‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

noncomputable def farW (h ε : ℝ) : ℕ → ℝ
  | 0 => 1
  | (k+1) => Real.exp (-(h / 8 * (ε * (2 ^ k * ε))))

noncomputable def farA (B h ε : ℝ) (i : ℕ) : ℝ := Real.exp (B * (2 ^ i * ε)) * farW h ε i

lemma farW_nonneg (h ε : ℝ) (i : ℕ) : 0 ≤ farW h ε i := by
  cases i with
  | zero => exact zero_le_one
  | succ k => exact (Real.exp_pos _).le

lemma farA_nonneg (B h ε : ℝ) (i : ℕ) : 0 ≤ farA B h ε i :=
  mul_nonneg (Real.exp_pos _).le (farW_nonneg _ _ _)

lemma farA_zero_le {B h ε : ℝ} (hBε : B * ε ≤ 1) : farA B h ε 0 ≤ 3 := by
  unfold farA farW
  rw [mul_one, pow_zero, one_mul]
  have h1 : Real.exp (B * ε) ≤ Real.exp 1 := Real.exp_le_exp.mpr hBε
  have := Real.exp_one_lt_d9
  linarith

lemma exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have := Real.add_one_le_exp (1:ℝ); linarith

lemma farA_succ_le {B h ε : ℝ} (hε : 0 < ε) (h32 : 32 * B ≤ h * ε) (h16 : 16 ≤ h * ε ^ 2) (k : ℕ) :
    farA B h ε (k+1) ≤ Real.exp (-(h * ε ^ 2 / 16)) * (1 / 2) ^ k := by
  have h1 : Real.exp (-(h * ε ^ 2 / 16)) * Real.exp (-1) ^ k
      ≤ Real.exp (-(h * ε ^ 2 / 16)) * (1 / 2) ^ k := by
    have := exp_neg_one_le_half
    have h0 := (Real.exp_pos (-1)).le
    gcongr
  refine le_trans ?_ h1
  unfold farA farW
  rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hP : (k:ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self (n := k)
  have hB : 2 * (B * ε) ≤ h * ε ^ 2 / 16 := by nlinarith
  have e : B * (2 ^ (k+1) * ε) + -(h / 8 * (ε * (2 ^ k * ε)))
      = 2 ^ k * (2 * (B * ε) - 2 * (h * ε ^ 2 / 16)) := by ring
  rw [e]
  have hT : 1 ≤ h * ε ^ 2 / 16 := by linarith
  generalize h * ε ^ 2 / 16 = T at *
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have h2 : (2:ℝ) ^ k * (2 * (B * ε) - 2 * T) ≤ 2 ^ k * (-T) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : ((k:ℝ) + 1) * T ≤ 2 ^ k * T := by gcongr
  nlinarith

lemma farA_sum_succ {B h ε : ℝ} (hε : 0 < ε) (h32 : 32 * B ≤ h * ε) (h16 : 16 ≤ h * ε ^ 2) (m : ℕ) :
    ∑ k ∈ range m, farA B h ε (k+1) ≤ 2 * Real.exp (-(h * ε ^ 2 / 16)) := by
  calc ∑ k ∈ range m, farA B h ε (k+1)
      ≤ ∑ k ∈ range m, Real.exp (-(h * ε ^ 2 / 16)) * (1 / 2) ^ k :=
        Finset.sum_le_sum fun k _ => farA_succ_le hε h32 h16 k
    _ = Real.exp (-(h * ε ^ 2 / 16)) * ∑ k ∈ range m, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(h * ε ^ 2 / 16)) * 2 := by
        gcongr
        exact sum_geometric_two_le m
    _ = _ := by ring

open Classical in
theorem far_region_sum : FarSum := by
  intro ι Γ _ _ S d A B h ε q hq hA hB hε hεq hBε h32 h16 hd0 hdε hcount
  have hε2 : 0 < ε ^ 2 := by positivity
  have hh : 0 ≤ h := by
    by_contra hneg
    push Not at hneg
    have : h * ε ^ 2 < 0 := mul_neg_of_neg_of_pos hneg hε2
    linarith
  have hex : ∀ x : ℝ, ∃ i : ℕ, x ≤ 2 ^ i * ε := by
    intro x
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / ε) (one_lt_two : (1:ℝ) < 2)
    exact ⟨n, by rw [div_lt_iff₀ hε] at hn; exact hn.le⟩
  obtain ⟨idx, hidx1, hidx2⟩ : ∃ idx : ℝ → ℕ, (∀ x, x ≤ 2 ^ idx x * ε) ∧
      (∀ x k, idx x = k + 1 → 2 ^ k * ε < x) := by
    refine ⟨fun x => Nat.find (hex x), fun x => Nat.find_spec (hex x), ?_⟩
    intro x k hk
    have := Nat.find_min (hex x) (m := k) (by simp only at hk; omega)
    exact not_le.mp this
  have hidx0 : ∀ x, ε < x → 1 ≤ idx x := by
    intro x hx
    by_contra hc
    have h0 : idx x = 0 := by omega
    have := hidx1 x
    rw [h0] at this
    simp at this
    linarith
  have hW : ∀ x, 0 ≤ x → Real.exp (-(decExp h q x)) ≤ farW h ε (idx x) := by
    intro x hx
    rcases hk : idx x with _ | k
    · show _ ≤ (1:ℝ)
      rw [Real.exp_le_one_iff]
      have : 0 ≤ decExp h q x :=
        mul_nonneg (by linarith) (le_min (sq_nonneg _) (div_nonneg hx (Real.sqrt_nonneg _)))
      linarith
    · have h1 := hidx2 x k hk
      show _ ≤ Real.exp (-(h / 8 * (ε * (2 ^ k * ε))))
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      have hεx : ε ≤ x := by
        have : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      have h2 := minimum_linear_form q ε x hq hε hεq hεx
      unfold decExp
      calc h / 8 * (ε * (2 ^ k * ε)) ≤ h / 8 * (ε * x) := by gcongr
        _ ≤ _ := by gcongr
  have hw0 : ∀ γ, 0 ≤ ∏ v, Real.exp (-(decExp h q (d γ v))) :=
    fun γ => Finset.prod_nonneg fun v _ => (Real.exp_pos _).le
  have hwW : ∀ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤ ∏ v, farW h ε (idx (d γ v)) :=
    fun γ hγ => Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le) (fun v _ => hW _ (hd0 γ hγ v))
  generalize hwdef : (fun γ => ∏ v, Real.exp (-(decExp h q (d γ v)))) = w at *
  have hw0' : ∀ γ, 0 ≤ w γ := fun γ => by rw [← hwdef]; exact hw0 γ
  have hwW' : ∀ γ ∈ S, w γ ≤ ∏ v, farW h ε (idx (d γ v)) := fun γ hγ => by
    rw [← hwdef]; exact hwW γ hγ
  show ∑ γ ∈ S, w γ ≤ _
  set m := S.sup (fun γ => univ.sup (fun v => idx (d γ v))) with hmdef
  have hm : ∀ γ ∈ S, ∀ v, idx (d γ v) ≤ m := by
    intro γ hγ v
    calc idx (d γ v) ≤ univ.sup (fun v => idx (d γ v)) :=
          Finset.le_sup (f := fun v => idx (d γ v)) (Finset.mem_univ v)
      _ ≤ m := Finset.le_sup (f := fun γ => univ.sup (fun v => idx (d γ v))) hγ
  have hT1 : Real.exp (-(h * ε ^ 2 / 16)) ≤ 1 / 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_one_le_half
    linarith
  have hv0 : ∀ v₀, ∑ γ ∈ S.filter (fun γ => ε < d γ v₀), w γ
      ≤ A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2)) := by
    intro v₀
    set t : ι → Finset ℕ := fun v => if v = v₀ then Ico 1 (m+1) else range (m+1) with ht
    have hmaps : ∀ γ ∈ S.filter (fun γ => ε < d γ v₀),
        (fun v => idx (d γ v)) ∈ Fintype.piFinset t := by
      intro γ hγ
      have hγ' := Finset.mem_filter.mp hγ
      rw [Fintype.mem_piFinset]
      intro v
      simp only [ht]
      split_ifs with hv
      · subst hv
        exact Finset.mem_Ico.mpr ⟨hidx0 _ hγ'.2, Nat.lt_succ_of_le (hm γ hγ'.1 v)⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hm γ hγ'.1 v))
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ I ∈ Fintype.piFinset t,
          ∑ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter (fun γ => (fun v => idx (d γ v)) = I), w γ
        ≤ ∑ I ∈ Fintype.piFinset t, A * ∏ v, farA B h ε (I v) := by
          apply Finset.sum_le_sum
          intro I _
          have hmem : ∀ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter
              (fun γ => (fun v => idx (d γ v)) = I), γ ∈ S ∧ ∀ v, idx (d γ v) = I v := by
            intro γ hγ
            have h1 := Finset.mem_filter.mp hγ
            exact ⟨(Finset.mem_filter.mp h1.1).1, fun v => congrFun h1.2 v⟩
          have hPW : 0 ≤ ∏ v, farW h ε (I v) := Finset.prod_nonneg fun v _ => farW_nonneg _ _ _
          calc ∑ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter
                (fun γ => (fun v => idx (d γ v)) = I), w γ
              ≤ ∑ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter
                (fun γ => (fun v => idx (d γ v)) = I), ∏ v, farW h ε (I v) := by
                apply Finset.sum_le_sum
                intro γ hγ
                obtain ⟨h1, h2⟩ := hmem γ hγ
                have := hwW' γ h1
                simp only [h2] at this
                exact this
            _ = (((S.filter (fun γ => ε < d γ v₀)).filter
                (fun γ => (fun v => idx (d γ v)) = I)).card : ℝ) * ∏ v, farW h ε (I v) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (A * Real.exp (B * ∑ v, 2 ^ (I v) * ε)) * ∏ v, farW h ε (I v) := by
                apply mul_le_mul_of_nonneg_right _ hPW
                refine le_trans ?_ (hcount (fun v => 2 ^ (I v) * ε) (fun v => by positivity))
                have hsub : (S.filter (fun γ => ε < d γ v₀)).filter
                    (fun γ => (fun v => idx (d γ v)) = I) ⊆
                    S.filter (fun γ => ∀ v, d γ v ≤ 2 ^ (I v) * ε) := by
                  intro γ hγ
                  obtain ⟨h1, h2⟩ := hmem γ hγ
                  refine Finset.mem_filter.mpr ⟨h1, fun v => ?_⟩
                  rw [← h2 v]; exact hidx1 _
                exact_mod_cast Finset.card_le_card hsub
            _ = A * ∏ v, farA B h ε (I v) := by
                unfold farA
                rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]; ring
      _ = A * ∏ v, ∑ i ∈ t v, farA B h ε i := by
          rw [← Finset.mul_sum, Finset.prod_univ_sum]
      _ ≤ A * ∏ v, (4 * if v = v₀ then Real.exp (-(h * ε ^ 2 / 16)) / 2 else 1) := by
          apply mul_le_mul_of_nonneg_left _ hA
          apply Finset.prod_le_prod
          · intro v _; exact Finset.sum_nonneg fun i _ => farA_nonneg _ _ _ _
          · intro v _
            have hs := farA_sum_succ (B := B) hε h32 h16 m
            simp only [ht]
            split_ifs with hv
            · rw [Finset.sum_Ico_eq_sum_range]
              simp only [Nat.add_sub_cancel, add_comm 1]
              linarith
            · rw [Finset.sum_range_succ']
              have := farA_zero_le (h := h) hBε
              linarith
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_eq']
          simp
  calc ∑ γ ∈ S, w γ ≤ ∑ γ ∈ S, ∑ v₀, (if ε < d γ v₀ then w γ else 0) := by
        apply Finset.sum_le_sum
        intro γ hγ
        obtain ⟨v, hv⟩ := hdε γ hγ
        calc w γ = (if ε < d γ v then w γ else 0) := by rw [if_pos hv]
          _ ≤ _ := Finset.single_le_sum (f := fun v₀ => if ε < d γ v₀ then w γ else 0)
              (fun v _ => by
                show 0 ≤ if ε < d γ v then w γ else 0
                split_ifs
                · exact hw0' γ
                · exact le_rfl) (Finset.mem_univ v)
    _ = ∑ v₀, ∑ γ ∈ S, (if ε < d γ v₀ then w γ else 0) := Finset.sum_comm
    _ = ∑ v₀, ∑ γ ∈ S.filter (fun γ => ε < d γ v₀), w γ := by simp_rw [Finset.sum_filter]
    _ ≤ ∑ _v₀ : ι, A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2)) :=
        Finset.sum_le_sum fun v₀ _ => hv0 v₀
    _ = Fintype.card ι * (A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ _ := by
        have h0 : 0 ≤ A * 4 ^ Fintype.card ι * Fintype.card ι * Real.exp (-(h * ε ^ 2 / 16)) := by
          positivity
        nlinarith

end Formalism.HermitianLatticeCounting.P
