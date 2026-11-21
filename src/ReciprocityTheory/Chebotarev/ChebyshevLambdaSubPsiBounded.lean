import ReciprocityTheory.Chebotarev.CasimirPowerSurjectiveSymmetric
import ReciprocityTheory.Chebotarev.EulerSum
import ReciprocityTheory.Chebotarev.EulerLim

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem norm_neg_log_one_sub_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
  have h1 : ‖-z‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le h1
  rw [norm_neg] at h
  have e : -Complex.log (1 - z) - z = -(Complex.log (1 + -z) - -z) := by ring_nf
  rw [e, norm_neg]
  refine h.trans ?_
  have h0 : 0 ≤ ‖z‖ := norm_nonneg _
  have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖z‖ ^ 2 := by ring

theorem psum_term_norm_le {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (q : Prm E) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  have hN : (0 : ℕ) < Nrm q := by have := two_le_Nrm q; omega
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN]
  simp only [Complex.neg_re, Complex.ofReal_re]
  have := DirichletCharacter.norm_le_one χ ((Nrm q : ℕ) : ZMod l)
  have hp : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
  nlinarith

theorem Nrm_rpow_neg_le_inv {E : Type} [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) (q : Prm E) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := by
  have h2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem casimirPower_surjective_symmetric' : CasimirPowerSurjectiveSymmetric := by
  intro E _ _ l _ χ
  refine ⟨∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)), fun s hs => ?_⟩
  set z : Prm E → ℂ := fun q => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)) with hzdef
  have hzb : ∀ q, ‖z q‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := fun q => psum_term_norm_le χ s q
  have hzs : Summable z := Summable.of_norm_bounded (summable_prm_rpow E hs) hzb
  have hls : Summable (fun q => -Complex.log (1 - z q)) := hzs.clog_one_sub.neg
  have hsq : ∀ q, ‖-Complex.log (1 - z q) - z q‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro q
    have h2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
    have hz1 : ‖z q‖ ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := (hzb q).trans (Nrm_rpow_neg_le_inv hs q)
    have hz2 : ‖z q‖ ≤ 1 / 2 := hz1.trans (by rw [one_div]; exact inv_anti₀ (by norm_num) h2)
    refine (norm_neg_log_one_sub_sub_le hz2).trans ?_
    rw [Real.rpow_neg (by linarith), Real.rpow_two, ← inv_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hz1 2
  have e : abelian₂ E χ s - Psum E χ s = ∑' q, (-Complex.log (1 - z q) - z q) := by
    unfold abelian₂ Psum
    exact (hls.tsum_sub hzs).symm
  rw [e]
  exact tsum_of_norm_bounded (summable_prm_rpow E (by norm_num : (1 : ℝ) < 2)).hasSum hsq

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem norm_chiNrm_cpow_le {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (q : Prm E) (s : ℝ) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  have hN : 0 < Nrm q := lt_of_lt_of_le (by norm_num) (two_le_Nrm q)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN]
  have h1 := χ.norm_le_one ((Nrm q : ℕ) : ZMod l)
  have h2 : (0:ℝ) ≤ ((Nrm q : ℕ) : ℝ) ^ (-(s:ℂ)).re := Real.rpow_nonneg (by positivity) _
  simp only [Complex.neg_re, Complex.ofReal_re] at h2 ⊢
  nlinarith [norm_nonneg (χ ((Nrm q : ℕ) : ZMod l))]

theorem nrm_rpow_neg_le_half {E : Type} [Field E] [NumberField E] (q : Prm E) {s : ℝ} (hs : 1 ≤ s) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2:ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
  calc ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (((Nrm q : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2

theorem smoothMap_seminorm_bound' : SmoothMapSeminormBound := by
  intro E _ _ l _ χ s0 hs0
  have hs0' : (1:ℝ) < s0 := hs0
  set a : ℝ := (1 + s0) / 2 with ha_def
  have ha1 : 1 < a := by rw [ha_def]; linarith
  have has0 : a < s0 := by rw [ha_def]; linarith
  have hcont : ContinuousOn (fun s : ℝ => abelian₂ E χ s) (Set.Ioi a) := by
    unfold abelian₂
    refine continuousOn_tsum (u := fun q : Prm E => (3 / 2) * ((Nrm q : ℕ) : ℝ) ^ (-a)) ?_
      ((summable_prm_rpow E ha1).mul_left _) ?_
    · intro q
      have hN : (Nrm q : ℕ) ≠ 0 := by have := two_le_Nrm q; omega
      have hc : Continuous (fun s : ℝ => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))) :=
        continuous_const.mul (Continuous.const_cpow (Complex.continuous_ofReal.neg)
          (Or.inl (by exact_mod_cast hN)))
      refine ContinuousOn.neg (ContinuousOn.clog (continuous_const.sub hc).continuousOn ?_)
      intro s hs
      have hs' : a < s := hs
      have hz := (norm_chiNrm_cpow_le χ q s).trans (nrm_rpow_neg_le_half q (by linarith))
      rw [Complex.mem_slitPlane_iff]
      left
      have hre := Complex.abs_re_le_norm (χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))
      rw [Complex.sub_re, Complex.one_re]
      have := (abs_le.mp (hre.trans hz)).2
      linarith
    · intro q s hs
      have hs' : a < s := hs
      have hz1 := norm_chiNrm_cpow_le χ q s
      have hz := hz1.trans (nrm_rpow_neg_le_half q (by linarith))
      rw [norm_neg, sub_eq_add_neg]
      have hz' : ‖-(χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))‖ ≤ 1 / 2 := by
        rw [norm_neg]; exact hz
      refine (Complex.norm_log_one_add_half_le_self hz').trans ?_
      rw [norm_neg]
      have hmono : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-a) := by
        have h2 : (2:ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      nlinarith
  exact (hcont.continuousAt (Ioi_mem_nhds has0)).continuousWithinAt

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem pa_cpow_eq (n : ℕ) (s : ℝ) :
    ((n : ℂ) ^ (-(s : ℂ))) = (((n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

theorem pa_one_le_absNorm {E : Type} [Field E] [NumberField E] (a : NZIdeal E) :
    (1 : ℝ) ≤ ((Ideal.absNorm a.1 : ℕ) : ℝ) := by
  have h : Ideal.absNorm a.1 ≠ 0 := by
    intro h0
    exact a.2 (Ideal.absNorm_eq_zero_iff.mp h0)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

theorem pa_rpow_lt_one {E : Type} [Field E] [NumberField E] (q : Prm E) {s : ℝ} (hs : 0 < s) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) < 1 := by
  have h := two_le_Nrm q
  have h1 : (1 : ℝ) < ((Nrm q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < Nrm q)
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

theorem real_euler (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Real.exp (∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) =
      ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by
  have hs0 : (0 : ℝ) < s := by linarith
  set f : Ideal (𝓞 E) → ℂ := fun a => ((Ideal.absNorm a : ℕ) : ℂ) ^ (-(s : ℂ)) with hfdef
  have hf1 : f 1 = 1 := by simp [hfdef]
  have hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b := by
    intro a b
    simp only [hfdef, map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _
  have hnorm : ∀ a : Ideal (𝓞 E), ‖f a‖ = ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s) := by
    intro a
    simp only [hfdef]
    rw [pa_cpow_eq, Complex.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hsum : Summable (fun a : NZIdeal E => ‖f a.1‖) := by
    simp only [hnorm]
    exact summable_absNorm_rpow E hs
  have hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1 := by
    intro q
    rw [hnorm]
    exact pa_rpow_lt_one q hs0
  have h := euler_exp_log f hf1 hmul hsum hlt
  apply Complex.ofReal_injective
  rw [Complex.ofReal_exp, Complex.ofReal_tsum, Complex.ofReal_tsum]
  have e1 : (∑' q : Prm E, (((-Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) : ℝ) : ℂ)) =
      ∑' q : Prm E, -Complex.log (1 - f q.asIdeal) := by
    refine tsum_congr fun q => ?_
    have hx := pa_rpow_lt_one q hs0
    rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub, Complex.ofReal_one,
      ← pa_cpow_eq]
    rfl
  have e2 : (∑' a : NZIdeal E, ((((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) = ∑' a : NZIdeal E, f a.1 := by
    refine tsum_congr fun a => ?_
    rw [← pa_cpow_eq]
  rw [e1, e2]
  exact h

theorem pa_log_bdd {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |-Real.log (1 - x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |x| < 1 := by
    rw [abs_of_nonneg hx0]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  norm_num at h
  rw [abs_of_nonneg hx0] at h
  rw [show -Real.log (1 - x) - x = -(x + Real.log (1 - x)) by ring, abs_neg]
  calc |x + Real.log (1 - x)| ≤ x ^ 2 / (1 - x) := h
    _ ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]

theorem pa_A_sub_PE (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    |(∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) - PE E s| ≤
      2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hP := summable_prm_rpow E hs
  have h2 := summable_prm_rpow E (by norm_num : (1 : ℝ) < 2)
  have hb : ∀ q : Prm E, ‖-Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s)) - ((Nrm q : ℕ) : ℝ) ^ (-s)‖ ≤
      2 * ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro q
    have hN2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
    have hN0 : (0 : ℝ) < ((Nrm q : ℕ) : ℝ) := by linarith
    have hx0 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg hN0.le _
    have hxh : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
      calc ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = (((Nrm q : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hN2
    rw [Real.norm_eq_abs]
    refine (pa_log_bdd hx0 hxh).trans ?_
    have : (((Nrm q : ℕ) : ℝ) ^ (-s)) ^ 2 ≤ ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
      rw [sq, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    linarith
  have hg : Summable (fun q : Prm E => -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s)) - ((Nrm q : ℕ) : ℝ) ^ (-s)) :=
    Summable.of_norm_bounded (h2.mul_left 2) hb
  have hA : Summable (fun q : Prm E => -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) :=
    (hg.add hP).congr (fun q => by ring)
  unfold PE
  rw [← hA.tsum_sub hP, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded ((h2.hasSum).mul_left 2) hb

theorem pa_Z_ge_one (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    1 ≤ ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by
  have h := (summable_absNorm_rpow E hs).le_tsum (⟨⊤, top_ne_bot⟩ : NZIdeal E)
    (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  simpa [Ideal.absNorm_top] using h

theorem pa_Z_anti (E : Type) [Field E] [NumberField E] {s t : ℝ} (ht : 1 < t) (hts : t ≤ s) :
    ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ≤
      ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-t) :=
  Summable.tsum_le_tsum (fun a => Real.rpow_le_rpow_of_exponent_le (pa_one_le_absNorm a) (by linarith))
    (summable_absNorm_rpow E (lt_of_lt_of_le ht hts)) (summable_absNorm_rpow E ht)

theorem pa_Z_lim (E : Type) [Field E] [NumberField E] :
    Tendsto (fun s : ℝ => (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s))
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue E)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT E)
  simp only [Complex.ofReal_re] at h
  refine h.congr' ?_
  refine eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => ?_
  simp only [Function.comp_apply]
  rw [dedekindZeta_eq_tsum E hs]
  have e : (∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) =
      ((∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun a => pa_cpow_eq _ _
  rw [e, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem pa_g_bdd (E : Type) [Field E] [NumberField E] :
    ∃ m M : ℝ, 0 < m ∧ ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      m ≤ (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ∧
      (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ≤ M := by
  set r := dedekindZeta_residue E
  have hr : 0 < r := dedekindZeta_residue_pos E
  have hmem := pa_Z_lim E (Icc_mem_nhds (by linarith : r / 2 < r) (by linarith : r < 2 * r))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (by norm_num : (1 : ℝ) < 2)).mp hmem
  have hu1 : 1 < u := hu
  set t := min ((1 + u) / 2) 2 with htdef
  have ht1 : 1 < t := lt_min (by linarith) (by norm_num)
  have htu : t < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : t ≤ 2 := min_le_right _ _
  set Zt := ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-t)
  refine ⟨min (r / 2) (t - 1), max (2 * r) Zt, lt_min (by linarith) (by linarith), fun s hs => ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
  have hZ1 := pa_Z_ge_one E hs1
  rcases le_total s t with hst | hst
  · have hin := hsub ⟨hs1, lt_of_le_of_lt hst htu⟩
    obtain ⟨h1, h2⟩ := hin
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩
  · have hZ := pa_Z_anti E ht1 hst
    constructor
    · refine (min_le_right _ _).trans ?_
      nlinarith
    · refine le_trans ?_ (le_max_right _ _)
      have hZ0 : 0 ≤ ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by linarith
      nlinarith

theorem pe_log_bdd : faceMap_castSucc_comp_eq_succ := by
  intro E _ _
  obtain ⟨m, M, hm, hbd⟩ := pa_g_bdd E
  refine ⟨2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) + (|Real.log m| + |Real.log M|), fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hbd s hs
  have hs1 : 1 < s := hs.1
  have hAP := pa_A_sub_PE E hs1
  have hZ := pa_Z_ge_one E hs1
  have he := real_euler E hs1
  set A := ∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))
  set Z := ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s)
  have hAZ : A = Real.log Z := by rw [← he, Real.log_exp]
  have hg0 : 0 < (s - 1) * Z := lt_of_lt_of_le hm h1
  have hlog : A - Real.log (1 / (s - 1)) = Real.log ((s - 1) * Z) := by
    rw [hAZ, one_div, Real.log_inv, Real.log_mul (by linarith) (by linarith)]
    ring
  have hl1 : Real.log m ≤ Real.log ((s - 1) * Z) := Real.log_le_log hm h1
  have hl2 : Real.log ((s - 1) * Z) ≤ Real.log M := Real.log_le_log hg0 h2
  have hb : |Real.log ((s - 1) * Z)| ≤ |Real.log m| + |Real.log M| :=
    abs_le.mpr ⟨by linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)],
      by linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]⟩
  have e : PE E s - Real.log (1 / (s - 1)) = -(A - PE E s) + (A - Real.log (1 / (s - 1))) := by ring
  rw [e, hlog]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  linarith

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem ehold_norm_cpow (n : ℕ) {s : ℝ} (hs : 1 < s) : ‖((n : ℂ) ^ (-(s : ℂ)))‖ = (n : ℝ) ^ (-s) := by
  rw [Complex.norm_natCast_cpow_of_re_ne_zero n (by simp; linarith)]
  simp

theorem ehold_summable {E : Type} [Field E] [NumberField E] (f : NZIdeal E → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun a : NZIdeal E => ‖f a * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))‖) := by
  refine (summable_absNorm_rpow E hs).of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_)
  rw [norm_mul, ehold_norm_cpow _ hs]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hf a)

theorem chebyshev_first_estimate : E1 := by
  refine ⟨fun E _ _ f hf s hs => (ehold_summable f hf hs).of_norm, fun E _ _ s hs => dedekindZeta_eq_tsum E hs,
    fun E _ _ s hs => summable_prm_rpow E hs⟩

theorem chebyshev_second_estimate : E2 := by
  intro E _ _ l _ χ s hs
  have key := euler_exp_log (E := E)
    (fun a => χ ((Ideal.absNorm a : ℕ) : ZMod l) * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-(s : ℂ)))
    (by simp) (fun a b => by
      simp only [map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]; ring)
    (ehold_summable (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l)) (fun a => DirichletCharacter.norm_le_one χ _) hs)
    (fun q => by
      rw [norm_mul, ehold_norm_cpow _ hs]
      have h2 : (2 : ℝ) ≤ ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
      have h3 : ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) ^ (-s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
      calc _ ≤ 1 * ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) ^ (-s) :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (Real.rpow_nonneg (by positivity) _)
        _ < 1 := by rw [one_mul]; exact h3)
  exact key

theorem affine_proper_base_change : E1 := chebyshev_first_estimate

theorem proper_base_change : E2 := chebyshev_second_estimate

theorem casimirPower_surjective_symmetric : CasimirPowerSurjectiveSymmetric := casimirPower_surjective_symmetric'

theorem chebyshev_log_bounded : faceMap_castSucc_comp_eq_succ := pe_log_bdd

theorem smoothMap_seminorm_bound : SmoothMapSeminormBound := smoothMap_seminorm_bound'

end ReciprocityTheory.Cheb
end
