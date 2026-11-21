import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.RightHalfWith

section
noncomputable section

namespace PI.ZW

open DirichletCharacter

lemma finsum_mem_le_of_subset' {s t : Set ℂ} (g : ℂ → ℝ) (hg : ∀ x, 0 ≤ g x) (ht : t.Finite)
    (hst : s ⊆ t) : ∑ᶠ x ∈ s, g x ≤ ∑ᶠ x ∈ t, g x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (ht.subset hst), finsum_mem_eq_finite_toFinset_sum _ ht]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.mpr hst) fun x _ _ => hg x

lemma finsum_mem_le_finsum_mem' {s : Set ℂ} (f g : ℂ → ℝ) (hs : s.Finite) (h : ∀ x ∈ s, f x ≤ g x) :
    ∑ᶠ x ∈ s, f x ≤ ∑ᶠ x ∈ s, g x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  exact Finset.sum_le_sum fun x hx => h x (hs.mem_toFinset.mp hx)

lemma ne_one_or_of_isPrimitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ ≠ 1 ∨ N = 1 := by
  by_cases h : χ = 1
  · right
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hχ
    exact hχ.symm
  · exact Or.inl h

lemma log_mul_abs_add_two_nonneg (N : ℕ) [NeZero N] (t : ℝ) : 0 ≤ Real.log (N * (|t| + 2)) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  apply Real.log_nonneg
  nlinarith [abs_nonneg t]

theorem zerosWindowWith_of (C : ℝ) (hR : RightHalfWith C) (hT : Transfer) :
    PI.ZerosWindowWith (2 * C) := by
  intro N _ χ hχ t
  have hχ' : χ ≠ 1 ∨ N = 1 := ne_one_or_of_isPrimitive hχ
  have hχi : χ⁻¹ ≠ 1 ∨ N = 1 := hχ'.imp (fun h h' => h (inv_eq_one.mp h')) id
  obtain ⟨hA, hAs⟩ := hR N χ hχ' t
  obtain ⟨hB, hBs⟩ := hR N χ⁻¹ hχi (-t)
  rw [abs_neg] at hBs
  have hZrA : ZerosNear χ t ∩ {ρ | 1 / 2 ≤ ρ.re} ⊆ RightNear χ t :=
    fun ρ ⟨⟨_, h1, h2, h3⟩, h4⟩ => ⟨h4, h1, h2, h3⟩
  have hZl : ∀ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}, 1 - ρ ∈ RightNear χ⁻¹ (-t) := by
    rintro ρ ⟨⟨h0, h1, h2, h3⟩, h4⟩
    simp only [Set.mem_setOf_eq] at h4
    refine ⟨by simp; linarith, by simp; linarith, ?_, (hT N χ hχ ρ h0 h1 h3).1⟩
    simp only [Complex.sub_im, Complex.one_im, zero_sub]
    rw [show -ρ.im - -t = -(ρ.im - t) by ring, abs_neg]
    exact h2
  have hsplit : ZerosNear χ t = (ZerosNear χ t ∩ {ρ | 1 / 2 ≤ ρ.re}) ∪ (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}) :=
    Set.ext fun ρ => ⟨fun h => (le_or_gt (1 / 2) ρ.re).imp (fun h' => ⟨h, h'⟩) (fun h' => ⟨h, h'⟩),
      fun h => h.elim (·.1) (·.1)⟩
  have hBimg : ((fun σ : ℂ => 1 - σ) '' RightNear χ⁻¹ (-t)).Finite := hB.image _
  have hZfin : (ZerosNear χ t).Finite := by
    rw [hsplit]
    refine (hA.subset hZrA).union (hBimg.subset fun ρ hρ => ⟨1 - ρ, hZl ρ hρ, by ring⟩)
  refine ⟨hZfin, ?_⟩
  have hdisj : Disjoint (ZerosNear χ t ∩ {ρ | 1 / 2 ≤ ρ.re}) (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}) :=
    Set.disjoint_left.mpr fun ρ h1 h2 => absurd (show (1 / 2 : ℝ) ≤ ρ.re from h1.2) (not_le.mpr (show ρ.re < 1 / 2 from h2.2))
  have hfl : (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}).Finite := hZfin.subset Set.inter_subset_left
  rw [hsplit, finsum_mem_union hdisj (hZfin.subset Set.inter_subset_left) hfl]
  have e1 := finsum_mem_le_of_subset' (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
    (fun _ => Nat.cast_nonneg _) hA hZrA
  have e2 : ∑ᶠ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      ∑ᶠ σ ∈ RightNear χ⁻¹ (-t), (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ) := by
    calc ∑ᶠ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
        ≤ ∑ᶠ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) : ℝ) :=
          finsum_mem_le_finsum_mem' _ _ hfl fun ρ hρ => by
            exact_mod_cast (hT N χ hχ ρ hρ.1.1 hρ.1.2.1 hρ.1.2.2.2).2
      _ = ∑ᶠ σ ∈ (fun σ : ℂ => 1 - σ) '' (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}), (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ) :=
          (finsum_mem_image (f := fun σ => (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ))
            (g := fun σ : ℂ => 1 - σ) (s := ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2})
            (fun a _ b _ h => by simpa using h)).symm
      _ ≤ ∑ᶠ σ ∈ RightNear χ⁻¹ (-t), (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ) :=
          finsum_mem_le_of_subset' _ (fun _ => Nat.cast_nonneg _) hB (by
            rintro _ ⟨ρ, hρ, rfl⟩
            exact hZl ρ hρ)
  linarith

theorem rightHalf_of (C₁ C₂ : ℝ) (h₁ : RightChiWith C₁) (h₂ : RightOneWith C₂) :
    RightHalfWith (max C₁ C₂) := by
  intro N _ χ hχ t
  have hl := log_mul_abs_add_two_nonneg N t
  rcases hχ with h | h
  · obtain ⟨hf, hs⟩ := h₁ N χ h t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hl)⟩
  · obtain ⟨hf, hs⟩ := h₂ N χ h t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hl)⟩

end PI.ZW
end
end

section
noncomputable section

open Metric

namespace PI.ZW

lemma order_ne_top_of_ball {f : ℂ → ℂ} {c z : ℂ} {R : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hfc : f c ≠ 0) (hz : z ∈ closedBall c R) : analyticOrderAt f z ≠ ⊤ := by
  have hR : 0 ≤ R := dist_nonneg.trans (Metric.mem_closedBall.1 hz)
  refine hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
    (Metric.mem_closedBall_self hR) hz ?_
  rw [analyticOrderAt_eq_zero.2 (Or.inr hfc)]
  exact ENat.zero_ne_top

lemma divisor_eq_order {f : ℂ → ℂ} {c z : ℂ} {r R : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hfc : f c ≠ 0) (hrR : r ≤ R) (hz : z ∈ closedBall c r) :
    MeromorphicOn.divisor f (closedBall c r) z = (analyticOrderNatAt f z : ℤ) := by
  have hzR : z ∈ closedBall c R := closedBall_subset_closedBall hrR hz
  have hm : MeromorphicOn f (closedBall c r) := (hf.mono (closedBall_subset_closedBall hrR)).meromorphicOn
  have hne := order_ne_top_of_ball hf hfc hzR
  rw [MeromorphicOn.divisor_apply hm hz, (hf z hzR).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hne]
  simp

theorem jensenCount : JensenCount := by
  intro f c M hf hfc hM1 hbd S hS
  have hR : |(19 / 10 : ℝ)| = 19 / 10 := abs_of_pos (by norm_num)
  have hf' : AnalyticOnNhd ℂ f (closedBall c |(19 / 10 : ℝ)|) := by rw [hR]; exact hf
  have hDnn : 0 ≤ MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf'
  have hfin : (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support.Finite :=
    (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).finiteSupport (isCompact_closedBall _ _)
  have hSD : ∀ u ∈ S, MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u =
      (analyticOrderNatAt f u : ℤ) ∧ 1 ≤ analyticOrderNatAt f u ∧ 0 < ‖c - u‖ ∧ ‖c - u‖ ≤ 37 / 20 := by
    intro u hu
    obtain ⟨hub, hfu⟩ := hS hu
    have hub' : u ∈ closedBall c (19 / 10) := closedBall_subset_closedBall (by norm_num) hub
    have hdiv := divisor_eq_order hf hfc le_rfl hub'
    have hne := order_ne_top_of_ball hf hfc hub'
    refine ⟨by rw [hR]; exact hdiv, ?_, ?_, ?_⟩
    · by_contra h0
      push_neg at h0
      have h00 : analyticOrderNatAt f u = 0 := by omega
      have hord : analyticOrderAt f u = 0 := by rw [← Nat.cast_analyticOrderNatAt hne, h00]; rfl
      rcases analyticOrderAt_eq_zero.1 hord with h | h
      · exact h (hf u hub')
      · exact h hfu
    · have : u ≠ c := by rintro rfl; exact hfc hfu
      exact norm_pos_iff.2 (sub_ne_zero.2 this.symm)
    · rw [norm_sub_rev, ← dist_eq_norm]; exact mem_closedBall.1 hub
  have hSsub : S ⊆ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support := by
    intro u hu
    obtain ⟨h1, h2, -, -⟩ := hSD u hu
    simp only [Function.mem_support, h1]
    exact_mod_cast (by omega : analyticOrderNatAt f u ≠ 0)
  have hSfin : S.Finite := hfin.subset hSsub
  refine ⟨hSfin, ?_⟩
  have hJ := AnalyticOnNhd.circleAverage_log_norm (c := c) (R := 19 / 10) (by norm_num) hf' hfc
  have hup : Real.circleAverage (fun x => Real.log ‖f x‖) c (19 / 10) ≤ Real.log M := by
    apply Real.circleAverage_mono_on_of_le_circle
    · exact MeromorphicOn.circleIntegrable_log_norm (hf'.mono sphere_subset_closedBall).meromorphicOn
    · intro x hx
      rw [hR] at hx
      by_cases h0 : f x = 0
      · rw [h0, norm_zero, Real.log_zero]; exact Real.log_nonneg hM1
      · exact Real.log_le_log (norm_pos_iff.2 h0) (hbd x hx)
  set g : ℂ → ℝ := fun u => (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u : ℝ) *
    Real.log (19 / 10 * ‖c - u‖⁻¹) with hg
  have hgnn : ∀ u, 0 ≤ g u := by
    intro u
    by_cases hu : u ∈ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support
    · have hdu : (0 : ℝ) ≤ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u : ℝ) := by
        exact_mod_cast hDnn u
      have hin := (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).supportWithinDomain hu
      rw [hR] at hin
      have hcu : ‖c - u‖ ≤ 19 / 10 := by rw [norm_sub_rev, ← dist_eq_norm]; exact mem_closedBall.1 hin
      apply mul_nonneg hdu
      rcases (norm_nonneg (c - u)).eq_or_lt with h0 | h0
      · rw [← h0, inv_zero, mul_zero, Real.log_zero]
      · apply Real.log_nonneg
        rw [← div_eq_mul_inv, le_div_iff₀ h0]; linarith
    · simp only [Function.mem_support, not_not] at hu
      simp [hg, hu]
  have hgsupp : Function.support g ⊆ hfin.toFinset := by
    intro u hu
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    apply hu
    simp [hg, h0]
  have hfs : ∑ᶠ u, g u = ∑ u ∈ hfin.toFinset, g u := finsum_eq_sum_of_support_subset g hgsupp
  have hsub2 : hSfin.toFinset ⊆ hfin.toFinset := by
    intro u hu
    simp only [Set.Finite.mem_toFinset] at hu ⊢
    exact hSsub hu
  have hlow : ∑ u ∈ hSfin.toFinset, g u ≤ ∑ u ∈ hfin.toFinset, g u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun u _ _ => hgnn u
  have hLpos : 0 < Real.log ((19 / 10) / (37 / 20)) := Real.log_pos (by norm_num)
  have hterm : ∀ u ∈ hSfin.toFinset, (analyticOrderNatAt f u : ℝ) * Real.log ((19 / 10) / (37 / 20)) ≤ g u := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    obtain ⟨h1, h2, h3, h4⟩ := hSD u hu
    simp only [hg, h1]
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log (by norm_num)
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) h3 h4
  have hfc0 : 0 < ‖f c‖ := norm_pos_iff.2 hfc
  have hM0 : 0 < M := by linarith
  rw [finsum_mem_eq_finite_toFinset_sum _ hSfin, le_div_iff₀ hLpos, Finset.sum_mul,
    Real.log_div hM0.ne' hfc0.ne']
  have hsum := Finset.sum_le_sum hterm
  have hJ' : ∑ᶠ u, g u = Real.circleAverage (fun x => Real.log ‖f x‖) c (19 / 10) - Real.log ‖f c‖ := by
    rw [hJ]; simp only [hg]; ring
  linarith

end PI.ZW
end
end

section
noncomputable section

open Metric Complex

namespace PI.ZW

lemma log_le_nine (X M' : ℝ) (hX : 2 ≤ X) (hM : 0 < M') (h : M' ≤ 170 * X) :
    Real.log M' ≤ 9 * Real.log X := by
  have hX0 : 0 < X := by linarith
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  have h170 : Real.log 170 ≤ Real.log 256 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  calc Real.log M' ≤ Real.log (170 * X) := Real.log_le_log hM h
    _ = Real.log 170 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
    _ ≤ 9 * Real.log X := by linarith

lemma mem_closedBall_of_right {ρ : ℂ} {t : ℝ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1) (h3 : |ρ.im - t| ≤ 1) :
    ρ ∈ closedBall (2 + t * I) (37 / 20) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsq : ‖ρ - (2 + t * I)‖ ^ 2 ≤ (37 / 20) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    have h4 := abs_le.mp h3
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ 7 / 2 - ρ.re),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (ρ.im - t)) (by linarith : (0 : ℝ) ≤ 1 + (ρ.im - t))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq

lemma sphere_facts {z : ℂ} {t : ℝ} (hz : z ∈ sphere (2 + t * I) (19 / 10)) :
    1 / 10 ≤ z.re ∧ ‖z‖ ≤ |t| + 4 := by
  rw [mem_sphere, dist_eq_norm] at hz
  have hc : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp [Complex.norm_real]
  constructor
  · have h1 := Complex.abs_re_le_norm (z - (2 + t * I))
    rw [hz] at h1
    simp at h1
    linarith [(abs_le.mp h1).1]
  · calc ‖z‖ = ‖(z - (2 + t * I)) + (2 + t * I)‖ := by ring_nf
      _ ≤ ‖z - (2 + t * I)‖ + ‖(2 : ℂ) + t * I‖ := norm_add_le _ _
      _ ≤ |t| + 4 := by rw [hz]; linarith

theorem rightChi_of (hJ : JensenCount) : RightChi := by
  intro hL hI
  have hl : 0 < Real.log ((19 / 10) / (37 / 20) : ℝ) := Real.log_pos (by norm_num)
  refine ⟨9 / Real.log ((19 / 10) / (37 / 20)), fun N _ χ hχ t => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hcre : (2 + t * I : ℂ).re = 2 := by simp
  have hc0 : DirichletCharacter.LFunction χ (2 + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hcre]; norm_num)
  have hpos : 0 < ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := norm_pos_iff.mpr hc0
  have hinv := hI N χ (2 + t * I) (by rw [hcre]; norm_num)
  rw [hcre] at hinv
  have hfc : 1 / 2 ≤ ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := by
    have h := (inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)).mp (hinv.trans (by norm_num))
    linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall (2 + t * I) (19 / 10)) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hM1 : (1 : ℝ) ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by
    have : 0 ≤ 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by positivity
    linarith
  have hbd : ∀ z ∈ sphere (2 + t * I) (19 / 10), ‖DirichletCharacter.LFunction χ z‖ ≤
      1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by
    intro z hz
    obtain ⟨hre, hnorm⟩ := sphere_facts hz
    have hz0 : 0 < z.re := by linarith
    refine (hL N χ hχ z hz0).trans ?_
    have h1 : ‖z‖ / z.re ≤ 10 * (|t| + 4) := by
      rw [div_le_iff₀ hz0]
      nlinarith [mul_le_mul_of_nonneg_left hre (by positivity : (0 : ℝ) ≤ 10 * (|t| + 4))]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1))
    nlinarith
  have hS : RightNear χ t ⊆ {z | z ∈ closedBall (2 + t * I) (37 / 20) ∧ DirichletCharacter.LFunction χ z = 0} :=
    fun ρ hρ => ⟨mem_closedBall_of_right hρ.1 hρ.2.1 hρ.2.2.1, hρ.2.2.2⟩
  obtain ⟨hfin, hsum⟩ := hJ (DirichletCharacter.LFunction χ) (2 + t * I) _ han hc0 hM1 hbd (RightNear χ t) hS
  refine ⟨hfin, hsum.trans ?_⟩
  have hX : 2 ≤ (N : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have htN : |t| ≤ N * |t| := le_mul_of_one_le_left (abs_nonneg t) hNr
  have hM85 : 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) ≤ 85 * ((N : ℝ) * (|t| + 2)) := by
    nlinarith [abs_nonneg t]
  have hM' : (1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))) / ‖DirichletCharacter.LFunction χ (2 + t * I)‖ ≤
      170 * ((N : ℝ) * (|t| + 2)) := by
    rw [div_le_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left hfc (by linarith : (0 : ℝ) ≤ (N : ℝ) * (|t| + 2))]
  have h9 := log_le_nine _ _ hX (by positivity) hM'
  calc Real.log ((1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))) /
        ‖DirichletCharacter.LFunction χ (2 + t * I)‖) / Real.log ((19 / 10) / (37 / 20))
      ≤ (9 * Real.log ((N : ℝ) * (|t| + 2))) / Real.log ((19 / 10) / (37 / 20)) :=
        div_le_div_of_nonneg_right h9 hl.le
    _ = 9 / Real.log ((19 / 10) / (37 / 20)) * Real.log ((N : ℝ) * (|t| + 2)) := by ring

end PI.ZW
end
end

section
noncomputable section

open Metric Complex Filter Topology

namespace PI.ZW

abbrev zeta1 : ℂ → ℂ := DirichletCharacter.LFunctionTrivChar₁ 1

lemma zeta1_eq_sub_one_mul_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : zeta1 s = (s - 1) * riemannZeta s := by
  show DirichletCharacter.LFunctionTrivChar₁ 1 s = _
  unfold DirichletCharacter.LFunctionTrivChar₁
  rw [Function.update_of_ne hs]
  simp [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]

lemma zeta1_apply_one : zeta1 1 = 1 := by
  show DirichletCharacter.LFunctionTrivChar₁ 1 1 = 1
  unfold DirichletCharacter.LFunctionTrivChar₁
  simp

lemma analyticAt_riemannZeta_of_ne {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  exact DifferentiableOn.analyticAt (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

lemma order_zeta1 {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt zeta1 s = analyticOrderNatAt riemannZeta s := by
  have hev : zeta1 =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
    exact zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hz
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have h2 := analyticAt_riemannZeta_of_ne hs
  simp only [analyticOrderNatAt]
  rw [analyticOrderAt_congr hev,
    show (fun z => (z - 1) * riemannZeta z) = (fun z : ℂ => z - 1) * riemannZeta from rfl,
    analyticOrderAt_mul h1 h2]
  have h0 : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
    (analyticOrderAt_eq_zero).2 (Or.inr (by simpa [sub_eq_zero] using hs))
  rw [h0, zero_add]

theorem rightOne_of (hJ : JensenCount) : RightOne := by
  intro hZ hI
  refine ⟨11 / Real.log ((19 / 10) / (37 / 20)), ?_⟩
  intro N _ χ hN t
  subst hN
  have hL : DirichletCharacter.LFunction χ = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  have hlogq : 0 < Real.log ((19 / 10 : ℝ) / (37 / 20)) := Real.log_pos (by norm_num)
  set c : ℂ := 2 + (t : ℂ) * Complex.I with hc
  have hcre : c.re = 2 := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  have hc1 : c ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hcre] at this
    norm_num at this
  have hAn : AnalyticOnNhd ℂ zeta1 (closedBall c (19 / 10)) := fun z _ =>
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt z
  have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hcre]; norm_num)
  have hfc : zeta1 c ≠ 0 := by
    rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hc1]
    exact mul_ne_zero (sub_ne_zero.2 hc1) hζc
  have hζlow : (1 / 2 : ℝ) ≤ ‖riemannZeta c‖ := by
    have k := hI 1 (1 : DirichletCharacter ℂ 1) c (by rw [hcre]; norm_num)
    rw [DirichletCharacter.LFunction_modOne_eq, hcre] at k
    have hpos : 0 < ‖riemannZeta c‖ := norm_pos_iff.2 hζc
    have k2 : ‖riemannZeta c‖⁻¹ ≤ 2 := by norm_num at k ⊢; linarith
    have := inv_le_of_inv_le₀ hpos k2
    norm_num at this ⊢
    linarith
  have hc1n : (1 : ℝ) ≤ ‖c - 1‖ := by
    have := Complex.abs_re_le_norm (c - 1)
    rw [Complex.sub_re, hcre, Complex.one_re] at this
    norm_num at this
    linarith
  have hfcl : (1 / 2 : ℝ) ≤ ‖zeta1 c‖ := by
    rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hc1, norm_mul]
    nlinarith [norm_nonneg (riemannZeta c)]
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hsph : ∀ z ∈ sphere c (19 / 10), ‖zeta1 z‖ ≤ 13 * (|t| + 5) ^ 2 := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    by_cases hz1 : z = 1
    · rw [hz1, zeta1_apply_one, norm_one]
      nlinarith
    · rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hz1, norm_mul]
      have hre : (1 / 10 : ℝ) ≤ z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, hcre, hz] at this
        have := (abs_le.1 this).1
        linarith
      have hcn : ‖c‖ ≤ 2 + |t| := by
        rw [hc]
        calc ‖(2 : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = 2 + |t| := by simp
      have hzn : ‖z‖ ≤ |t| + 4 := by
        have := norm_le_insert' z c
        have h2 : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
          calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
            _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
        linarith
      have hz1n : ‖z - 1‖ ≤ |t| + 5 := by
        have := norm_sub_le z 1
        rw [norm_one] at this
        linarith
      have hζ := hZ z (by linarith) hz1
      have hz1pos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
      have hinv : 1 + 1 / z.re ≤ 11 := by
        have : 1 / z.re ≤ 10 := by
          rw [div_le_iff₀ (by linarith)]
          linarith
        linarith
      have hA : ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) ≤ (|t| + 5) * (|t| + 5) * 11 := by
        have h1 : 0 ≤ ‖z - 1‖ * ‖z‖ := by positivity
        calc ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) ≤ ‖z - 1‖ * ‖z‖ * 11 := mul_le_mul_of_nonneg_left hinv h1
          _ ≤ (|t| + 5) * (|t| + 5) * 11 := by
            have : ‖z‖ ≤ |t| + 5 := by linarith
            gcongr
      calc ‖z - 1‖ * ‖riemannZeta z‖
          ≤ ‖z - 1‖ * (1 + 1 / ‖z - 1‖ + ‖z‖ * (1 + 1 / z.re)) :=
            mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
        _ = ‖z - 1‖ + ‖z - 1‖ * (1 / ‖z - 1‖) + ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) := by ring
        _ = ‖z - 1‖ + 1 + ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) := by rw [mul_one_div_cancel hz1pos.ne']
        _ ≤ 13 * (|t| + 5) ^ 2 := by nlinarith
  have hM1 : (1 : ℝ) ≤ 13 * (|t| + 5) ^ 2 := by nlinarith
  have hsub : RightNear χ t ⊆ {z | z ∈ closedBall c (37 / 20) ∧ zeta1 z = 0} := by
    intro ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hρ
    rw [hL] at h4
    have hρ1 : ρ ≠ 1 := by
      intro e
      rw [e] at h2
      simp at h2
    refine ⟨?_, by rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hρ1, h4, mul_zero]⟩
    rw [mem_closedBall, dist_eq_norm]
    have hsq : ‖ρ - c‖ ^ 2 ≤ (37 / 20) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hcre, hcim]
      have := abs_le.1 h3
      nlinarith
    nlinarith [norm_nonneg (ρ - c)]
  obtain ⟨hfin, hsum⟩ := hJ zeta1 c (13 * (|t| + 5) ^ 2) hAn hfc hM1 hsph _ hsub
  refine ⟨hfin, ?_⟩
  rw [hL]
  have hcongr : ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt riemannZeta ρ : ℝ) =
      ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt zeta1 ρ : ℝ) := by
    refine finsum_mem_congr rfl fun ρ hρ => ?_
    have hρ1 : ρ ≠ 1 := by
      intro e
      have h2 := hρ.2.1
      rw [e] at h2
      simp at h2
    rw [order_zeta1 hρ1]
  rw [hcongr]
  refine hsum.trans ?_
  simp only [Nat.cast_one, one_mul]
  set y : ℝ := |t| + 2 with hy
  have hy2 : (2 : ℝ) ≤ y := by linarith
  have hfpos : 0 < ‖zeta1 c‖ := by linarith
  have hq : 13 * (|t| + 5) ^ 2 / ‖zeta1 c‖ ≤ y ^ 11 := by
    rw [div_le_iff₀ hfpos]
    have e1 : |t| + 5 ≤ 3 * y := by linarith
    have e2 : (|t| + 5) ^ 2 ≤ 9 * y ^ 2 := by nlinarith
    have e3 : (256 : ℝ) ≤ y ^ 8 := by
      have := pow_le_pow_left₀ (by norm_num) hy2 8
      norm_num at this
      linarith
    have e4 : y ^ 10 ≤ y ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e5 : 256 * y ^ 2 ≤ y ^ 10 := by
      have := mul_le_mul_of_nonneg_right e3 (sq_nonneg y)
      calc 256 * y ^ 2 ≤ y ^ 8 * y ^ 2 := this
        _ = y ^ 10 := by ring
    have e6 : y ^ 11 * (1 / 2) ≤ y ^ 11 * ‖zeta1 c‖ :=
      mul_le_mul_of_nonneg_left hfcl (by positivity)
    nlinarith
  have hlog : Real.log (13 * (|t| + 5) ^ 2 / ‖zeta1 c‖) ≤ 11 * Real.log y := by
    rw [show (11 : ℝ) * Real.log y = Real.log (y ^ 11) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) hq
  calc Real.log (13 * (|t| + 5) ^ 2 / ‖zeta1 c‖) / Real.log ((19 / 10) / (37 / 20))
      ≤ 11 * Real.log y / Real.log ((19 / 10) / (37 / 20)) := div_le_div_of_nonneg_right hlog hlogq.le
    _ = 11 / Real.log ((19 / 10) / (37 / 20)) * Real.log y := by ring

end PI.ZW
end
end

section
namespace PI.ZW

theorem rightChi : RightChi := rightChi_of jensenCount

theorem rightOne : RightOne := rightOne_of jensenCount

theorem zerosWindow_of_transfer (hT : Transfer) :
    PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow := by
  intro hL hZ hI
  obtain ⟨C₁, h₁⟩ := rightChi hL hI
  obtain ⟨C₂, h₂⟩ := rightOne hZ hI
  have hlog : ∀ (N : ℕ) [NeZero N] (t : ℝ), 0 ≤ Real.log (↑N * (|t| + 2)) := by
    intro N _ t
    apply Real.log_nonneg
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hN) (add_nonneg (abs_nonneg t) zero_le_two)]
  have h₁' : RightChiWith (max C₁ 1) := by
    unfold RightChiWith at h₁ ⊢
    intro N _ χ hχ t
    obtain ⟨hf, hs⟩ := h₁ N χ hχ t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlog N t))⟩
  have h₂' : RightOneWith (max C₂ 1) := by
    unfold RightOneWith at h₂ ⊢
    intro N _ χ hχ t
    obtain ⟨hf, hs⟩ := h₂ N χ hχ t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlog N t))⟩
  have hw := zerosWindowWith_of _ (rightHalf_of _ _ h₁' h₂') hT
  unfold PI.ZerosWindow
  exact ⟨_, mul_pos two_pos (lt_of_lt_of_le one_pos (le_trans (le_max_right C₁ 1) (le_max_left _ _))), hw⟩

end PI.ZW
end
