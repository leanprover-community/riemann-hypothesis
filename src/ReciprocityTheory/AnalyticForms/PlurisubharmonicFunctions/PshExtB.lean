import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

section
open Metric Real Filter Topology MeasureTheory

namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension

section
theorem cA_mul (b : ℝ) (f : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    circleAverage (fun z => b * f z) c R = b * circleAverage f c R := by
  simp only [circleAverage, smul_eq_mul, intervalIntegral.integral_const_mul]; ring

theorem mp_core {k : ℂ → ℝ} {c ζ0 : ℂ} {r η : ℝ} {E : Finset ℂ}
    (hζ0 : ζ0 ∈ closedBall c r) (hζ0E : ζ0 ∉ E) (hη : 0 < η)
    (hcont : ContinuousOn k (closedBall c r \ ↑E))
    (hsph : ∀ ζ ∈ sphere c r, k ζ < k ζ0)
    (hpunct : ∀ e ∈ E, ∀ ζ ∈ closedBall c r \ ↑E, 0 < dist ζ e → dist ζ e < η → k ζ < k ζ0)
    (hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball c r \ ↑E → k a < circleAverage k a s) :
    False := by
  set K := closedBall c r \ ⋃ e ∈ E, ball e (η / 2) with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall c r).diff (isOpen_biUnion fun e _ => isOpen_ball)
  have hKE : K ⊆ closedBall c r \ ↑E := by
    intro x hx
    refine ⟨hx.1, fun hxE => hx.2 ?_⟩
    exact Set.mem_biUnion hxE (mem_ball_self (by linarith))
  have hζ0K : ζ0 ∈ K := by
    refine ⟨hζ0, ?_⟩
    simp only [Set.mem_iUnion, mem_ball, not_exists]
    intro e he hd
    have hpos : 0 < dist ζ0 e := dist_pos.2 (fun h => hζ0E (h ▸ he))
    exact lt_irrefl _ (hpunct e he ζ0 ⟨hζ0, hζ0E⟩ hpos (by linarith))
  obtain ⟨ζ1, hζ1K, hmax⟩ := hKc.exists_isMaxOn ⟨ζ0, hζ0K⟩ (hcont.mono hKE)
  have h10 : k ζ0 ≤ k ζ1 := hmax hζ0K
  have hin : dist ζ1 c < r := by
    rcases (mem_closedBall.1 hζ1K.1).lt_or_eq with h | h
    · exact h
    · exact absurd (hsph ζ1 (mem_sphere.2 h)) (not_lt.2 h10)
  have hfar : ∀ e ∈ E, η ≤ dist ζ1 e := by
    intro e he
    by_contra hlt
    push Not at hlt
    have h2 : η / 2 ≤ dist ζ1 e := by
      by_contra h3
      push Not at h3
      exact hζ1K.2 (Set.mem_biUnion he (mem_ball.2 h3))
    exact absurd (hpunct e he ζ1 (hKE hζ1K) (by linarith) hlt) (not_lt.2 h10)
  set s := min (r - dist ζ1 c) (η / 2) / 2 with hs
  have hm0 : 0 < min (r - dist ζ1 c) (η / 2) := lt_min (by linarith) (by linarith)
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s ≤ (r - dist ζ1 c) / 2 := by
    have := min_le_left (r - dist ζ1 c) (η / 2); rw [hs]; linarith
  have hs2 : s ≤ η / 4 := by
    have := min_le_right (r - dist ζ1 c) (η / 2); rw [hs]; linarith
  have hsK : closedBall ζ1 s ⊆ K := by
    intro x hx
    have hx' := mem_closedBall.1 hx
    refine ⟨mem_closedBall.2 ?_, ?_⟩
    · linarith [dist_triangle x ζ1 c]
    · simp only [Set.mem_iUnion, mem_ball, not_exists, not_lt]
      intro e he
      have h1 := hfar e he
      have h2 := dist_triangle ζ1 x e
      rw [dist_comm ζ1 x] at h2
      linarith
  have hsB : closedBall ζ1 s ⊆ ball c r \ ↑E := by
    intro x hx
    refine ⟨mem_ball.2 ?_, (hKE (hsK hx)).2⟩
    have hx' := mem_closedBall.1 hx
    linarith [dist_triangle x ζ1 c]
  have hlt := hsub ζ1 s hs0 hsB
  have hle : circleAverage k ζ1 s ≤ k ζ1 := by
    apply circleAverage_mono_on_of_le_circle
    · apply ContinuousOn.circleIntegrable hs0.le
      exact (hcont.mono hKE).mono (sphere_subset_closedBall.trans hsK)
    · intro x hx
      rw [abs_of_pos hs0] at hx
      exact hmax (hsK (sphere_subset_closedBall hx))
  linarith

theorem circleAverage_norm_sub_sq (a c : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    circleAverage (fun ζ => ‖ζ - c‖ ^ 2) a s = ‖a - c‖ ^ 2 + s ^ 2 := by
  have hpt : ∀ ζ ∈ sphere a |s|, ‖ζ - c‖ ^ 2 =
      (‖a - c‖ ^ 2 + s ^ 2) + 2 * ((starRingEnd ℂ (a - c)) * (ζ - a)).re := by
    intro ζ hζ
    rw [abs_of_nonneg hs, mem_sphere, dist_eq_norm] at hζ
    have : ζ - c = (a - c) + (ζ - a) := by ring
    rw [this, ← hζ, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp [Complex.mul_re]
    ring
  rw [circleAverage_congr_sphere hpt]
  have hh : circleAverage (fun ζ => (starRingEnd ℂ (a - c)) * (ζ - a)) a s = 0 := by
    rw [circleAverage_of_differentiable_on_off_countable (s := ∅) Set.countable_empty]
    · simp
    · exact (by fun_prop : Continuous fun ζ : ℂ => (starRingEnd ℂ (a - c)) * (ζ - a)).continuousOn
    · intro z _; fun_prop
  have hre : circleAverage (fun ζ => ((starRingEnd ℂ (a - c)) * (ζ - a)).re) a s = 0 := by
    have h2 : CircleIntegrable (fun ζ => (starRingEnd ℂ (a - c)) * (ζ - a)) a s :=
      (by fun_prop : Continuous fun ζ : ℂ => (starRingEnd ℂ (a - c)) * (ζ - a)).continuousOn.circleIntegrable'
    have := Complex.reCLM.circleAverage_comp_comm h2
    simp only [Function.comp_def, Complex.reCLM_apply] at this
    rw [this, hh]; simp
  have h2 : circleAverage (fun x => 2 * ((starRingEnd ℂ) (a - c) * (x - a)).re) a s =
      2 * circleAverage (fun x => ((starRingEnd ℂ) (a - c) * (x - a)).re) a s :=
    cA_mul _ _ _ _
  rw [circleAverage_fun_add, circleAverage_const, h2, hre]
  · simp
  · exact (continuous_const).continuousOn.circleIntegrable'
  · exact (by fun_prop : Continuous fun ζ : ℂ => 2 * ((starRingEnd ℂ (a - c)) * (ζ - a)).re).continuousOn.circleIntegrable'

noncomputable def pert (E : Finset ℂ) (c : ℂ) (ε δ : ℝ) (ζ : ℂ) : ℝ :=
  ε * ∑ f ∈ E, log ‖ζ - f‖ + δ * ‖ζ - c‖ ^ 2

theorem pert_continuousOn (E : Finset ℂ) (c : ℂ) (ε δ : ℝ) :
    ContinuousOn (pert E c ε δ) (↑E)ᶜ := by
  have hlog : ∀ f ∈ E, ContinuousOn (fun ζ : ℂ => log ‖ζ - f‖) (↑E)ᶜ := by
    intro f hf
    apply ContinuousOn.log (by fun_prop)
    intro x hx hx0
    rw [norm_eq_zero, sub_eq_zero] at hx0
    exact hx (hx0 ▸ hf)
  unfold pert
  exact (continuousOn_const.mul (continuousOn_finsetSum E hlog)).add (by fun_prop)

theorem pert_submean {E : Finset ℂ} {c a : ℂ} {s ε δ : ℝ} (hs : 0 < s) (hε : 0 ≤ ε)
    (haE : a ∉ E) (hE : ∀ f ∈ E, f ∉ sphere a s) :
    CircleIntegrable (pert E c ε δ) a s ∧
      pert E c ε δ a + δ * s ^ 2 ≤ circleAverage (pert E c ε δ) a s := by
  have hlogc : ∀ f ∈ E, ContinuousOn (fun ζ : ℂ => log ‖ζ - f‖) (sphere a |s|) := by
    intro f hf
    apply ContinuousOn.log (by fun_prop)
    intro x hx hx0
    rw [norm_eq_zero, sub_eq_zero] at hx0
    rw [abs_of_pos hs] at hx
    exact hE f hf (hx0 ▸ hx)
  have hli : ∀ f ∈ E, CircleIntegrable (fun ζ : ℂ => log ‖ζ - f‖) a s :=
    fun f hf => (hlogc f hf).circleIntegrable'
  have hsumc : ContinuousOn (fun ζ : ℂ => ∑ f ∈ E, log ‖ζ - f‖) (sphere a |s|) :=
    continuousOn_finsetSum E hlogc
  have hqi : CircleIntegrable (fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2) a s :=
    (by fun_prop : Continuous fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2).continuousOn.circleIntegrable'
  have hsi : CircleIntegrable (fun ζ : ℂ => ε * ∑ f ∈ E, log ‖ζ - f‖) a s :=
    (continuousOn_const.mul hsumc).circleIntegrable'
  refine ⟨hsi.add hqi, ?_⟩
  unfold pert
  rw [circleAverage_fun_add hsi hqi]
  have h1 : circleAverage (fun ζ : ℂ => ε * ∑ f ∈ E, log ‖ζ - f‖) a s
      = ε * ∑ f ∈ E, circleAverage (fun ζ : ℂ => log ‖ζ - f‖) a s := by
    rw [show circleAverage (fun ζ : ℂ => ε * ∑ f ∈ E, log ‖ζ - f‖) a s
      = ε * circleAverage (fun ζ : ℂ => ∑ f ∈ E, log ‖ζ - f‖) a s from cA_mul _ _ _ _]
    rw [circleAverage_fun_sum hli]
  have h2 : circleAverage (fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2) a s = δ * (‖a - c‖ ^ 2 + s ^ 2) := by
    rw [show circleAverage (fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2) a s
      = δ * circleAverage (fun ζ : ℂ => ‖ζ - c‖ ^ 2) a s from cA_mul _ _ _ _]
    rw [circleAverage_norm_sub_sq a c hs.le]
  rw [h1, h2]
  have h3 : ∑ f ∈ E, log ‖a - f‖ ≤ ∑ f ∈ E, circleAverage (fun ζ : ℂ => log ‖ζ - f‖) a s := by
    apply Finset.sum_le_sum
    intro f hf
    have haf : a - f ≠ 0 := sub_ne_zero.2 (fun h => haE (h ▸ hf))
    rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hs.ne']
    have : log ‖a - f‖ = log s + log (s⁻¹ * ‖a - f‖) := by
      rw [log_mul (inv_ne_zero hs.ne') (norm_ne_zero_iff.2 haf), log_inv]; ring
    rw [this]
    have : log (s⁻¹ * ‖a - f‖) ≤ log⁺ (s⁻¹ * ‖a - f‖) := le_max_right _ _
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hε
  nlinarith

end

section

theorem smg2 {g : ℂ → ℝ} {r : ℝ} {F : Finset ℂ} (hr : 0 < r) (hF0 : (0 : ℂ) ∉ F)
    (hFr : ∀ f ∈ F, f ∈ ball (0 : ℂ) r)
    (hc : ContinuousOn g (closedBall 0 r \ ↑F))
    (hgrow : ∀ ε > 0, ∀ T : ℝ, ∃ η > 0, ∀ e ∈ F, ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F,
      dist ζ e < η → g ζ + ε * log ‖ζ - e‖ < T)
    (hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑F → g a ≤ circleAverage g a s) :
    g 0 ≤ circleAverage g 0 r := by
  have hsph : sphere (0 : ℂ) r ⊆ closedBall 0 r \ ↑F := fun x hx =>
    ⟨sphere_subset_closedBall hx, fun hxF => by
      have h1 := hFr x hxF
      rw [mem_ball] at h1
      rw [mem_sphere] at hx
      linarith⟩
  obtain ⟨Φ, hΦc, hΦs, hΦ0, hΦm⟩ := poisson_ext hr (hc.mono hsph)
  by_contra hlt
  push Not at hlt
  set γ := g 0 - Φ 0 with hγ
  have hγ0 : 0 < γ := by rw [hγ, hΦ0]; linarith
  obtain ⟨BΦ, hBΦ⟩ : ∃ BΦ, ∀ ζ ∈ closedBall (0 : ℂ) r, -Φ ζ ≤ BΦ := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r).bddAbove_image hΦc.neg
    exact ⟨M, fun ζ hζ => hM ⟨ζ, hζ, rfl⟩⟩
  set L := (F.card : ℝ) * log (2 * r) - ∑ f ∈ F, log ‖(0 : ℂ) - f‖ with hL
  set ε := γ / (4 * (|L| + 1)) with hε
  set δ := γ / (4 * (r ^ 2 + 1)) with hδ
  have hε0 : 0 < ε := by positivity
  have hδ0 : 0 < δ := by positivity
  have hεL : ε * L < γ / 4 := by
    have : ε * (|L| + 1) = γ / 4 := by rw [hε]; field_simp
    nlinarith [le_abs_self L]
  have hδr : δ * r ^ 2 < γ / 4 := by
    have : δ * (r ^ 2 + 1) = γ / 4 := by rw [hδ]; field_simp
    nlinarith
  set k : ℂ → ℝ := fun ζ => (g ζ - Φ ζ) + pert F 0 ε δ ζ with hk
  have hk0 : k 0 = γ + ε * ∑ f ∈ F, log ‖(0 : ℂ) - f‖ := by
    simp [hk, pert, hγ]
  have hlog2r : ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F, ∀ f ∈ F, log ‖ζ - f‖ ≤ log (2 * r) := by
    intro ζ hζ f hf
    have hne : ζ - f ≠ 0 := sub_ne_zero.2 (fun h => hζ.2 (h ▸ hf))
    apply log_le_log (norm_pos_iff.2 hne)
    have h1 := mem_closedBall_zero_iff.1 hζ.1
    have h2 := mem_ball_zero_iff.1 (hFr f hf)
    calc ‖ζ - f‖ ≤ ‖ζ‖ + ‖f‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith
  have hsumle : ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F,
      ∑ f ∈ F, log ‖ζ - f‖ ≤ (F.card : ℝ) * log (2 * r) := by
    intro ζ hζ
    have := Finset.sum_le_sum (fun f hf => hlog2r ζ hζ f hf)
    simpa using this
  obtain ⟨η, hη, hηp⟩ := hgrow ε hε0
    (k 0 - BΦ - δ * r ^ 2 - ε * ((F.card : ℝ) * |log (2 * r)|))
  apply mp_core (k := k) (c := 0) (ζ0 := 0) (r := r) (E := F) (η := η)
    (by simp [hr.le]) hF0 hη
  ·
    refine ((hc.sub (hΦc.mono Set.sdiff_subset))).add ((pert_continuousOn F 0 ε δ).mono ?_)
    intro x hx; exact hx.2
  ·
    intro ζ hζ
    have hζ' := hsph hζ
    have h1 : g ζ - Φ ζ = 0 := by rw [hΦs ζ hζ]; ring
    have h2 : ‖ζ - 0‖ ^ 2 = r ^ 2 := by
      rw [sub_zero, mem_sphere_zero_iff_norm.1 hζ]
    have h00 : δ * ‖(0 : ℂ) - 0‖ ^ 2 = 0 := by simp
    simp only [hk, pert, h1, h2]
    have := hsumle ζ hζ'
    have h3 := mul_le_mul_of_nonneg_left this hε0.le
    have : ε * L = ε * ((F.card : ℝ) * log (2 * r)) - ε * ∑ f ∈ F, log ‖(0 : ℂ) - f‖ := by
      rw [hL]; ring
    linarith
  ·
    intro e he ζ hζ _ hd
    have hgp := hηp e he ζ hζ hd
    have hsplit : ∑ f ∈ F, log ‖ζ - f‖ = log ‖ζ - e‖ + ∑ f ∈ F.erase e, log ‖ζ - f‖ :=
      (Finset.add_sum_erase F _ he).symm
    have herase : ∑ f ∈ F.erase e, log ‖ζ - f‖ ≤ (F.card : ℝ) * |log (2 * r)| := by
      calc ∑ f ∈ F.erase e, log ‖ζ - f‖ ≤ ∑ f ∈ F.erase e, |log (2 * r)| :=
            Finset.sum_le_sum (fun f hf =>
              (hlog2r ζ hζ f (Finset.mem_of_mem_erase hf)).trans (le_abs_self _))
        _ = ((F.erase e).card : ℝ) * |log (2 * r)| := by simp
        _ ≤ (F.card : ℝ) * |log (2 * r)| := by
            gcongr
            exact Finset.erase_subset e F
    have hq : ‖ζ - 0‖ ^ 2 ≤ r ^ 2 := by
      rw [sub_zero]
      have := mem_closedBall_zero_iff.1 hζ.1
      gcongr
    have hP := hBΦ ζ hζ.1
    have hk' : k ζ = g ζ - Φ ζ + (ε * ∑ f ∈ F, log ‖ζ - f‖ + δ * ‖ζ - 0‖ ^ 2) := rfl
    rw [hk', hsplit]
    have : δ * ‖ζ - 0‖ ^ 2 ≤ δ * r ^ 2 := mul_le_mul_of_nonneg_left hq hδ0.le
    have : ε * ∑ f ∈ F.erase e, log ‖ζ - f‖ ≤ ε * ((F.card : ℝ) * |log (2 * r)|) :=
      mul_le_mul_of_nonneg_left herase hε0.le
    nlinarith
  ·
    intro a s hs hsub'
    have haF : a ∉ F := (hsub' (mem_closedBall_self hs.le)).2
    have hFs : ∀ f ∈ F, f ∉ sphere a s := fun f hf hfs =>
      (hsub' (sphere_subset_closedBall hfs)).2 hf
    obtain ⟨hpi, hpm⟩ := pert_submean (c := 0) (δ := δ) hs hε0.le haF hFs
    have hsB : sphere a |s| ⊆ closedBall (0 : ℂ) r \ ↑F := by
      rw [abs_of_pos hs]
      intro x hx
      have := hsub' (sphere_subset_closedBall hx)
      exact ⟨ball_subset_closedBall this.1, this.2⟩
    have hgi : CircleIntegrable g a s := (hc.mono hsB).circleIntegrable'
    have hΦi : CircleIntegrable Φ a s := (hΦc.mono (hsB.trans Set.sdiff_subset)).circleIntegrable'
    have hav : circleAverage k a s =
        circleAverage g a s - circleAverage Φ a s + circleAverage (pert F 0 ε δ) a s := by
      have e1 := circleAverage_fun_add (hgi.sub hΦi) hpi
      have e2 : circleAverage (g - Φ) a s = circleAverage g a s - circleAverage Φ a s :=
        circleAverage_fun_sub hgi hΦi
      simp only [Pi.sub_apply] at e1
      rw [hk, e1, e2]
    have hΦa : circleAverage Φ a s = Φ a :=
      hΦm a s hs (fun x hx => (hsub' hx).1)
    have hga := hsub a s hs hsub'
    rw [hav, hΦa]
    have : 0 < δ * s ^ 2 := by positivity
    simp only [hk]
    linarith

theorem smg {g : ℂ → ℝ} {r : ℝ} {F : Finset ℂ} (hr : 0 < r) (hF0 : (0 : ℂ) ∉ F)
    (hFr : ∀ f ∈ F, f ∈ ball (0 : ℂ) r)
    (hc : ContinuousOn g (closedBall 0 r \ ↑F))
    (hB : ∃ B, ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F, g ζ ≤ B)
    (hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑F → g a ≤ circleAverage g a s) :
    g 0 ≤ circleAverage g 0 r := by
  obtain ⟨B, hB⟩ := hB
  refine smg2 hr hF0 hFr hc ?_ hsub
  intro ε hε T
  refine ⟨exp ((T - B) / ε), exp_pos _, ?_⟩
  intro e he ζ hζ hd
  have hne : ζ - e ≠ 0 := sub_ne_zero.2 (fun h => hζ.2 (h ▸ he))
  have hlog : log ‖ζ - e‖ < (T - B) / ε := by
    rw [dist_eq_norm] at hd
    exact (log_lt_iff_lt_exp (norm_pos_iff.2 hne)).2 hd
  have : ε * log ‖ζ - e‖ < T - B := by
    have := mul_lt_mul_of_pos_left hlog hε
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  linarith [hB ζ hζ]

theorem exists_sphere_ge {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn g (sphere 0 r)) (h : g 0 ≤ circleAverage g 0 r) :
    ∃ ζ ∈ sphere (0 : ℂ) r, g 0 ≤ g ζ := by
  by_contra hno
  push Not at hno
  obtain ⟨ζ1, hζ1, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hr.le) hc
  have hle : circleAverage g 0 r ≤ g ζ1 := by
    apply circleAverage_mono_on_of_le_circle
    · exact hc.circleIntegrable hr.le
    · intro x hx
      rw [abs_of_pos hr] at hx
      exact hmax hx
  linarith [hno ζ1 hζ1]

end

end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
end

section
open Metric Real Filter Topology MeasureTheory

namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension

section
open ReciprocityTheory.AnForm.A

variable {D : ℕ}

theorem psh_line {V : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (h : IsPsh V φ)
    (z w : Fin D → ℂ) {a : ℂ} {s : ℝ} (hs : 0 < s)
    (hV : ∀ ζ ∈ closedBall a s, z + ζ • w ∈ V) :
    CircleIntegrable (fun ζ => φ (z + ζ • w)) a s ∧
      φ (z + a • w) ≤ circleAverage (fun ζ => φ (z + ζ • w)) a s := by
  have key : ∀ θ : ℝ, z + circleMap a s θ • w = (z + a • w) + circleMap 0 1 θ • ((s : ℂ) • w) := by
    intro θ
    ext i
    simp only [circleMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_one]
    ring
  have hU : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → (z + a • w) + ζ • ((s : ℂ) • w) ∈ V := by
    intro ζ hζ
    have hn : ‖(s : ℂ) * ζ‖ ≤ s := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
      nlinarith [norm_nonneg ζ]
    have h1 : a + (s : ℂ) * ζ ∈ closedBall a s := by
      rw [mem_closedBall, dist_eq_norm]
      simpa using hn
    have h2 := hV _ h1
    have e : z + (a + (s : ℂ) * ζ) • w = (z + a • w) + ζ • ((s : ℂ) • w) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e] at h2
    exact h2
  obtain ⟨hi, hle⟩ := h.2 (z + a • w) ((s : ℂ) • w) hU
  refine ⟨?_, ?_⟩
  · unfold CircleIntegrable at hi ⊢
    simpa only [key] using hi
  · unfold Real.circleAverage at hle ⊢
    simpa only [key] using hle

noncomputable def ej (j : Fin D) : Fin D → ℂ := Pi.single j 1

theorem line_coord (x : Fin D → ℂ) (j i : Fin D) (ζ : ℂ) :
    (x + ζ • ej j) i = x i + if i = j then ζ else 0 := by
  simp only [ej, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem loglog_bound (C a0 ε T : ℝ) (hε : 0 < ε) (ha0 : 0 ≤ a0) :
    ∃ Y : ℝ, ∀ y, Y ≤ y → 0 ≤ y → C * log (exp 1 + a0 + y) - ε * y < T := by
  have hc0 : 0 < |C| + 1 := by positivity
  have hK0 : 0 < 2 * (|C| + 1) / ε := by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ε / 2 * (exp 1 + a0) + (|C| + 1) * (log (2 * (|C| + 1) / ε) - 1) :=
    ⟨_, rfl⟩
  refine ⟨2 * (A - T) / ε + 1, fun y hy hy0 => ?_⟩
  have he : (2 : ℝ) ≤ exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hx : 0 < exp 1 + a0 + y := by linarith
  have hlog0 : 0 ≤ log (exp 1 + a0 + y) := Real.log_nonneg (by linarith)
  have h1 : log ((exp 1 + a0 + y) / (2 * (|C| + 1) / ε)) ≤ (exp 1 + a0 + y) / (2 * (|C| + 1) / ε) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx.ne' hK0.ne'] at h1
  have h2 : C * log (exp 1 + a0 + y) ≤ (|C| + 1) * log (exp 1 + a0 + y) := by
    apply mul_le_mul_of_nonneg_right _ hlog0
    have := le_abs_self C
    linarith
  have h3 := mul_le_mul_of_nonneg_left
    (show log (exp 1 + a0 + y) ≤ (exp 1 + a0 + y) / (2 * (|C| + 1) / ε) + (log (2 * (|C| + 1) / ε) - 1) by linarith) hc0.le
  have h3' := mul_add (|C| + 1) ((exp 1 + a0 + y) / (2 * (|C| + 1) / ε)) (log (2 * (|C| + 1) / ε) - 1)
  have h4 : (|C| + 1) * ((exp 1 + a0 + y) / (2 * (|C| + 1) / ε)) = ε / 2 * (exp 1 + a0 + y) := by
    field_simp
  have h5 : ε * (2 * (A - T) / ε + 1) = 2 * (A - T) + ε := by
    field_simp
  have h6 := mul_le_mul_of_nonneg_left hy hε.le
  nlinarith [h2, h3, h3', h4, h5, h6, hA]

section partA

variable {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C : ℝ}

theorem slice_step (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹))
    {x : Fin D → ℂ} {j : Fin D} (hj : j ∈ S) {r : ℝ} (hr : 0 < r) (hxA : x ∉ coordDiv S)
    (hxj : ‖x j‖ < r) (hdisc : ∀ ζ ∈ closedBall (0 : ℂ) r, x + ζ • ej j ∈ U) :
    ∃ ζ ∈ sphere (0 : ℂ) r, u x ≤ u (x + ζ • ej j) := by
  have hxi : ∀ i ∈ S, x i ≠ 0 := fun i hi h0 => hxA ⟨i, hi, h0⟩
  have hgood : ∀ ζ ∈ closedBall (0 : ℂ) r, ζ ≠ -x j → x + ζ • ej j ∈ U \ coordDiv S := by
    intro ζ hζ hne
    refine ⟨hdisc ζ hζ, ?_⟩
    rintro ⟨i, hi, h0⟩
    rw [line_coord] at h0
    split_ifs at h0 with hij
    · subst hij
      exact hne (by linear_combination h0)
    · rw [add_zero] at h0
      exact hxi i hi h0
  have hx1 : ∀ i, ‖x i‖ < 1 := by
    have h0 := hU1 (hdisc 0 (Metric.mem_closedBall_self hr.le))
    rw [zero_smul, add_zero, mem_ball, dist_zero_right] at h0
    intro i
    exact lt_of_le_of_lt (norm_le_pi_norm x i) h0
  obtain ⟨a0, ha0def⟩ : ∃ a0 : ℝ, a0 = ∑ i ∈ S.erase j, log ‖x i‖⁻¹ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a0 := by
    rw [ha0def]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [Real.log_inv]
    exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) (hx1 i).le)
  have hcont : ContinuousOn (fun ζ : ℂ => u (x + ζ • ej j)) (closedBall 0 r \ ↑({-x j} : Finset ℂ)) := by
    have hmaps : Set.MapsTo (fun ζ : ℂ => x + ζ • ej j) (closedBall 0 r \ ↑({-x j} : Finset ℂ))
        (U \ coordDiv S) := by
      intro ζ hζ
      exact hgood ζ hζ.1 (fun h => hζ.2 (by simp [h]))
    have hcf : Continuous (fun ζ : ℂ => x + ζ • ej j) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact ContinuousOn.comp (g := u) (f := fun ζ : ℂ => x + ζ • ej j) hc hcf.continuousOn hmaps
  have hgrow : ∀ ε > 0, ∀ T : ℝ, ∃ η > 0, ∀ e ∈ ({-x j} : Finset ℂ),
      ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑({-x j} : Finset ℂ),
      dist ζ e < η → u (x + ζ • ej j) + ε * log ‖ζ - e‖ < T := by
    intro ε hε T
    obtain ⟨Y, hY⟩ := loglog_bound C a0 ε T hε ha0
    refine ⟨exp (-(max Y 0 + 1)), exp_pos _, ?_⟩
    intro e he ζ hζ hdist
    rw [Finset.mem_singleton] at he
    subst he
    have hne : ζ ≠ -x j := fun h => hζ.2 (by simp [h])
    have hpos : 0 < ‖ζ - -x j‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    rw [dist_eq_norm] at hdist
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = log ‖ζ - -x j‖⁻¹ := ⟨_, rfl⟩
    have hylog : log ‖ζ - -x j‖ = -y := by rw [hy, Real.log_inv, neg_neg]
    have hyY : max Y 0 + 1 ≤ y := by
      have h1 := Real.log_lt_log hpos hdist
      rw [Real.log_exp] at h1
      linarith
    have hsum : ∑ i ∈ S, log ‖(x + ζ • ej j) i‖⁻¹ = y + a0 := by
      rw [← Finset.add_sum_erase S _ hj]
      congr 1
      · rw [line_coord, if_pos rfl, hy, sub_neg_eq_add, add_comm]
      · rw [ha0def]
        apply Finset.sum_congr rfl
        intro i hi
        rw [line_coord, if_neg (Finset.ne_of_mem_erase hi), add_zero]
    have hgz := hg _ (hgood ζ hζ.1 hne)
    rw [hsum] at hgz
    have h1 := hY y (by linarith [le_max_left Y 0]) (by linarith [le_max_right Y 0])
    have h2 : exp 1 + (y + a0) = exp 1 + a0 + y := by ring
    rw [h2] at hgz
    rw [hylog]
    linarith
  have hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑({-x j} : Finset ℂ) →
      u (x + a • ej j) ≤ circleAverage (fun ζ => u (x + ζ • ej j)) a s := by
    intro a s hs hs2
    refine (psh_line hpsh x (ej j) hs (fun ζ hζ => ?_)).2
    have h1 := hs2 hζ
    exact hgood ζ (ball_subset_closedBall h1.1) (fun h => h1.2 (by simp [h]))
  have hF0 : (0 : ℂ) ∉ ({-x j} : Finset ℂ) := by
    rw [Finset.mem_singleton]
    intro h
    exact hxi j hj (by linear_combination h)
  have hFr : ∀ f ∈ ({-x j} : Finset ℂ), f ∈ ball (0 : ℂ) r := by
    intro f hf
    rw [Finset.mem_singleton] at hf
    subst hf
    rw [mem_ball, dist_zero_right, norm_neg]
    exact hxj
  have hmean := smg2 hr hF0 hFr hcont hgrow hsub
  have hcs : ContinuousOn (fun ζ : ℂ => u (x + ζ • ej j)) (sphere 0 r) := by
    refine hcont.mono (fun ζ hζ => ⟨sphere_subset_closedBall hζ, fun h => ?_⟩)
    have h1 : ζ = -x j := by simpa using h
    rw [mem_sphere, dist_zero_right, h1, norm_neg] at hζ
    linarith
  obtain ⟨ζ, hζ, hle⟩ := exists_sphere_ge hr hcs hmean
  exact ⟨ζ, hζ, by simpa only [zero_smul, add_zero] using hle⟩

end partA

end

section
open ReciprocityTheory.AnForm.A

variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C : ℝ}

theorem local_bound (hU : IsOpen U) (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹))
    {p : Fin D → ℂ} (hp : p ∈ U) : ∃ ρ > 0, ∃ M, ∀ z ∈ ball p ρ \ coordDiv S, u z ≤ M := by
  classical
  obtain ⟨R, hR0, hRU⟩ := Metric.isOpen_iff.1 hU p hp
  have e0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  have e1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < R / 2 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (half_pos hR0))
  have e2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i ∈ S, p i ≠ 0 → r < ‖p i‖ / 4 := by
    rw [Filter.eventually_all_finset]
    intro i _
    by_cases h0 : p i = 0
    · exact Filter.Eventually.of_forall (fun _ h => absurd h0 h)
    · have h4 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ‖p i‖ / 4 :=
        nhdsWithin_le_nhds (eventually_lt_nhds (div_pos (norm_pos_iff.2 h0) (by norm_num : (0 : ℝ) < 4)))
      exact h4.mono (fun _ h _ => h)
  obtain ⟨r, hr0, hrR, hrp⟩ := (e0.and (e1.and e2)).exists
  set L : Set (Fin D → ℂ) := closedBall p (3 * r / 2) ∩ ⋂ i ∈ S, {y | r / 2 ≤ ‖y i‖} with hL
  have hLc : IsCompact L := (isCompact_closedBall p _).inter_right
    (isClosed_biInter fun i _ => isClosed_le continuous_const (continuous_apply i).norm)
  have hLsub : L ⊆ U \ coordDiv S := by
    intro y hy
    refine ⟨hRU ?_, ?_⟩
    · have h1 := hy.1
      rw [mem_closedBall] at h1
      rw [mem_ball]
      linarith
    · rintro ⟨i, hi, hyi⟩
      have h1 := Set.mem_iInter₂.1 hy.2 i hi
      simp only [Set.mem_setOf_eq, hyi, norm_zero] at h1
      linarith
  obtain ⟨Mb, hMb⟩ := hLc.bddAbove_image (hc.mono hLsub)
  refine ⟨r / 2, half_pos hr0, Mb, ?_⟩
  have key : ∀ F : Finset (Fin D), (∀ i ∈ F, i ∈ S ∧ p i = 0) → ∀ x : Fin D → ℂ, x ∉ coordDiv S →
      (∀ i, dist (x i) (p i) < 3 * r / 2) → (∀ i ∈ S, p i = 0 → i ∉ F → r / 2 < ‖x i‖) →
      (∀ i ∈ F, ‖x i‖ < r / 2) → ∃ y ∈ L, u x ≤ u y := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _ x _ hxd hxm _
      refine ⟨x, ⟨?_, ?_⟩, le_rfl⟩
      · rw [mem_closedBall, dist_pi_le_iff (by linarith)]
        exact fun i => (hxd i).le
      · refine Set.mem_iInter₂.2 fun i hi => ?_
        show r / 2 ≤ ‖x i‖
        by_cases h0 : p i = 0
        · exact (hxm i hi h0 (by simp)).le
        · have h1 := hrp i hi h0
          have h2 := hxd i
          rw [dist_eq_norm] at h2
          have h3 := norm_sub_norm_le (p i) (x i)
          rw [norm_sub_rev] at h3
          linarith
    | @insert j F hjF ih =>
      intro hF x hxS hxd hxm hxF
      have hj := hF j (Finset.mem_insert_self j F)
      have hxj : ‖x j‖ < r / 2 := hxF j (Finset.mem_insert_self j F)
      have hdisc : ∀ ζ ∈ closedBall (0 : ℂ) r, x + ζ • ej j ∈ U := by
        intro ζ hζ
        rw [mem_closedBall, dist_zero_right] at hζ
        apply hRU
        rw [mem_ball, dist_pi_lt_iff hR0]
        intro i
        rw [line_coord, dist_eq_norm]
        split_ifs with hij
        · subst hij
          rw [hj.2, sub_zero]
          exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)
        · rw [add_zero, ← dist_eq_norm]
          linarith [hxd i]
      obtain ⟨ζ, hζ, hle⟩ := slice_step hU1 hc hpsh hg hj.1 hr0 hxS (by linarith) hdisc
      rw [mem_sphere, dist_zero_right] at hζ
      have hnew : r / 2 < ‖x j + ζ‖ := by
        have h1 := norm_sub_norm_le ζ (-(x j))
        rw [norm_neg, sub_neg_eq_add, add_comm] at h1
        linarith
      have hS' : x + ζ • ej j ∉ coordDiv S := by
        rintro ⟨i, hi, h0⟩
        rw [line_coord] at h0
        split_ifs at h0 with hij
        · subst hij
          rw [h0, norm_zero] at hnew
          linarith
        · rw [add_zero] at h0
          exact hxS ⟨i, hi, h0⟩
      have hd' : ∀ i, dist ((x + ζ • ej j) i) (p i) < 3 * r / 2 := by
        intro i
        rw [line_coord]
        split_ifs with hij
        · subst hij
          rw [hj.2, dist_zero_right]
          exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)
        · rw [add_zero]
          exact hxd i
      have hm' : ∀ i ∈ S, p i = 0 → i ∉ F → r / 2 < ‖(x + ζ • ej j) i‖ := by
        intro i hi h0 hiF
        rw [line_coord]
        split_ifs with hij
        · subst hij
          exact hnew
        · rw [add_zero]
          exact hxm i hi h0 (by simp [hij, hiF])
      have hF' : ∀ i ∈ F, ‖(x + ζ • ej j) i‖ < r / 2 := by
        intro i hi
        have hij : i ≠ j := fun h => hjF (h ▸ hi)
        rw [line_coord, if_neg hij, add_zero]
        exact hxF i (Finset.mem_insert_of_mem hi)
      obtain ⟨y, hyL, hy⟩ := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)) (x + ζ • ej j)
        hS' hd' hm' hF'
      exact ⟨y, hyL, hle.trans hy⟩
  intro z ⟨hzb, hzS⟩
  rw [mem_ball, dist_pi_lt_iff (half_pos hr0)] at hzb
  have hd : ∀ i, dist (z i) (p i) < 3 * r / 2 := fun i => by linarith [hzb i]
  have hm : ∀ i ∈ S, p i = 0 → i ∉ S.filter (fun i => p i = 0) → r / 2 < ‖z i‖ :=
    fun i hi h0 hiT => absurd (Finset.mem_filter.2 ⟨hi, h0⟩) hiT
  have hF : ∀ i ∈ S.filter (fun i => p i = 0), ‖z i‖ < r / 2 := by
    intro i hi
    have h1 := hzb i
    rw [(Finset.mem_filter.1 hi).2, dist_zero_right] at h1
    exact h1
  obtain ⟨y, hyL, hy⟩ := key (S.filter (fun i => p i = 0)) (fun i hi => Finset.mem_filter.1 hi) z hzS hd hm hF
  exact hy.trans (hMb ⟨y, hyL, rfl⟩)

theorem part_a (hU : IsOpen U) (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹)) :
    ∀ K : Set (Fin D → ℂ), IsCompact K → K ⊆ U → BddAbove (u '' (K \ coordDiv S)) := by
  intro K hK hKU
  choose! ρ hρ M hM using fun p (hp : p ∈ U) => local_bound hU hU1 hc hpsh hg hp
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : K => ball (p : Fin D → ℂ) (ρ p))
    (fun _ => isOpen_ball)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hρ z (hKU hz))⟩)
  refine ⟨∑ p ∈ t, |M p|, ?_⟩
  rintro _ ⟨z, ⟨hzK, hzS⟩, rfl⟩
  obtain ⟨p, hpt, hzp⟩ : ∃ p ∈ t, z ∈ ball (p : Fin D → ℂ) (ρ p) := by
    simpa only [Set.mem_iUnion, exists_prop] using ht hzK
  have h1 := hM p (hKU p.2) z ⟨hzp, hzS⟩
  have h2 : |M p| ≤ ∑ q ∈ t, |M q| := Finset.single_le_sum (f := fun q : K => |M (q : Fin D → ℂ)|) (fun q _ => abs_nonneg _) hpt
  exact h1.trans ((le_abs_self _).trans h2)

end

section
theorem ii_of_bdd {f : ℝ → ℝ} (hf : Measurable f) (B : ℝ) (hB : ∀ θ, |f θ| ≤ B) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := B)).mono_fun hf.aestronglyMeasurable ?_
  exact ae_of_all _ (fun θ => by
    simp only [Real.norm_eq_abs]
    exact (hB θ).trans (le_abs_self B))

theorem avg_lim {E X : Type*} [TopologicalSpace E] {ψ : E → ℝ} {U K : Set E}
    (hψ : UpperSemicontinuousOn ψ U) (hKU : K ⊆ U) {m M : ℝ} (hm : ∀ y ∈ K, m ≤ ψ y)
    (hM : ∀ y ∈ K, ψ y ≤ M) {l : Filter X} [l.IsCountablyGenerated] (P : X → ℝ → E)
    (P0 : ℝ → E) (hPc : ∀ᶠ x in l, Continuous (P x)) (hP0c : Continuous P0)
    (hPK : ∀ᶠ x in l, ∀ θ, P x θ ∈ K) (hP0K : ∀ θ, P0 θ ∈ K)
    (hlim : ∀ θ, Tendsto (fun x => P x θ) l (𝓝 (P0 θ))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∫ θ in (0 : ℝ)..2 * π, ψ (P x θ) ≤ (∫ θ in (0 : ℝ)..2 * π, ψ (P0 θ)) + ε := by
  have usc_comp : ∀ Q : ℝ → E, Continuous Q → (∀ θ, Q θ ∈ K) →
      UpperSemicontinuous (fun θ => ψ (Q θ)) := by
    intro Q hQ hQK θ y hy
    have h1 : Tendsto Q (𝓝 θ) (𝓝[U] (Q θ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hQ.tendsto θ, Filter.Eventually.of_forall (fun θ' => hKU (hQK θ'))⟩
    exact h1.eventually (hψ (Q θ) (hKU (hQK θ)) y hy)
  have bnd : ∀ y ∈ K, |ψ y| ≤ |m| + |M| := by
    intro y hy
    rw [abs_le]
    have h1 := hm y hy
    have h2 := hM y hy
    have h3 := neg_abs_le m
    have h4 := le_abs_self M
    have h5 := abs_nonneg m
    have h6 := abs_nonneg M
    constructor <;> linarith
  have meas0 : Measurable (fun θ => ψ (P0 θ)) := (usc_comp P0 hP0c hP0K).measurable
  have bndG : ∀ x, (∀ θ, P x θ ∈ K) → ∀ θ, |max (ψ (P x θ)) (ψ (P0 θ))| ≤ |m| + |M| := by
    intro x hxK θ
    rw [abs_le]
    have h1 := abs_le.1 (bnd _ (hxK θ))
    have h2 := abs_le.1 (bnd _ (hP0K θ))
    exact ⟨le_trans h1.1 (le_max_left _ _), max_le h1.2 h2.2⟩
  have hlimG : ∀ θ, Tendsto (fun x => max (ψ (P x θ)) (ψ (P0 θ))) l (𝓝 (ψ (P0 θ))) := by
    intro θ
    rw [tendsto_order]
    refine ⟨fun a ha => Filter.Eventually.of_forall (fun x => lt_of_lt_of_le ha (le_max_right _ _)),
      fun b hb => ?_⟩
    have h1 : Tendsto (fun x => P x θ) l (𝓝[U] (P0 θ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim θ, hPK.mono (fun x hx => hKU (hx θ))⟩
    filter_upwards [h1.eventually (hψ (P0 θ) (hKU (hP0K θ)) b hb)] with x hx
    exact max_lt hx hb
  have hT : Tendsto (fun x => ∫ θ in (0 : ℝ)..2 * π, max (ψ (P x θ)) (ψ (P0 θ))) l
      (𝓝 (∫ θ in (0 : ℝ)..2 * π, ψ (P0 θ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => |m| + |M|)
    · filter_upwards [hPc, hPK] with x hx hxK
      exact ((usc_comp (P x) hx hxK).measurable.max meas0).aestronglyMeasurable
    · filter_upwards [hPK] with x hxK
      exact Filter.Eventually.of_forall (fun θ _ => by
        rw [Real.norm_eq_abs]
        exact bndG x hxK θ)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun θ _ => hlimG θ)
  have hev := (tendsto_order.1 hT).2 _ (lt_add_of_pos_right _ hε)
  filter_upwards [hev, hPc, hPK] with x hx hxc hxK
  have hmeas := (usc_comp (P x) hxc hxK).measurable
  have hIF : IntervalIntegrable (fun θ => ψ (P x θ)) volume 0 (2 * π) :=
    ii_of_bdd hmeas (|m| + |M|) (fun θ => bnd _ (hxK θ)) 0 (2 * π)
  have hIG : IntervalIntegrable (fun θ => max (ψ (P x θ)) (ψ (P0 θ))) volume 0 (2 * π) :=
    ii_of_bdd (hmeas.max meas0) (|m| + |M|) (bndG x hxK) 0 (2 * π)
  have hle : ∫ θ in (0 : ℝ)..2 * π, ψ (P x θ) ≤ ∫ θ in (0 : ℝ)..2 * π, max (ψ (P x θ)) (ψ (P0 θ)) :=
    intervalIntegral.integral_mono_on (by positivity) hIF hIG (fun θ _ => le_max_left _ _)
  exact le_trans hle hx.le

end

end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
end
