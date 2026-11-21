import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermFiniteProjection

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem eventually_eq_zero_of_lines {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hl : ∀ v : Fin d → ℂ, ∀ᶠ t in 𝓝 (0 : ℂ), h (a + t • v) = 0) :
    ∀ᶠ y in 𝓝 a, h y = 0 := by
  obtain ⟨r, hr, han⟩ := ha.exists_ball_analyticOnNhd
  filter_upwards [Metric.ball_mem_nhds a hr] with y hy
  by_cases hv : y - a = 0
  · have hya : y = a := sub_eq_zero.1 hv
    have h0 := (hl 0).self_of_nhds
    simpa [hya] using h0
  have hvpos : 0 < ‖y - a‖ := norm_pos_iff.2 hv
  have hmaps : ∀ t ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖), a + t • (y - a) ∈ Metric.ball a r := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hvpos] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact ht
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => h (a + t • (y - a))) (Metric.ball (0 : ℂ) (r / ‖y - a‖)) := by
    intro t ht
    have h1 : AnalyticAt ℂ (fun t : ℂ => a + t • (y - a)) t := by fun_prop
    exact AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • (y - a)) (han _ (hmaps t ht)) h1
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖) := by
    rw [Metric.mem_ball, dist_zero_right, norm_one, one_lt_div hvpos, ← dist_eq_norm]
    exact hy
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖) := Metric.mem_ball_self (div_pos hr hvpos)
  have hz := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) _).isPreconnected h0
    (by filter_upwards [hl (y - a)] with t ht using ht) h1
  simpa using hz

theorem exists_line_eventually_ne_zero {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hne : ¬ ∀ᶠ y in 𝓝 a, h y = 0) :
    ∃ v : Fin d → ℂ, ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (a + t • v) ≠ 0 := by
  by_contra hcon
  refine hne (eventually_eq_zero_of_lines ha fun v => ?_)
  have h1 : AnalyticAt ℂ (fun t : ℂ => a + t • v) 0 := by fun_prop
  have ha' : AnalyticAt ℂ h (a + (0 : ℂ) • v) := by simpa using ha
  rcases (AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • v) ha' h1).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · exact h0
  · exact absurd ⟨v, h0⟩ hcon

theorem exists_proj_fibres_line {d : ℕ} (v : Fin d → ℂ) (hv : v ≠ 0) :
    ∃ π : (Fin d → ℂ) →L[ℂ] (Fin (d - 1) → ℂ), ∀ y y', π y = π y' → ∃ t : ℂ, y = y' + t • v := by
  have hrank : Module.finrank ℂ ((Fin d → ℂ) ⧸ (ℂ ∙ v)) = Module.finrank ℂ (Fin (d - 1) → ℂ) := by
    have h1 := Submodule.finrank_quotient_add_finrank (ℂ ∙ v)
    rw [finrank_span_singleton hv, Module.finrank_fin_fun] at h1
    rw [Module.finrank_fin_fun]
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hrank
  refine ⟨LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ (ℂ ∙ v).mkQ), fun y y' hyy => ?_⟩
  have hq : (ℂ ∙ v).mkQ y = (ℂ ∙ v).mkQ y' := e.injective hyy
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_span_singleton] at hq
  obtain ⟨t, ht⟩ := hq
  exact ⟨t, by rw [ht]; abel⟩

theorem GermFiniteProjection.proof : GermFiniteProjection.Statement := by
  intro σ _ X w _ hirr
  classical
  have hw : w ∈ X := hirr.1
  have hP : ∃ d : ℕ, ∃ A : (σ → ℂ) →L[ℂ] (Fin d → ℂ), ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w := by
    let e : (σ → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card σ) → ℂ) :=
      LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm
    exact ⟨Fintype.card σ, LinearMap.toContinuousLinearMap e.toLinearMap, Set.univ, univ_mem,
      fun x _ hx => e.injective hx⟩
  obtain ⟨A, W, hW, hAW⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, A, ⟨W, hW, hAW⟩, fun h hh hXh => ?_⟩
  by_contra hne
  have hAw : h (A w) = 0 := hXh.self_of_nhds hw
  obtain ⟨v, hv⟩ := exists_line_eventually_ne_zero hh hne
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hv.exists
    simp [hAw] at ht
  have hd : Nat.find hP - 1 < Nat.find hP := by
    have : 0 < Nat.find hP := Nat.pos_of_ne_zero fun h0 => hv0 (funext fun i => (Fin.cast h0 i).elim0)
    omega
  obtain ⟨π, hπ⟩ := exists_proj_fibres_line v hv0
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhdsWithin_iff.1 hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hcont : ∀ᶠ x in 𝓝 w, A x ∈ Metric.ball (A w) (ε * ‖v‖) :=
    A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (mul_pos hε hvpos))
  refine Nat.find_min hP hd ⟨π.comp A, W ∩ {x | (x ∈ X → h (A x) = 0) ∧ A x ∈ Metric.ball (A w) (ε * ‖v‖)},
    inter_mem hW (hXh.and hcont), ?_⟩
  rintro x ⟨hxX, hxW, hxh, hxb⟩ hπx
  apply hAW x ⟨hxX, hxW⟩
  obtain ⟨t, ht⟩ := hπ (A x) (A w) hπx
  by_cases ht0 : t = 0
  · simpa [ht0] using ht
  exfalso
  have htε : t ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    have hb : ‖t • v‖ < ε * ‖v‖ := by
      rw [Metric.mem_ball, dist_eq_norm, ht, add_sub_cancel_left] at hxb
      exact hxb
    rw [norm_smul] at hb
    exact lt_of_mul_lt_mul_right hb hvpos.le
  exact hεv ⟨htε, ht0⟩ (by rw [← ht]; exact hxh hxX)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

theorem analyticAt_det_fderiv {k : ℕ} {f : (Fin k → ℂ) → Fin k → ℂ} {x : Fin k → ℂ}
    (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) x := by
  have hd : AnalyticAt ℂ (fderiv ℂ f) x := hf.fderiv
  have he : ∀ i j : Fin k, AnalyticAt ℂ (fun z => fderiv ℂ f z (Pi.single j 1) i) x := by
    intro i j
    let L : ((Fin k → ℂ) →L[ℂ] Fin k → ℂ) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).comp
        (ContinuousLinearMap.apply ℂ (Fin k → ℂ) (Pi.single j 1))
    show AnalyticAt ℂ (L ∘ fderiv ℂ f) x
    exact (L.analyticAt _).comp hd
  have heq : (fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) =
      fun z => ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, fderiv ℂ f z (Pi.single i 1) (σ i) := by
    funext z
    rw [← LinearMap.det_toMatrix', Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  rw [heq]
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)

theorem exists_zero_ne_near {k : ℕ} (hk : 2 ≤ k) {J : (Fin k → ℂ) → ℂ} {c : Fin k → ℂ}
    (hJ : AnalyticAt ℂ J c) (hc : J c = 0) {W : Set (Fin k → ℂ)} (hW : W ∈ 𝓝 c) :
    ∃ z ∈ W, z ≠ c ∧ J z = 0 := by
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  by_cases h0 : ∀ᶠ y in 𝓝 c, J y = 0
  · have h1 : ∀ᶠ y in 𝓝[≠] c, y ∈ W ∧ J y = 0 := nhdsWithin_le_nhds (Filter.inter_mem hW h0)
    obtain ⟨y, ⟨hyW, hy0⟩, hyc⟩ := (h1.and self_mem_nhdsWithin).exists
    exact ⟨y, hyW, hyc, hy0⟩
  obtain ⟨v, hv⟩ := exists_line_eventually_ne_zero hJ h0
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hv.exists
    simp [hc] at ht

  obtain ⟨u, -, hu⟩ : ∃ u ∈ (⊤ : Submodule ℂ (Fin k → ℂ)), u ∉ ℂ ∙ v := by
    refine SetLike.exists_of_lt (lt_top_iff_ne_top.2 fun htop => ?_)
    have h1 := finrank_span_singleton (K := ℂ) hv0
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨R, hR, han⟩ := hJ.exists_ball_analyticOnNhd
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
  set ρ := min R ε with hρ
  have hρ0 : 0 < ρ := lt_min hR hε
  obtain ⟨δ, hδ, hδv⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hv)
  set r := min (δ / 2) (ρ / (2 * (‖v‖ + 1))) with hr
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hrv : r * ‖v‖ < ρ / 2 := by
    have h1 : r ≤ ρ / (2 * (‖v‖ + 1)) := min_le_right _ _
    have h2 : r * ‖v‖ ≤ ρ / (2 * (‖v‖ + 1)) * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h3 : ρ / (2 * (‖v‖ + 1)) * ‖v‖ < ρ / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg v]
    linarith

  have hmem : ∀ s t : ℂ, ‖s • u‖ < ρ / 2 → ‖t‖ ≤ r → c + s • u + t • v ∈ ball c ρ := by
    intro s t hs ht
    rw [mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
    calc ‖s • u + t • v‖ ≤ ‖s • u‖ + ‖t‖ * ‖v‖ := (norm_add_le _ _).trans (le_of_eq (by rw [norm_smul t v]))
      _ < ρ / 2 + ρ / 2 := add_lt_add_of_lt_of_le hs (by nlinarith [norm_nonneg v])
      _ = ρ := by ring
  have hballR : ball c ρ ⊆ ball c R := ball_subset_ball (min_le_left _ _)

  have hK : IsCompact (sphere (0 : ℂ) r) := isCompact_sphere 0 r
  have hKne : (sphere (0 : ℂ) r).Nonempty := NormedSpace.sphere_nonempty.2 hr0.le
  have hcontJ : ∀ p ∈ ball c ρ, ContinuousAt J p := fun p hp => (han p (hballR hp)).continuousAt
  have hF0 : ∀ t ∈ sphere (0 : ℂ) r, J (c + t • v) ≠ 0 := by
    intro t ht
    have htn : ‖t‖ = r := by simpa using ht
    refine hδv (by simpa [dist_eq_norm, htn] using hrδ) (by rintro rfl; simp at htn; linarith)
  have hline : ∀ t : ℂ, ‖t‖ ≤ r → c + t • v ∈ ball c ρ := by
    intro t ht
    have h1 := hmem 0 t (by rw [zero_smul, norm_zero]; exact half_pos hρ0) ht
    rwa [zero_smul, add_zero] at h1
  have hcontK : ContinuousOn (fun t : ℂ => ‖J (c + t • v)‖) (sphere 0 r) := by
    intro t ht
    have hp := hline t (mem_sphere_zero_iff_norm.1 ht).le
    exact (ContinuousAt.comp (f := fun t : ℂ => c + t • v) (hcontJ _ hp) (by fun_prop)).norm.continuousWithinAt
  obtain ⟨t0, ht0K, ht0min⟩ := hK.exists_isMinOn hKne hcontK
  set m := ‖J (c + t0 • v)‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (hF0 t0 ht0K)

  have hcirc : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ t ∈ sphere (0 : ℂ) r, m / 2 < ‖J (c + s • u + t • v)‖ := by
    refine hK.eventually_forall_of_forall_eventually fun t ht => ?_
    have htr : ‖t‖ ≤ r := (mem_sphere_zero_iff_norm.1 ht).le
    have hcont : ContinuousAt (fun p : ℂ × ℂ => J (c + p.1 • u + p.2 • v)) (0, t) := by
      refine ContinuousAt.comp (f := fun p : ℂ × ℂ => c + p.1 • u + p.2 • v) ?_ (by fun_prop)
      exact hcontJ _ (hmem 0 t (by simpa using half_pos hρ0) htr)
    have hle : ‖J (c + t0 • v)‖ ≤ ‖J (c + t • v)‖ := isMinOn_iff.1 ht0min t ht
    exact hcont.norm.eventually (lt_mem_nhds (by simp only [zero_smul, add_zero]; linarith))
  have hcen : ∀ᶠ s in 𝓝 (0 : ℂ), ‖J (c + s • u)‖ < m / 2 := by
    have hcont : ContinuousAt (fun s : ℂ => J (c + s • u)) 0 :=
      ContinuousAt.comp (f := fun s : ℂ => c + s • u) (by simpa using hcontJ c (mem_ball_self hρ0))
        (by fun_prop)
    have h1 : ‖J (c + (0 : ℂ) • u)‖ < m / 2 := by simpa [hc] using half_pos hm0
    exact hcont.norm.eventually (gt_mem_nhds h1)
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s • u‖ < ρ / 2 := by
    have hcont : ContinuousAt (fun s : ℂ => ‖s • u‖) 0 := by fun_prop
    exact hcont.eventually (gt_mem_nhds (by simpa using half_pos hρ0))
  obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, hs0⟩ :=
    ((((hcirc.and hcen).and hsmall).filter_mono (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))).and
      (self_mem_nhdsWithin (s := {(0 : ℂ)}ᶜ))).exists

  obtain ⟨t, ht, htz⟩ : ∃ t ∈ closedBall (0 : ℂ) r, J (c + s • u + t • v) = 0 := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hdiff : DifferentiableOn ℂ (fun t : ℂ => (J (c + s • u + t • v))⁻¹) (closedBall 0 r) := by
      intro t ht
      have htr : ‖t‖ ≤ r := by simpa using ht
      have hp := hmem s t hs3 htr
      have hJd : DifferentiableAt ℂ J (c + s • u + t • v) := (han _ (hballR hp)).differentiableAt
      have hcomp : DifferentiableAt ℂ (fun t : ℂ => J (c + s • u + t • v)) t :=
        hJd.comp t (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => c + s • u + t • v) t)
      exact (hcomp.inv (hne t ht)).differentiableWithinAt
    have hdc : DiffContOnCl ℂ (fun t : ℂ => (J (c + s • u + t • v))⁻¹) (ball 0 r) :=
      hdiff.diffContOnCl_ball subset_rfl
    have hbd := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc (C := (m / 2)⁻¹)
      (fun t ht => by
        rw [frontier_ball 0 hr0.ne'] at ht
        rw [norm_inv]
        exact inv_anti₀ (half_pos hm0) (hs1 t ht).le)
      (subset_closure (mem_ball_self hr0))
    have hJs : J (c + s • u) ≠ 0 := by simpa using hne 0 (mem_closedBall_self hr0.le)
    simp only [zero_smul, add_zero, norm_inv] at hbd
    have := inv_lt_inv₀ (half_pos hm0) (norm_pos_iff.2 hJs) |>.2 hs2
    linarith
  refine ⟨c + s • u + t • v, hεW ?_, ?_, htz⟩
  · exact ball_subset_ball (min_le_right R ε) (hmem s t hs3 (by simpa using ht))
  · intro heq
    apply hu
    have h1 : s • u = -(t • v) := by
      have : s • u + t • v = 0 := by
        have := congrArg (· - c) heq
        simpa [add_assoc] using this
      exact eq_neg_of_add_eq_zero_left this
    have hs : s ≠ 0 := by simpa using hs0
    rw [Submodule.mem_span_singleton]
    refine ⟨-(s⁻¹ * t), ?_⟩
    calc -(s⁻¹ * t) • v = s⁻¹ • (-(t • v)) := by rw [smul_neg, smul_smul, neg_smul]
      _ = s⁻¹ • (s • u) := by rw [h1]
      _ = u := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
