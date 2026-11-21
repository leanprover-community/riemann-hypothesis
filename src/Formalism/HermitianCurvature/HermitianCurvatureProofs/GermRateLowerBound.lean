import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizePtG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableBlockIntegrand
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceIntCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.YGSlice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCongrRight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbGermRateLowBOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizeToStd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOmBlock

section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory Filter

noncomputable section

theorem bump_annulus {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h12 : r₁ ≤ r₂) :
    ∃ χD : ℂ → ℂ, U.IsCutC χD ∧ (∀ w : ℂ, r₁ ≤ ‖w‖ → ‖w‖ ≤ r₂ → χD w = 1) ∧
      (∀ w ∈ tsupport χD, ‖w‖ ≤ 2 * r₂) := by
  let bo : ContDiffBump (0 : ℂ) := ⟨r₂, 2 * r₂, by linarith, by linarith⟩
  let bi : ContDiffBump (0 : ℂ) := ⟨r₁ / 4, r₁ / 2, by linarith, by linarith⟩
  have hsupp : tsupport (fun w : ℂ => (((1 - bi w) * bo w : ℝ) : ℂ)) ⊆ Metric.closedBall 0 (2 * r₂) := by
    refine (tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero _).trans ?_
    refine (tsupport_mul_subset_right).trans ?_
    rw [bo.tsupport_eq]
  refine ⟨fun w => (((1 - bi w) * bo w : ℝ) : ℂ), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.sub bi.contDiff).mul bo.contDiff)
  · have h := (bo.hasCompactSupport.mul_left (f := fun w : ℂ => 1 - bi w)).comp_left Complex.ofReal_zero
    exact h
  · intro h0
    have hnb : ∀ᶠ w in nhds (0 : ℂ), (((1 - bi w) * bo w : ℝ) : ℂ) = 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by linarith : (0 : ℝ) < r₁ / 4)] with w hw
      have : bi w = 1 := bi.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)
      simp [this]
    exact (notMem_tsupport_iff_eventuallyEq.2 hnb) h0
  · intro w hw1 hw2
    have ho : bo w = 1 := bo.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using hw2)
    have hi : bi w = 0 := bi.zero_of_le_dist (by
      show r₁ / 2 ≤ dist w 0
      rw [dist_zero_right]; linarith)
    simp [ho, hi]
  · intro w hw
    have := hsupp hw
    simpa [Metric.mem_closedBall, dist_zero_right] using this

theorem isLocPt_ptG {h' : C.LPt} (hh' : D.IsLocPt h' (D.ptSize h')) {m : ℕ} {Kc : Set ℂ} (hK0 : (0 : ℂ) ∉ Kc)
    {q : (ℂ × ℂ) ⊕ ℂ} (hq : okG m Kc q) : D.IsLocPt (ptG h' m q) (D.ptSize h' + (m + 2)) := by
  refine ⟨?_, ptSize_ptG h' m q⟩
  rcases q with ⟨t, c⟩ | z
  · obtain ⟨ht, hc⟩ := hq
    have hc0 : c ≠ 0 := by
      rintro rfl; simp at hc; exact hK0 hc
    intro b hb
    simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | rfl | rfl
    · exact hh'.1 b hb
    · exact ⟨by omega, ht⟩
    · exact ⟨le_rfl, hc0⟩
  · obtain ⟨D, hD, hz⟩ := hq
    have hz0 : z ≠ 0 := by
      rintro rfl
      have h0 : ((-1 : ℂ) ^ (m + 3)) * D = 0 := by rw [← hz]; simp
      have : D = 0 := (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ (by norm_num))
      exact hK0 (this ▸ hD)
    intro b hb
    simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | rfl
    · exact hh'.1 b hb
    · exact ⟨by omega, hz0⟩

theorem arith_ma (m RR As a : ℝ) (hm : 0 ≤ m) (hR : m + 3 ≤ RR) (hAs : 1 ≤ As)
    (ha : 128 * RR ^ 3 * As ≤ a) : (m + 1) * (m + 4) < a := by
  have hR1 : 1 ≤ RR := by linarith
  have h1 : (m + 1) * (m + 4) < (m + 3) ^ 2 := by nlinarith
  have h2 : (m + 3) ^ 2 ≤ RR ^ 2 := pow_le_pow_left₀ (by linarith) hR 2
  have h3 : RR ^ 2 ≤ RR ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
  have h4 : RR ^ 3 ≤ 128 * RR ^ 3 * As := by
    have : 0 ≤ RR ^ 3 := by positivity
    nlinarith
  linarith


theorem cccoef_congr {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k ρ Wp Wq} {A : ℝ} {mm : ℕ} {ε : ℝ}
    {F F' : B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV k ρ, F g = F' g) (hF : JC.CCCoefM Bs A mm ε F) :
    JC.CCCoefM Bs A mm ε F' := by
  obtain ⟨h1, ⟨c, hc⟩, h3⟩ := hF
  exact ⟨Formalism.FourierDecayAlt.P.Ux1.ckOn_congr h h1, ⟨c, Formalism.FourierDecayAlt.P.Ux1.cc_congr h hc⟩,
    fun g hg hne => h3 g hg (by rwa [h g hg])⟩

theorem sliceAt_apply {k r : ℕ} {ι : Type} [Fintype ι] {E0 : Type} [NormedAddCommGroup E0] [NormedSpace ℂ E0]
    [CompleteSpace E0] (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → (ι → E0)) (p : C.LPt)
    (hle : D.ptSize p ≤ r) (γ : B.Mat k (r - D.ptSize p)) (e : ι)
    (hint : Integrable (fun ξ : U.Xi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar k (r - D.ptSize p) (D.ptPerm p) (D.castV (by omega) z) (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p))) :
    D.sliceAt k r z z' F p γ e = D.sliceAt k r z z' (fun g => F g e) p γ := by
  unfold D.sliceAt
  rw [dif_pos hle, dif_pos hle]
  unfold U.PhiFun
  have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E0) e).integral_comp_comm hint
  exact this.symm ▸ rfl

set_option maxHeartbeats 1000000 in
theorem germPlace_of (hSI : SliceIntCut) (hYG : YGSlice) (hFM : FormModel) : GermPlace := by
  intro Wp Wq _ _ _ _ _ _ P0 T sg w f χ ε h' m i hi hsz hf hfR hχ hε hk2 hh' Kc hKc hK0
  classical

  set ph := D.ptSize h' with hph
  set ρ := P0.r - i with hρ
  have e1 : P0.r = ph + (m + 2) + ρ := by omega
  have e2 : ph + (m + 2) + ρ = P0.r := by omega
  have hj1 : 1 ≤ ph + (m + 2) := by omega
  have hi1 : 1 ≤ i := by omega
  set N := w.length with hN
  set z0 := D.castV e1 T.base.z with hz0
  set z0' := D.castV e1 T.base.z' with hz0'
  set f1 := D.castF e2 f with hf1

  have hLD := fun e : Wd.Ix (Fin N) =>
    Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD P0.k (ph + (m + 2)) ρ Wp Wq z0 z0' (by omega) w e hj1
  choose Θ hΘ hΘF using hLD
  have hFrel : ∀ e : Wd.Ix (Fin N), ∀ g ∈ B.GV P0.k (ph + (m + 2) + ρ), U.DjU P0.k (ph + (m + 2)) ρ g ≠ 0 →
      D.castF e2 (D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e) g =
        B.opApply (Θ e) (fun x => ((χ (Formalism.QuantumDeterminants.Gf P0.k (ph + (m + 2) + ρ) z0 z0' x / ε) : ℝ) : ℂ) • f1 x) g := by
    intro e g hg hD
    have hFc : B.CkOn ⊤ (B.GV P0.k P0.r) (D.cutF T.base χ f ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hf ε
    have h1 : D.castF e2 (D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e) =
        D.uwG P0.k (ph + (m + 2) + ρ) z0 z0' (D.castF e2 (D.cutF T.base χ f ε)) (ph + (m + 2)) (by omega) w e := by
      rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ (by omega) _ _ w e
    rw [h1, hΘF e _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]

  set σ := D.ptPerm h' with hσ
  set d := D.ptDiag h' with hd_def
  have hd : ∀ q, d q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h' hh'.1 q q.2
  set dh := (U.hMat σ d).det with hdh_def
  have hdh : dh ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd
  set wd := (G.wMat (m + 1)).det with hwd_def
  have hwd : wd ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (m + 1)

  obtain ⟨r1, hr1, hKr1⟩ : ∃ r1 : ℝ, 0 < r1 ∧ ∀ D ∈ Kc, r1 ≤ ‖D‖ := by
    rcases Kc.eq_empty_or_nonempty with hE | hne
    · exact ⟨1, one_pos, by simp [hE]⟩
    · obtain ⟨D0, hD0, hmin⟩ := hKc.exists_isMinOn hne continuous_norm.continuousOn
      refine ⟨‖D0‖, norm_pos_iff.2 (fun h0 => hK0 (h0 ▸ hD0)), fun D hD => hmin hD⟩
  obtain ⟨r2, hKr2⟩ : ∃ r2 : ℝ, ∀ D ∈ Kc, ‖D‖ ≤ r2 := hKc.isBounded.exists_norm_le
  set cdw : ℝ := ‖dh * wd‖ with hcdw
  have hcdw0 : 0 < cdw := norm_pos_iff.2 (mul_ne_zero hdh hwd)
  set A1 : ℝ := cdw * r1 / 2 with hA1
  set A2 : ℝ := cdw * max r1 r2 * 2 with hA2
  have hA1p : 0 < A1 := by positivity
  have hA12 : A1 ≤ A2 := by
    have : r1 ≤ max r1 r2 := le_max_left _ _
    have : cdw * r1 ≤ cdw * max r1 r2 := mul_le_mul_of_nonneg_left this hcdw0.le
    rw [hA1, hA2]; nlinarith
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := bump_annulus hA1p hA12
  have hKj : ∀ D ∈ Kc, A1 < ‖dh * (wd * D)‖ ∧ ‖dh * (wd * D)‖ < A2 := by
    intro D hD
    have e : ‖dh * (wd * D)‖ = cdw * ‖D‖ := by rw [← mul_assoc, norm_mul]
    rw [e]
    have h1 := hKr1 D hD
    have h2 : ‖D‖ ≤ max r1 r2 := (hKr2 D hD).trans (le_max_right _ _)
    constructor
    · rw [hA1]; nlinarith
    · rw [hA2]
      have : 0 < max r1 r2 := lt_of_lt_of_le hr1 (le_max_left _ _)
      nlinarith
  have hA2p : 0 < A2 := lt_of_lt_of_le hA1p hA12
  obtain ⟨δ, hδ, hχε⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.isCutG_scale hχ hε
  set ε'' : ℝ := δ * ε / (2 * A2) ^ 2 with hε''def
  have hε'' : 0 < ε'' := by positivity

  obtain ⟨C₂, CcG, hUG⟩ := Formalism.FourierDecayAlt.P.germ_expansion_applies
  obtain ⟨CcU, hCU⟩ := Formalism.FourierDecayAlt.P.corollary_u2_germ_hypothesis 127 C₂
  set nd : ℕ := 2 * P0.r + P0.k + 1 with hnd
  set X : ℕ := N * nd ^ 2 + nd ^ 3 with hX
  set o : ℕ := N * (ph + (m + 2)) with ho
  set κ : ℕ := N * (ph + (m + 2)) + N * (ph + (m + 2)) ^ 2 with hκ
  set mmB : ℕ := P5.mmUser P0 N + (5 + (2 * (P0.r - i) + P0.k + 1) * N) with hmmB
  set As : ℕ := (11 * X + 5) + o + (κ + (ph + (m + 1 + 1)) * o) + mmB +
    (2 * (ph + (m + 1 + 1) + ρ) + P0.k + 1) ^ 3 + (C₂ * (ph + (m + 1 + 1) + ρ + 1) ^ 2 + 1) with hAs
  let UD : U.UData P0.k ph (m + 1 + 1) ρ Wp Wq (Wd.Ix (Fin N)) :=
    ⟨σ, d, z0, z0', Θ, χD, fun x => χ (ε⁻¹ * x), δ * ε, ε'', o, κ, 0, mmB, As⟩
  have hOk : UD.Ok C₂ := by
    refine ⟨hd, by omega, Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem,
      Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem, fun e => hΘ e, hχD, hχε, hε'', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have h2 := hχDs x hx
      have h3 : ‖x‖ ^ 2 ≤ (2 * A2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      calc ε'' * ‖x‖ ^ 2 ≤ ε'' * (2 * A2) ^ 2 := mul_le_mul_of_nonneg_left h3 hε''.le
        _ = δ * ε := by
          have : (2 * A2) ^ 2 ≠ 0 := by positivity
          rw [hε''def, div_mul_cancel₀ _ this]
    · show o ≤ As; omega
    · show κ + (ph + (m + 1 + 1)) * o ≤ As; omega
    · show ((0 : ℝ)) ≤ (As : ℝ); positivity
    · show mmB ≤ As; omega
    · show (2 * (ph + (m + 1 + 1) + ρ) + P0.k + 1) ^ 3 ≤ As; omega
    · show C₂ * (ph + (m + 1 + 1) + ρ + 1) ^ 2 + 1 ≤ As; omega

  set RR : ℝ := ((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1 with hRR
  have hRR1 : 1 ≤ RR := by rw [hRR]; have : (0 : ℝ) ≤ ((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
  set R4 : ℝ := RR ^ 4 * (As : ℝ) with hR4
  have hR40 : 0 ≤ R4 := by positivity
  set A₀ : ℝ := (|CcG| + |CcU|) * R4 with hA₀def
  have hA₀G : CcG * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) ≤ A₀ := by
    have e : CcG * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) = CcG * R4 := by
      show _ = CcG * (RR ^ 4 * (As : ℝ)); rw [hRR]; ring
    rw [e, hA₀def]
    calc CcG * R4 ≤ |CcG| * R4 := mul_le_mul_of_nonneg_right (le_abs_self _) hR40
      _ ≤ (|CcG| + |CcU|) * R4 := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg CcU]) hR40
  have hA₀U : CcU * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) ≤ A₀ := by
    have e : CcU * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) = CcU * R4 := by
      show _ = CcU * (RR ^ 4 * (As : ℝ)); rw [hRR]; ring
    rw [e, hA₀def]
    calc CcU * R4 ≤ |CcU| * R4 := mul_le_mul_of_nonneg_right (le_abs_self _) hR40
      _ ≤ (|CcG| + |CcU|) * R4 := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg CcG]) hR40
  obtain ⟨Rf, hRf⟩ := hfR
  have hf1s : B.CkOn ⊤ (B.GV P0.k (ph + (m + 1 + 1) + ρ)) f1 := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hf
  have hf1c : ∀ (A : ℝ) (mm : ℕ), B.InCC A mm f1 := by
    intro A mm
    refine Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hf1s (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P0.k _ Rf) (fun g hg hgC => ?_) A mm
    by_contra hne
    apply hgC
    have h1 := hRf _ (Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hg) hne
    rwa [Formalism.FourierDecayAlt.P.PBE.gN_castM] at h1
  obtain ⟨c, hc⟩ := hf1c A₀ (3 * UD.As)

  obtain ⟨V, indexVFirst, indexVSecond, hVc, ⟨MM⟩⟩ :=
    Formalism.FourierDecayAlt.P.compactly_supported_banach_model P0.k ρ (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) (UD.a C₂ A₀) UD.mmB UD.S
  letI := indexVFirst; letI := indexVSecond; haveI := hVc
  obtain ⟨-, hKg⟩ := hUG P0.k ph m ρ Wp Wq (Wd.Ix (Fin N)) UD hOk A₀ hA₀G
  obtain ⟨Cst, hCst⟩ := hKg Kc hKc hK0
  obtain ⟨Φ, hΦev, hΦg⟩ := hCst f1 c hc V MM
  obtain ⟨ha1, -, -, Cd, hCd⟩ := hCU P0.k ph (m + 1 + 1) ρ Wp Wq (Wd.Ix (Fin N)) UD hOk A₀ hA₀U
  obtain ⟨Φ', hΦ'ev, hΦ'reg⟩ := hCd f1 c hc V MM
  have hΦΦ' : ∀ Z : G.Mat (m + 1 + 1), G.detM Z ≠ 0 → Φ Z = Φ' Z := by
    intro Z hZ
    have h0 : ∀ γ ∈ B.GV P0.k ρ, (fun _ : B.Mat P0.k ρ => (0 : Wd.Ix (Fin N) → (Wq →L[ℂ] Wp))) γ =
        MM.ev (Φ Z - Φ' Z) γ := by
      intro γ hγ
      rw [map_sub, Pi.sub_apply, hΦev Z hZ γ hγ, hΦ'ev Z hZ γ hγ, sub_self]
    have hcc := Formalism.FourierDecayAlt.P.Ux1.cc_congr h0 (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (A := UD.a C₂ A₀) (m := UD.mmB))
    have := MM.least _ 0 hcc
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

  have hAs1 : (1 : ℝ) ≤ (As : ℝ) := by
    have : 1 ≤ As := by omega
    exact_mod_cast this
  have ha128 : 128 * RR ^ 3 * (As : ℝ) ≤ UD.a C₂ A₀ := by
    have h := ha1
    rw [hRR]; norm_num at h ⊢; exact h
  have hRm : (m : ℝ) + 3 ≤ RR := by
    rw [hRR]; push_cast
    have : (0 : ℝ) ≤ (ph : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (ρ : ℝ) := Nat.cast_nonneg _
    linarith
  have hma : ((m : ℝ) + 1) * ((m : ℝ) + 4) < UD.a C₂ A₀ := arith_ma _ _ _ _ (Nat.cast_nonneg m) hRm hAs1 ha128
  have hRr : RR = (P0.r : ℝ) + 1 := by rw [hRR, e2]
  have hAa : P5.Auser P0 N + 1 ≤ UD.a C₂ A₀ := by
    have hX1 : ((11 * X + 5 : ℕ) : ℝ) ≤ (As : ℝ) := by
      have : 11 * X + 5 ≤ As := by omega
      exact_mod_cast this
    have hXr : ((N : ℝ) * (P5.nV P0 : ℝ) ^ 2 + (P5.nV P0 : ℝ) ^ 3) = (X : ℝ) := by
      rw [hX, hnd]; simp [P5.nV]
    unfold P5.Auser
    rw [hXr, ← hRr]
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
    push_cast at hX1
    have hR3 : 1 ≤ RR ^ 3 := one_le_pow₀ hRR1
    nlinarith
  have hdetc : IsOpen {Z : G.Mat (m + 1 + 1) | G.detM Z ≠ 0} := by
    refine isOpen_ne_fun ?_ continuous_const
    unfold G.detM
    exact Continuous.matrix_det (continuous_id (X := Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ))
  have hdec : ∀ Z : G.Mat (m + 1 + 1), G.detM Z ≠ 0 → ContinuousAt Φ Z ∧ ‖Φ Z‖ ≤ (Cd * c) * (1 + ‖Z‖) ^ (-UD.a C₂ A₀) := by
    intro Z hZ
    have hev : Φ =ᶠ[nhds Z] Φ' := by
      filter_upwards [hdetc.mem_nhds hZ] with Z' hZ' using hΦΦ' Z' hZ'
    refine ⟨(hΦ'reg Z hZ).1.continuousAt.congr hev.symm, ?_⟩
    have h := (hΦ'reg Z hZ).2 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    rw [hΦΦ' Z hZ]
    exact h

  have hLex : ∀ γ ∈ B.GV P0.k ρ, ∃ L : V →L[ℂ] (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)), ∀ v, L v = MM.ev v γ := by
    intro γ hγ
    have hgN : 0 < B.gN γ ^ UD.a C₂ A₀ := Real.rpow_pos_of_pos (Formalism.FourierDecayAlt.P.Ux1.gN_pos hγ) _
    let L₀ : V →ₗ[ℂ] (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : B.Mat P0.k ρ => Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) γ) ∘ₗ MM.ev
    have hbd : ∀ v, ‖L₀ v‖ ≤ (B.gN γ ^ UD.a C₂ A₀)⁻¹ * ‖v‖ := by
      intro v
      have h1 := (MM.mem v).2 [] [] (by simp) (by simp) (by simp) γ hγ
      rw [inv_mul_eq_div, le_div_iff₀' hgN]
      exact h1
    exact ⟨L₀.mkContinuous _ hbd, fun v => rfl⟩

  set Fι : B.Mat P0.k P0.r → (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) :=
    fun g e => D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e g with hFι
  have hO : IsOpen {x : B.Mat P0.k (ph + (m + 1 + 1) + ρ) |
      A1 < ‖U.DjU P0.k (ph + (m + 1 + 1)) ρ x‖ ∧ ‖U.DjU P0.k (ph + (m + 1 + 1)) ρ x‖ < A2} := by
    have hc := (Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU P0.k (ph + (m + 1 + 1)) ρ).norm
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hread : ∀ γ ∈ B.GV P0.k ρ, ∀ Z : G.Mat (m + 1 + 1), G.detM Z ≠ 0 →
      G.detM Z ∈ (fun D => wd * D) '' Kc →
      MM.ev (Φ Z) γ = U.PhiFun P0.k ρ σ d (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e1.symm Fι) Z γ := by
    intro γ hγ Z hZ hZK
    obtain ⟨D0, hD0, hZD⟩ := hZK
    rw [hΦev Z hZ γ hγ]
    unfold U.UData.Phi U.PhiFun
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    congr 1
    funext e
    have hg := Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ Z hZ hγ
    have hDj : U.DjU P0.k (ph + (m + 1 + 1)) ρ (U.gaXi P0.k ρ σ d ξ Z γ) = dh * (wd * D0) := by
      rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, ← hZD]
    have hb := hKj D0 hD0
    rw [← hDj] at hb
    have hDj0 : U.DjU P0.k (ph + (m + 1 + 1)) ρ (U.gaXi P0.k ρ σ d ξ Z γ) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hb; linarith [hb.1]
    have hF := hFrel e _ hg hDj0
    simp only [U.UData.F1]
    refine (Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open (Θ e) hO (fun x hx => ?_) _ hb).trans hF.symm
    show (χD (U.DjU P0.k (ph + (m + 1 + 1)) ρ x) *
      ((χ (ε⁻¹ * Formalism.QuantumDeterminants.Gf P0.k (ph + (m + 1 + 1) + ρ) z0 z0' x) : ℝ) : ℂ)) • f1 x = _
    rw [hχD1 _ hx.1.le hx.2.le, one_mul, div_eq_inv_mul]

  have hev_slv : ∀ q, okG m Kc q → ∀ γ ∈ B.GV P0.k ρ, ∀ e,
      MM.ev (yG U.betaU m Φ q) γ e =
        KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q) (by rw [ptSize_ptG, hsz]) e γ := by
    intro q hq γ hγ e
    obtain ⟨L, hL⟩ := hLex γ hγ
    have hloc : D.IsLocPt (ptG h' m q) i := hsz ▸ isLocPt_ptG hh' hK0 hq
    have hle : D.ptSize (ptG h' m q) ≤ P0.r := by rw [ptSize_ptG]; omega
    have hγ' : D.castM (by rw [ptSize_ptG]; omega : ρ = P0.r - D.ptSize (ptG h' m q)) γ ∈
        B.GV P0.k (P0.r - D.ptSize (ptG h' m q)) := Formalism.FourierDecayAlt.P.PBE.castM_GV _ hγ
    have hint : Integrable (fun ξ : U.Xi P0.k (D.ptSize (ptG h' m q)) 0 (P0.r - D.ptSize (ptG h' m q))
          (D.ptPerm (ptG h' m q)) =>
        U.psiStar P0.k (P0.r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q))
          (D.castV (by rw [ptSize_ptG]; omega) T.base.z) (D.castV (by rw [ptSize_ptG]; omega) T.base.z') ξ •
          D.castF (by rw [ptSize_ptG]; omega) Fι
            (U.gaXi P0.k (P0.r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.ptDiag (ptG h' m q)) ξ
              (fun a => a.elim0) (D.castM (by rw [ptSize_ptG]; omega) γ)))
        (U.muXi P0.k (D.ptSize (ptG h' m q)) 0 (P0.r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q))) := by
      refine integrable_pi_iff.2 fun e' => ?_
      exact hSI Wp Wq P0 T w f χ ε i hi hi1 hk2 hf ⟨Rf, hRf⟩ hχ hε _ hloc e' _ hγ'
    have hY := hYG P0.k P0.r (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) T.base.z T.base.z' Fι h' m ρ e1 V Φ L γ Kc
      (Cd * c) (UD.a C₂ A₀) hh' hK0 hma hdec
      (fun Z hZ hZK => by rw [hL]; exact hread γ hγ Z hZ hZK) q hq hint
    rw [← hL, hY, sliceAt_apply _ _ _ _ hle _ e hint]
    rfl

  have hz1 : U.lowV P0.k (ph + (m + 1 + 1)) ρ z0 = (T.bs i).z := by
    have hzl : T.base.z = D.castV (by omega) (Formalism.QuantumDeterminants.liftVec P0.k i (P0.r - i) (T.bs i).z) := (T.z_lev i hi).symm
    rw [hz0, hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec (by omega) _ _
  have hz1' : U.lowV P0.k (ph + (m + 1 + 1)) ρ z0' = (T.bs i).z' := by
    have hzl : T.base.z' = D.castV (by omega) (Formalism.QuantumDeterminants.liftVec P0.k i (P0.r - i) (T.bs i).z') := (T.z'_lev i hi).symm
    rw [hz0', hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec (by omega) _ _
  have hSg : ∀ γ ∈ UD.S, ε'' ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - i) (T.bs i).z (T.bs i).z' γ := by
    intro γ hγ
    have h := hγ
    simp only [U.UData.S, Set.mem_ofPred_eq] at h
    rw [← hz1, ← hz1']
    exact h
  obtain ⟨Bf, Cp, hCp0, hBf, hBfx⟩ := hFM Wp Wq P0 T sg ⟨i, by omega⟩ w (UD.a C₂ A₀) UD.mmB ε'' UD.S hε''
    hAa (by show P5.mmUser P0 N ≤ mmB; omega) (by show 5 + (2 * (P0.r - i) + P0.k + 1) * N ≤ mmB; omega) hSg V MM
  have hcls : ∀ (v : V) (e : Wd.Ix (Fin N)),
      JC.CCCoefM (T.bs i) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (fun γ => MM.ev v γ e) := by
    intro v e
    have h1 : B.CCle (UD.a C₂ A₀) UD.mmB (fun γ => MM.ev v γ e) ‖v‖ := ccle_comp (MM.mem v) e
    have h2 : B.CCle (P5.Auser P0 N + 1) UD.mmB (fun γ => MM.ev v γ e) ‖v‖ :=
      Formalism.FourierDecayAlt.P.compactly_supported_monotone P0.k ρ _ (UD.a C₂ A₀) _ ‖v‖ UD.mmB _ hAa h1
    have h3 : B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (fun γ => MM.ev v γ e) ‖v‖ :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by show P5.mmUser P0 N ≤ mmB; omega) h2
    refine ⟨h3.1, ⟨_, h3⟩, fun γ hγ hne => ?_⟩
    have hS : γ ∈ UD.S := by
      by_contra hn
      apply hne
      show MM.ev v γ e = 0
      rw [MM.off v γ hγ hn]
      rfl
    exact hSg γ hS
  have hform : ∀ q1 q2, okG m Kc q1 → okG m Kc q2 →
      D.formLev T sg ⟨i, by omega⟩ w
        (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q1) (by rw [ptSize_ptG, hsz]))
        (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q2) (by rw [ptSize_ptG, hsz])) =
      Bf (yG U.betaU m Φ q1) (yG U.betaU m Φ q2) := by
    intro q1 q2 hq1 hq2
    refine (hBfx _ _ _ _ ε'' hε'' (fun e => ?_) (fun e => ?_) (fun e γ hγ => hev_slv q1 hq1 γ hγ e)
      (fun e γ hγ => hev_slv q2 hq2 γ hγ e)).symm
    · exact cccoef_congr (fun γ hγ => hev_slv q1 hq1 γ hγ e) (hcls _ e)
    · exact cccoef_congr (fun γ hγ => hev_slv q2 hq2 γ hγ e) (hcls _ e)
  exact ⟨V, indexVFirst, indexVSecond, hVc, Bf, Φ, Cp, Cst * c, hCp0, hBf, hform, fun t D ht hD => hΦg t D ht hD⟩

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory NumberField

noncomputable section

theorem isLocalPoint_to_standard (r : ℕ) (g : ℝ) (hg : 0 < g) :
    ∀ (b : ℕ) (P : C.LPt), (∀ x ∈ P, 1 ≤ x.1 ∧ x.2 ≠ 0) → ∀ x ∈ D.toStd r g b P, 1 ≤ x.1 ∧ x.2 ≠ 0
  | _, [] => by simp [D.toStd]
  | b, (s, t) :: rest => by
    intro h x hx
    simp only [D.toStd, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have h1 := h (s, t) (by simp)
      refine ⟨h1.1, ?_⟩
      have hq : (0 : ℝ) < g / (2 * Real.pi) := div_pos hg (by positivity)
      refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ Complex.I_ne_zero)) h1.2
      exact Complex.ofReal_ne_zero.mpr (zpow_pos hq _).ne'
    · exact isLocalPoint_to_standard r g hg (b + s) rest (fun y hy => h y (by simp [hy])) x hx

theorem isLocPt_toStd (r : ℕ) (g : ℝ) (hg : 0 < g) (P : C.LPt) (i : ℕ) (hP : D.IsLocPt P i) :
    D.IsLocPt (D.toStd r g 1 P) i :=
  ⟨isLocalPoint_to_standard r g hg 1 P hP.1, by rw [ptSize_toStd]; exact hP.2⟩

theorem weight_product_append (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) :
    ∀ (b : ℕ) (P Q : C.LPt), C.nAux k r GG fr b (P ++ Q) = C.nAux k r GG fr b P * C.nAux k r GG fr (b + D.ptSize P) Q
  | b, [], Q => by simp [C.nAux, D.ptSize]
  | b, (s, t) :: rest, Q => by
    simp only [List.cons_append, C.nAux]
    rw [weight_product_append k r GG fr (b + s) rest Q, ← mul_assoc]
    have e : b + D.ptSize ((s, t) :: rest) = b + s + D.ptSize rest := by
      simp only [D.ptSize, List.map_cons, List.sum_cons]; ring
    rw [e]

theorem weight_product_germ_indep (k r : ℕ) (GG GG' : ℝ) (fr : ℕ → ℕ → ℝ) :
    ∀ (b : ℕ) (P : C.LPt), b + D.ptSize P ≤ r + 1 → C.nAux k r GG fr b P = C.nAux k r GG' fr b P
  | b, [], _ => by simp [C.nAux]
  | b, (s, t) :: rest, h => by
    simp only [C.nAux]
    have hs : D.ptSize ((s, t) :: rest) = s + D.ptSize rest := by simp [D.ptSize]
    rw [hs] at h
    have hc : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by omega
    rw [if_neg hc, if_neg hc, weight_product_germ_indep k r GG GG' fr (b + s) rest (by omega)]

theorem bSt_append (κ : ℝ) (P Q : C.LPt) : D.bSt κ (P ++ Q) = D.bSt κ P * D.bSt κ Q := by
  simp [D.bSt, List.map_append, List.prod_append]

theorem norm_fs (r : ℕ) (g : ℝ) (hg : 0 < g) (b s : ℕ) (t : ℂ) :
    ‖GermFibreKernels.fs r g b s t‖ = (g / (2 * Real.pi)) ^ S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) * ‖t‖ := by
  unfold GermFibreKernels.fs
  have hq : (0 : ℝ) < g / (2 * Real.pi) := div_pos hg (by positivity)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zpow_pos hq _)]

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem sizeAt_nonneg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) : 0 ≤ S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  exact List.prod_nonneg fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact abs_nonneg _

theorem rd_pos' : 0 < S6.rd E := GermRealisation.rd_pos E

theorem gamLev_nonneg (S : C.HidaSetting E Wp Wq) (i : ℕ) :
    0 ≤ D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i := by
  have hrd := (rd_pos' (E := E)).le
  have hg : (0 : ℝ) ≤ (S.g : ℝ) := Nat.cast_nonneg _
  unfold D.GamLev
  refine Finset.prod_nonneg fun l _ => div_nonneg (zpow_nonneg ?_ _) ?_
  · unfold D.kapG; positivity
  · unfold D.deG; positivity

theorem gamLev_zero (S : C.HidaSetting E Wp Wq) (i : ℕ) (hi : i ≤ S.G.r) (hg : (S.g : ℝ) = 0) :
    D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i = 0 := by
  unfold D.GamLev
  refine Finset.prod_eq_zero (i := S.G.r + 1) (by simp; omega) ?_
  simp [D.deG, hg]

theorem gNSetC_main (S : C.HidaSetting E Wp Wq) [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (i : ℕ)
    (hi : i ≤ S.G.r) (a : List C.Letter) (P Q : C.LPt) (hP : D.IsLocPt P i) (hQ : D.IsLocPt Q i) :
    KB.gN (PBL.setC S p F) v ε i a P Q =
      ((lamP S v a i P * lamP S v a i Q : ℝ) : ℂ) *
        D.formLev (p v).T (M.sgn (D.parOf S v) (p v).l0) ⟨i, by have e : (D.parOf S v).r = S.G.r := rfl; omega⟩ a
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 P) (by
            rw [← hP.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 P))
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 Q) (by
            rw [← hQ.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 Q)) := by
  have hsz : 0 ≤ S.sizeAt v a := sizeAt_nonneg S v a
  have hΓ := gamLev_nonneg S i
  have e1 : KB.gN (PBL.setC S p F) v ε i a P Q =
      ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G P) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G Q) : ℝ) : ℂ) *
        PBL.rrC S p F v ε i a P Q / (S.sizeAt v a : ℂ) := rfl
  rw [e1]
  unfold PBL.rrC KB.Pl.RR lamP
  set Γ := D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i with hΓdef
  set bP := D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P
  set bQ := D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) Q
  set nP := C.nLoc S.G.k S.G.r S.fr (S.pd v).G P
  set nQ := C.nLoc S.G.k S.G.r S.fr (S.pd v).G Q
  set sz := S.sizeAt v a
  have hsq : √(Γ * sz) * √(Γ * sz) = Γ * sz := Real.mul_self_sqrt (mul_nonneg hΓ hsz)
  have hcoef : √nP / (bP * √(Γ * sz)) * (√nQ / (bQ * √(Γ * sz))) = √nP * √nQ * (1 / (bP * bQ * Γ)) / sz := by
    rw [div_mul_div_comm, show bP * √(Γ * sz) * (bQ * √(Γ * sz)) = bP * bQ * (√(Γ * sz) * √(Γ * sz)) by ring, hsq]
    field_simp
  rcases eq_or_lt_of_le (Nat.cast_nonneg (S.g) : (0 : ℝ) ≤ (S.g : ℝ)) with hg | hg
  · have h0 : Γ = 0 := gamLev_zero S i hi hg.symm
    simp [h0]
  · have hP' := isLocPt_toStd S.G.r (S.g : ℝ) hg P i hP
    have hQ' := isLocPt_toStd S.G.r (S.g : ℝ) hg Q i hQ
    unfold D.RRplace
    rw [dif_pos ⟨hP', hQ'⟩, dif_pos hi, hcoef]
    unfold KB.slv
    push_cast
    ring

theorem gNSetC : GNSetC := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p F v ε i hi a P Q hP hQ
  exact gNSetC_main S p F v ε i hi a P Q hP hQ

end loc

def betaZ (κ : ℝ) (N : ℤ) : ℝ := ∏ x ∈ Finset.Ico 1 N, (κ ^ (1 - 2 * x) / Real.pi) ^ (N - x)

theorem bSt_cons (κ : ℝ) (n : ℕ) (t : ℂ) (P : C.LPt) : D.bSt κ ((n, t) :: P) = betaZ κ n * D.bSt κ P := by
  simp [D.bSt, betaZ]

theorem bSt_nil (κ : ℝ) : D.bSt κ [] = 1 := by simp [D.bSt]

theorem betaZ_one (κ : ℝ) : betaZ κ 1 = 1 := by simp [betaZ]

theorem prod_Ico_int_succ (f : ℤ → ℝ) (a b : ℤ) (h : a ≤ b) :
    ∏ x ∈ Finset.Ico a (b + 1), f x = (∏ x ∈ Finset.Ico a b, f x) * f b := by
  rw [Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_insert_right h, Finset.prod_insert (by simp), mul_comm]

theorem betaZ_succ (κ : ℝ) (hκ : κ ≠ 0) (n : ℕ) :
    betaZ κ ((n : ℤ) + 1) = betaZ κ n * ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) := by
  unfold betaZ
  have hc : ∀ x : ℤ, κ ^ (1 - 2 * x) / Real.pi ≠ 0 := fun x => div_ne_zero (zpow_ne_zero _ hκ) Real.pi_ne_zero
  have e : ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) ^ ((n : ℤ) + 1 - x) =
      ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), ((κ ^ (1 - 2 * x) / Real.pi) ^ ((n : ℤ) - x) * (κ ^ (1 - 2 * x) / Real.pi)) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← zpow_add_one₀ (hc x)]; congr 1; ring
  rw [e, Finset.prod_mul_distrib]
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [prod_Ico_int_succ _ _ _ (by omega), sub_self, zpow_zero, mul_one]

theorem prod_c (κ : ℝ) (hκ : κ ≠ 0) : ∀ n : ℕ,
    ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) = κ ^ (-((n : ℤ) ^ 2)) / Real.pi ^ n
  | 0 => by simp
  | n + 1 => by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 = ((n : ℤ) + 1) + 1 by push_cast; ring, prod_Ico_int_succ _ _ _ (by omega),
      prod_c κ hκ n, div_mul_div_comm, ← zpow_add₀ hκ, pow_succ]
    congr 2
    push_cast; ring

theorem betaZ_succ' (κ : ℝ) (hκ : κ ≠ 0) (n : ℕ) :
    betaZ κ ((n : ℤ) + 1) = betaZ κ n * (κ ^ (-((n : ℤ) ^ 2)) / Real.pi ^ n) := by
  rw [betaZ_succ κ hκ, prod_c κ hκ]

theorem sqrt_zpow_two_mul (y : ℝ) (hy : 0 ≤ y) (a b : ℤ) : √(y ^ (2 * a * b)) = y ^ (a * b) := by
  rw [show 2 * a * b = (a * b) * 2 by ring, zpow_mul, zpow_two, Real.sqrt_mul_self (zpow_nonneg hy _)]

theorem bSt_pos_loc (κ : ℝ) (hκ : 0 < κ) (p : C.LPt) : 0 < D.bSt κ p := by
  unfold D.bSt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
  exact Finset.prod_pos fun m _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _

theorem weight_product_nonneg (k r : ℕ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 ≤ fr b s) :
    ∀ (b : ℕ) (P : C.LPt), 0 ≤ C.nAux k r 0 fr b P
  | _, [] => by simp [C.nAux]
  | b, (s, t) :: rest => by
    simp only [C.nAux]
    refine mul_nonneg ?_ (weight_product_nonneg k r fr hfr (b + s) rest)
    split_ifs
    · rcases Nat.eq_zero_or_pos (k - 1) with h | h
      · rw [h]; simp
      · rw [zero_pow h.ne']
    · exact zpow_nonneg (mul_nonneg (hfr _ _) (norm_nonneg _)) _

theorem betaZ_pos (κ : ℝ) (hκ : 0 < κ) (N : ℤ) : 0 < betaZ κ N :=
  Finset.prod_pos fun _ _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _

section loc2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem lambdaValue_append_two (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (b0 m : ℕ) (hi : b0 + m + 2 ≤ S.G.r)
    (h : C.LPt) (hh : D.ptSize h = b0) (t c : ℂ) :
    lamP S v a (b0 + m + 2) (h ++ [(m + 1, t), (1, c)]) =
      √(C.nAux S.G.k S.G.r 0 S.fr 1 h) /
          (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) h *
            √(D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) (b0 + m + 2) *
              S.sizeAt v a)) *
        ((S.fr (1 + b0) (m + 1) * ‖t‖) ^ (((m + 1 : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + b0 + (m + 1) - 1) + ((m + 1 : ℕ) : ℤ) - 3)) *
          (S.fr (1 + b0 + (m + 1)) 1 * ‖c‖) ^ (((1 : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + b0 + (m + 1) + 1 - 1) + ((1 : ℕ) : ℤ) - 3)) /
          (betaZ (D.kapG (S.g : ℝ) (S6.rd E)) ((m + 1 : ℕ) : ℤ) * betaZ (D.kapG (S.g : ℝ) (S6.rd E)) ((1 : ℕ) : ℤ))) := by
  have hfr : ∀ b s, 0 ≤ S.fr b s := fun b s => by unfold C.HidaSetting.fr; exact Real.rpow_nonneg (rd_pos' (E := E)).le _
  unfold lamP C.nLoc
  have hsz : D.ptSize (h ++ [(m + 1, t), (1, c)]) = b0 + m + 2 := by
    simp [D.ptSize, List.map_append, List.sum_append] at hh ⊢; omega
  rw [weight_product_germ_indep S.G.k S.G.r _ 0 S.fr 1 _ (by omega), weight_product_append, hh]
  simp only [C.nAux, mul_one]
  rw [bSt_append, bSt_cons, bSt_cons, bSt_nil, mul_one]
  split_ifs with H1 H2 <;> first | (exfalso; omega) | (exfalso; simp only [and_true] at *; omega) | skip
  rw [Real.sqrt_mul (weight_product_nonneg _ _ _ hfr _ _), Real.sqrt_mul (zpow_nonneg (mul_nonneg (hfr _ _) (norm_nonneg t)) _),
    sqrt_zpow_two_mul _ (mul_nonneg (hfr _ _) (norm_nonneg t)), sqrt_zpow_two_mul _ (mul_nonneg (hfr _ _) (norm_nonneg c))]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem lambdaMap_one_eq_zero (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (b0 m : ℕ) (hi : b0 + m + 2 ≤ S.G.r)
    (h : C.LPt) (hh : D.ptSize h = b0) (z : ℂ) :
    lamP S v a (b0 + m + 2) (h ++ [(m + 2, z)]) =
      √(C.nAux S.G.k S.G.r 0 S.fr 1 h) /
          (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) h *
            √(D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) (b0 + m + 2) *
              S.sizeAt v a)) *
        ((S.fr (1 + b0) (m + 2) * ‖z‖) ^ (((m + 2 : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + b0 + (m + 2) - 1) + ((m + 2 : ℕ) : ℤ) - 3)) /
          betaZ (D.kapG (S.g : ℝ) (S6.rd E)) ((m + 2 : ℕ) : ℤ)) := by
  have hfr : ∀ b s, 0 ≤ S.fr b s := fun b s => by unfold C.HidaSetting.fr; exact Real.rpow_nonneg (rd_pos' (E := E)).le _
  unfold lamP C.nLoc
  have hsz : D.ptSize (h ++ [(m + 2, z)]) = b0 + m + 2 := by
    simp [D.ptSize, List.map_append, List.sum_append] at hh ⊢; omega
  rw [weight_product_germ_indep S.G.k S.G.r _ 0 S.fr 1 _ (by omega), weight_product_append, hh]
  simp only [C.nAux, mul_one]
  rw [bSt_append, bSt_cons, bSt_nil, mul_one]
  split_ifs with H1 <;> first | (exfalso; omega) | (exfalso; simp only [and_true] at *; omega) | skip
  rw [Real.sqrt_mul (weight_product_nonneg _ _ _ hfr _ _), sqrt_zpow_two_mul _ (mul_nonneg (hfr _ _) (norm_nonneg z))]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem germConst : GermConst := by
  intro E _ _ _ Wp Wq _ _ _ _ S v a b s hg1 hg2 hb hs hi h hh
  obtain ⟨b0, rfl⟩ : ∃ b0, b = b0 + 1 := ⟨b - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have ei : b0 + 1 + (m + 2) - 1 = b0 + m + 2 := by omega
  have es1 : m + 2 - 1 = m + 1 := by omega
  have es2 : m + 2 - 2 = m := by omega
  have eh : b0 + 1 - 1 = b0 := by omega
  rw [eh] at hh
  rw [ei] at hi ⊢
  simp only [es1, es2]
  obtain ⟨ρ, hρ⟩ : ∃ ρ, S.G.r = b0 + m + 2 + ρ := ⟨S.G.r - (b0 + m + 2), by omega⟩
  have eρ : S.G.r - (b0 + m + 2) = ρ := by omega
  rw [eρ]
  have hgpos : (0 : ℝ) < (S.g : ℝ) := by unfold C.HidaSetting.g; exact_mod_cast Nat.mul_pos hg1 hg2
  simp only [lambdaValue_append_two S v a b0 m hi h hh, lambdaMap_one_eq_zero S v a b0 m hi h hh, norm_fs _ _ hgpos, norm_mul, norm_pow,
    norm_inv, KB.dlB]
  have n1 : 1 + b0 + (m + 1) - 1 = b0 + m + 1 := by omega
  have n2 : 1 + b0 + (m + 1) + 1 - 1 = b0 + m + 2 := by omega
  have n3 : 1 + b0 + (m + 2) - 1 = b0 + m + 2 := by omega
  have n4 : 1 + b0 + (m + 1) = b0 + m + 2 := by omega
  have n5 : U.Mlev S.G.k ρ - 2 = S.G.k + 2 * ρ + 1 := by simp only [U.Mlev]; omega
  have hκ : D.kapG (S.g : ℝ) (S6.rd E) = ((S.g : ℝ) / (2 * Real.pi) * S6.rd E)⁻¹ := by
    unfold D.kapG; field_simp
  have hrd : 0 < S6.rd E := rd_pos' (E := E)
  have hκ0 : D.kapG (S.g : ℝ) (S6.rd E) ≠ 0 := by rw [hκ]; positivity
  rw [show ((m + 2 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring, betaZ_succ' _ hκ0 (m + 1)]
  simp only [n1, n2, n3, n4, n5, Nat.cast_one, betaZ_one, mul_one, C.HidaSetting.fr]
  set Hf := √(C.nAux S.G.k S.G.r 0 S.fr 1 h) /
      (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) h *
        √(D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) (b0 + m + 2) * S.sizeAt v a))
    with hHf
  clear_value Hf
  have hB1 := betaZ_pos _ (show 0 < D.kapG (S.g : ℝ) (S6.rd E) by rw [hκ]; positivity) ((m + 1 : ℕ) : ℤ)
  set B1 := betaZ (D.kapG (S.g : ℝ) (S6.rd E)) ((m + 1 : ℕ) : ℤ) with hB1d
  clear_value B1
  rw [hκ]
  have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
  set δ := D.deG (S.g : ℝ) (S6.rd E) with hδd
  clear_value δ
  have hq : 0 < (S.g : ℝ) / (2 * Real.pi) := by positivity
  set q := (S.g : ℝ) / (2 * Real.pi) with hqd
  clear_value q
  set R := S6.rd E with hRd
  clear_value R
  rw [hρ]
  have n6 : b0 + m + 2 - 1 = b0 + m + 1 := by omega
  have n7 : b0 + m + 2 + 1 - 1 = b0 + m + 2 := by omega
  simp only [n6, n7]
  have hHf0 : 0 ≤ Hf := by
    rw [hHf]
    refine div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (bSt_pos_loc _ (by rw [hκ]; positivity) h).le (Real.sqrt_nonneg _))
  unfold kapB
  have c1 : (((m + 1) * (m + 4) / 2 : ℕ) : ℝ) = ((m : ℝ) + 1) * ((m : ℝ) + 4) / 2 := by
    have : 2 ∣ (m + 1) * (m + 4) := by
      have h2 : (m + 1) * (m + 4) = (m + 1) * (m + 2) + 2 * (m + 1) := by ring
      rw [h2]; exact (Nat.even_mul_succ_self (m + 1)).two_dvd.add (dvd_mul_right 2 _)
    rw [Nat.cast_div this (by norm_num)]; push_cast; ring
  have c2 : (((m + 2) * (m + 1) / 2 : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) / 2 := by
    have : 2 ∣ (m + 2) * (m + 1) := by
      rw [mul_comm]; exact (Nat.even_mul_succ_self (m + 1)).two_dvd
    rw [Nat.cast_div this (by norm_num)]; push_cast; ring
  set ν1 : ℤ := S6.nuBlock ((b0 + m + 2 + ρ : ℕ) : ℤ) ((b0 + 1 : ℕ) : ℤ) ((m + 1 : ℕ) : ℤ) with hν1
  set ν2 : ℤ := S6.nuBlock ((b0 + m + 2 + ρ : ℕ) : ℤ) ((b0 + m + 2 : ℕ) : ℤ) 1 with hν2
  set e1 : ℤ := ((m + 1 : ℕ) : ℤ) * ((S.G.k : ℤ) + 2 * ρ + m + 3) with he1
  set e2 : ℤ := (S.G.k : ℤ) + 2 * ρ + 1 with he2
  refine ⟨Hf * (R ^ (-ν2 - ν1 * e1 - ν2 * e2) * √δ * Real.pi ^ ((m + 1) * (m + 4) / 2) / B1 /
    q ^ (ν1 * ((m + 1 : ℕ) : ℤ) * ((S.G.k : ℤ) + 2 * ρ + m + 2) + ν2 * e2)), fun x D z hx hD hz => ?_⟩
  have hX : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hz0 : z ≠ 0 := by rintro rfl; apply hD; rw [← hz]; simp
  have hZ : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hZl : ((m : ℝ) + 2) * Real.log ‖z‖ = Real.log ‖D‖ := by
    rw [← hz, norm_pow, Real.log_pow]; push_cast; ring
  rcases hHf0.eq_or_lt with h0 | hHp
  · rw [← h0]; simp
  have lg : ∀ {A B : ℝ}, 0 < A → 0 < B → Real.log A = Real.log B → A = B :=
    fun hA hB hAB => Real.log_injOn_pos (Set.mem_Ioi.2 hA) (Set.mem_Ioi.2 hB) hAB
  refine ⟨lg (by positivity) (by positivity) ?_, lg (by positivity) (by positivity) ?_⟩
  · simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv, Real.log_pow, Real.log_zpow,
      Real.log_rpow, Real.log_sqrt, c1, c2]
    simp only [hν1, hν2, he1, he2, S6.nuBlock, C.Mlev, U.Mlev]
    push_cast
    ring
  · simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv, Real.log_pow, Real.log_zpow,
      Real.log_rpow, Real.log_sqrt, c1, c2]
    simp only [hν1, hν2, he1, he2, S6.nuBlock, C.Mlev, U.Mlev]
    push_cast
    linear_combination ((S.G.k : ℝ) + 2 * ρ + 1) * hZl

end loc2

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

theorem Formalism.FourierDecayAlt.P.germ_null_set_compact : Formalism.FourierDecayAlt.P.FormNormSumIdentities.GNSetC := Formalism.FourierDecayAlt.P.FormNormSumIdentities.gNSetC

theorem Formalism.FourierDecayAlt.P.germ_constant : Formalism.FourierDecayAlt.P.FormNormSumIdentities.GermConst := Formalism.FourierDecayAlt.P.FormNormSumIdentities.germConst
end

section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem levQInt : ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ Cc : ℝ, 16 * Cp ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r), 1 ≤ i → ∀ (w : List C.Letter), w.length ≤ N →
      ∀ (p : C.LPt) (hc : r - i = r - D.ptSize p), D.IsLocPt p i → ∀ (hle : D.ptSize p ≤ r) (a : Wd.Ix (Fin w.length)),
      ∀ (hh : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) hh →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) hh c →
      ∀ γ ∈ B.GV k (r - D.ptSize p),
        Integrable (fun ξ : U.Xi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p) =>
          U.psiStar k (r - D.ptSize p) (D.ptPerm p) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') ξ •
            D.castF (by omega) (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)
              (U.gaXi k (r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
          (U.muXi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p)) := by
  obtain ⟨Cp, hCp0, hCp⟩ := posCoreQ
  refine ⟨Cp, hCp0, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi hi1 w hw p hc hp hle a

  obtain ⟨h, n, t, rfl⟩ : ∃ (h : C.LPt) (n : ℕ) (t : ℂ), p = h ++ [(n + 1, t)] := by
    have hne : p ≠ [] := by
      rintro rfl
      have := hp.2
      simp [D.ptSize] at this
      omega
    refine ⟨p.dropLast, (p.getLast hne).1 - 1, (p.getLast hne).2, ?_⟩
    have h1 : 1 ≤ (p.getLast hne).1 := (hp.1 _ (List.getLast_mem hne)).1
    rw [Nat.sub_add_cancel h1]
    exact (List.dropLast_append_getLast hne).symm
  obtain ⟨hpb, hps⟩ := hp
  subst hps
  set ph := D.ptSize h with hph
  have hP : D.ptSize (h ++ [(n + 1, t)]) = ph + (n + 1) := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h (n + 1) t
  have ht : t ≠ 0 := (hpb (n + 1, t) (by simp)).2
  have hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)])) := ⟨hpb, rfl⟩
  have hlocH := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2
  set ρ := r - D.ptSize (h ++ [(n + 1, t)]) with hρ
  have hsum : ph + (n + 1) + ρ = r := by omega
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  have hσ : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h)) (Fin.cast hP q)).val = (D.ptPerm (h ++ [(n + 1, t)]) q).val := by
    intro q
    rw [hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨q.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t (Fin.cast hP q) = D.ptDiag (h ++ [(n + 1, t)]) q := by
    intro q
    simp only [D.ptDiag]
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]
  have hdP : ∀ q, Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t q ≠ 0 := by
    intro q
    refine Fin.addCases (fun i => ?_) (fun i => ?_) q
    · simp only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; exact hd0 i
    · simp only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]; exact ht
  have hS : ∀ (Gx : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ), D.sliceAt k r T.base.z T.base.z' Gx (h ++ [(n + 1, t)]) γ =
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) Gx) (fun a => a.elim0) γ := by
    intro Gx γ
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) γ
    unfold D.sliceAt
    rw [dif_pos (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  have e1 : r = ph + (n + 1) + ρ := hsum.symm
  have e2 : ph + (n + 1) + ρ = r := hsum
  have hj1 : 1 ≤ ph + (n + 1) := by omega
  obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (by omega) w a hj1
  have hU : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g =
        B.opApply Θ (D.castF e2 (D.cutF T.base χ hh ε)) g := by
    intro hh hsm g hg hD
    have hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ hh ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hsm ε
    have h1 : D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) =
        D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.cutF T.base χ hh ε)) (ph + (n + 1)) (by omega) w a := by
      rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hP _ _ w a
    rw [h1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD]
  have hFrel : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g =
        B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z)
          (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 hh x) g := by
    intro hh hsm g hg hD
    rw [hU hh hsm g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]
  set nd := 2 * r + k + 1 with hnd
  set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs
  obtain ⟨b1, b2, b3, b4, b5⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs r k N w.length (ph + (n + 1)) hk2 hw (by omega)
  have hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r := by
    simp only [P5.mmUser, P5.nV, hPk, hPr, hnd]
  have hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by
    simp only [P5.Auser, P5.nV, hPk, hPr, hnd]
    try (push_cast; try ring)
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by exact_mod_cast b5
  have hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5 := by
    rw [hAs]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hsumR : (((ph + (n + 1) + ρ : ℕ) : ℝ)) = (r : ℝ) := by exact_mod_cast hsum
  obtain ⟨ε', K, hε', hK0, hQ⟩ := hCp k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
    Θ _ _ hΘ χ A₀ ε hχ hε (D.ptPerm h) (D.ptDiag h) t hd0 ht As (P5.mmUser P0 N) (P5.Auser P0 N + 1)
    b1 b2 (by rw [hmmU]; exact b3) (by rw [hsum]; exact b4)
    (by
      rw [hsumR, hAU, hAsR]
      have hR3 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
      have : 0 ≤ ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by positivity
      nlinarith)
    (by
      rw [hsumR, hAsR]
      have hR4 : 0 ≤ ((r : ℝ) + 1) ^ 4 := by positivity
      have hX0 : 0 ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by linarith
      have s1 : Cp * ((r : ℝ) + 1) ^ 4 * (11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5) ≤
          Cp * ((r : ℝ) + 1) ^ 4 * (16 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have s2 : 16 * Cp * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) ≤
          Cc * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_right hCc (by positivity)
      have s3 : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) ≤ A₀ := by
        have hndR : (nd : ℝ) = 2 * (r : ℝ) + k + 1 := by rw [hnd]; push_cast; ring
        rw [hndR]; exact hA₀
      nlinarith)
  have hfun : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp),
      D.castF hc (D.sliceAt k r T.base.z T.base.z'
        (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) (h ++ [(n + 1, t)])) =
      fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a))
        (fun a => a.elim0) γ := by
    intro hh
    rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]
    funext γ
    exact hS _ γ
  have hz1 : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z) = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z := by
    have hzl : T.base.z = D.castV (by omega)
        (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z) :=
      (T.z_lev _ hi).symm
    rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _
  have hz1' : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z') = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z' := by
    have hzl' : T.base.z' = D.castV (by omega)
        (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z') :=
      (T.z'_lev _ hi).symm
    rw [hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _
  have hZ0 : G.detM (fun a => a.elim0 : G.Mat 0) ≠ 0 := by
    unfold G.detM; rw [Matrix.det_isEmpty]; exact one_ne_zero
  intro hh c hsm hcl γ hγ
  have I := (hQ (D.castF e2 hh) c (ccle_castF e2 hcl) _ (hFrel hh hsm)).2.2 γ hγ
  have hσ' : ∀ q : Fin (ph + (n + 1)), (D.ptPerm (h ++ [(n + 1, t)]) (Fin.cast hP.symm q)).val =
      (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h) q).val := by
    intro q; have := hσ (Fin.cast hP.symm q); simpa using this.symm
  have hd' : ∀ q : Fin (ph + (n + 1)), D.ptDiag (h ++ [(n + 1, t)]) (Fin.cast hP.symm q) =
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t q := by
    intro q; have := hd (Fin.cast hP.symm q); simpa using this.symm
  have I2 := (Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP.symm _ _ hσ' _ _ hd' (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε)
      (D.ptSize (h ++ [(n + 1, t)])) hi w a)) γ).1 I
  simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF] at I2
  exact I2

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem slice_integral_cutoff : Formalism.FourierDecayAlt.P.FormNormSumIdentities.SliceIntCut := by
  obtain ⟨Cp, hCp0, hL⟩ := Formalism.FourierDecayAlt.P.FormNormSumIdentities.levQInt
  intro Wp Wq _ _ _ _ _ _ P0 T w f χ ε i hi hi1 hk2 hfs hR hχ hε p hp e γ hγ
  obtain ⟨R, hR⟩ := hR
  obtain ⟨c, hcl⟩ := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hfs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P0.k P0.r R)
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    ((16 * Cp) * ((P0.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) ^ 2 +
      (2 * (P0.r : ℝ) + P0.k + 1) ^ 3))
    (3 * (11 * (w.length * (2 * P0.r + P0.k + 1) ^ 2 + (2 * P0.r + P0.k + 1) ^ 3) + 5))
  have hle : D.ptSize p ≤ P0.r := hp.2 ▸ hi
  have hc : P0.r - i = P0.r - D.ptSize p := by rw [hp.2]
  exact hL (16 * Cp) le_rfl P0.k P0.r Wp Wq T χ _ w.length P0 rfl rfl hk2 hχ le_rfl ε hε i hi hi1 w le_rfl p hc hp
    hle e f c hfs hcl γ hγ

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory

open Formalism.FourierDecayAlt.P.PBJ

section core

variable {k ρ ph m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem coreQ (σh : Equiv.Perm (Fin ph)) (dh : Fin ph → ℂ) (σb : Equiv.Perm (Fin m)) (db : Fin m → ℂ)
    (z z' : Fin (2 * (ph + m + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + m + ρ) → E) (γ : B.Mat k ρ)
    (hint : Integrable (fun ξ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) =>
        U.psiStar (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) z z' ξ •
          F (U.gaXi (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) ξ (fun a => a.elim0) γ))
      (U.muXi k (ph + m) 0 ρ (Fub.sigQ σh σb))) :
    U.PhiFun (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) z z' F (fun a => a.elim0) γ =
      U.PhiTop (p := m) (s := 0) U.betaU σb db
        (fun Z => U.PhiFun (p := ph) (s := m) k ρ σh dh z z' F Z γ) (fun x => x.elim0) := by
  set RR := U.RC k (ph + m) ρ × U.RC k (ph + m) ρ
  have sR := Dx2.SL.sigma_RC k (ph + m) ρ
  set μR : Measure RR := (U.muRC k (ph + m) ρ).prod (U.muRC k (ph + m) ρ)
  have s1 := Fub.sfXiH ph m σh
  have s2 := Fub.sfXiH m 0 σb
  have s3 : SFinite (U.muXiH (ph + m) 0 (Fub.sigQ σh σb)) := Fub.sfXiH (ph + m) 0 (Fub.sigQ σh σb)
  let g : RR × (U.XiH ph m σh × U.XiH m 0 σb) → E := fun y =>
    U.psiH U.betaU σb y.2.2 •
      (U.psiStar (p := ph) (s := m) k ρ σh z z' (y.1, y.2.1) • F (U.gaXi (p := ph) (s := m) k ρ σh dh (y.1, y.2.1)
        (Matrix.of.symm (U.ZjH (p := m) (s := 0) σb db y.2.2 (fun x => x.elim0))) γ))
  let Φ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) ≃ᵐ RR × (U.XiH ph m σh × U.XiH m 0 σb) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl RR) (Fub.xiE σh σb)
  have hΦ : MeasurePreserving Φ (U.muXi k (ph + m) 0 ρ (Fub.sigQ σh σb)) (μR.prod (volume.prod volume)) :=
    (MeasurePreserving.id μR).prod (Fub.xiE_mp σh σb)
  have hfg : (fun ξ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) =>
      U.psiStar (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) z z' ξ •
        F (U.gaXi (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) ξ (fun a => a.elim0) γ)) = g ∘ Φ := by
    funext ξ
    obtain ⟨x, ⟨a0, b0⟩, v, u⟩ := ξ
    rw [Function.comp_apply]
    rw [show Φ (x, ((a0, b0), v, u)) = (x, Fub.xiE σh σb ((a0, b0), v, u)) from rfl, Fub.xiE_apply]
    simp only [g, U.psiStar, U.gaXi, U.ZjH, Dx2.SL.zj_zero, Fub.zj_split, Equiv.apply_symm_apply]
    rw [Fub.psiH_split σh σb U.betaU a0 b0 (Dx2.SL.uniqueT m).toInhabited.default v u, smul_smul]
    congr 1
    have e1 : Formalism.QuantumDeterminants.psi k (ph + m + 0 + ρ) z cStd (U.Rn k (ph + m + 0) ρ x.1) =
        Formalism.QuantumDeterminants.psi k (ph + m + ρ) z cStd (U.Rn k (ph + m) ρ x.1) := rfl
    have e2 : Formalism.QuantumDeterminants.psi k (ph + m + 0 + ρ) z' cStd (U.Rn k (ph + m + 0) ρ x.2) =
        Formalism.QuantumDeterminants.psi k (ph + m + ρ) z' cStd (U.Rn k (ph + m) ρ x.2) := rfl
    rw [e1, e2]
    ring
  have hg : Integrable g (μR.prod (volume.prod volume)) := by
    have := hint; rw [hfg] at this
    exact (hΦ.integrable_comp_emb Φ.measurableEmbedding).mp this
  have hL : U.PhiFun (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) z z' F (fun a => a.elim0) γ =
      ∫ y, g y ∂(μR.prod (volume.prod volume)) := by
    unfold U.PhiFun
    rw [hfg]
    exact hΦ.integral_comp' g
  have hA : MeasurePreserving (MeasurableEquiv.prodAssoc : (RR × U.XiH ph m σh) × U.XiH m 0 σb ≃ᵐ _)
      ((μR.prod volume).prod volume) (μR.prod (volume.prod volume)) := Dx2.SL.assoc_mp μR volume volume
  let g' : (RR × U.XiH ph m σh) × U.XiH m 0 σb → E := fun w => g (w.1.1, (w.1.2, w.2))
  have eg : g ∘ (MeasurableEquiv.prodAssoc : (RR × U.XiH ph m σh) × U.XiH m 0 σb ≃ᵐ _) = g' := rfl
  have hg' : Integrable g' ((μR.prod volume).prod volume) := by
    rw [← eg]; exact (hA.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mpr hg
  have hA' : ∫ y, g y ∂(μR.prod (volume.prod volume)) = ∫ w, g' w ∂((μR.prod volume).prod volume) :=
    (hA.integral_comp' g).symm
  rw [hL, hA', MeasureTheory.integral_prod_symm g' hg']
  unfold U.PhiTop
  rw [show U.muXiH m 0 σb = volume from rfl]
  congr 1
  funext w
  simp only [g', g]
  rw [integral_smul]
  rfl

end core

section wrap

theorem partner_two (h : C.LPt) (n : ℕ) (t c : ℂ) (a : ℕ) (ha : a < D.ptSize h + (n + 1 + 1)) :
    D.ptPartner (h ++ [(n + 1, t), (1, c)]) a =
      if a < D.ptSize h then D.ptPartner h a else if a < D.ptSize h + (n + 1) then D.ptSize h + (n - (a - D.ptSize h))
        else a := by
  rw [show h ++ [(n + 1, t), (1, c)] = (h ++ [(n + 1, t)]) ++ [(1, c)] by simp]
  rw [Dx2.SL.partner_append 1 c (h ++ [(n + 1, t)]) a (by rw [Dx2.SL.ptSize_append]; omega), Dx2.SL.ptSize_append]
  by_cases h1 : a < D.ptSize h + (n + 1)
  · rw [if_pos h1, Dx2.SL.partner_append (n + 1) t h a h1]
    by_cases h2 : a < D.ptSize h
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_pos h1]; omega
  · rw [if_neg h1, if_neg (by omega), if_neg h1]; omega

theorem scal_two (h : C.LPt) (n : ℕ) (t c : ℂ) (a : ℕ) (ha : a < D.ptSize h + (n + 1 + 1)) :
    D.ptScal (h ++ [(n + 1, t), (1, c)]) a =
      if a < D.ptSize h then D.ptScal h a else if a < D.ptSize h + (n + 1) then t else c := by
  rw [show h ++ [(n + 1, t), (1, c)] = (h ++ [(n + 1, t)]) ++ [(1, c)] by simp]
  rw [Dx2.SL.scal_append 1 c (h ++ [(n + 1, t)]) a (by rw [Dx2.SL.ptSize_append]; omega), Dx2.SL.ptSize_append]
  by_cases h1 : a < D.ptSize h + (n + 1)
  · rw [if_pos h1, Dx2.SL.scal_append (n + 1) t h a h1]
    by_cases h2 : a < D.ptSize h
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_pos h1]
  · rw [if_neg h1, if_neg (by omega), if_neg h1]

theorem kapB_mul (n : ℕ) :
    kapB n * ((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) ^ (Fintype.card (Fin (n + 1)) +
        (Fintype.card (G.UT (n + 1)) + Fintype.card (Fin (n + 1)))) : NNReal) : ℝ) = 1 := by
  rw [Dx2.SL.norm_betaU, show (2 : ℝ) / (2 * Real.pi) = 1 / Real.pi by field_simp, Dx2.SL.card_UT' n,
    Fintype.card_fin]
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN : (n + 1) * (n + 4) / 2 = n + 1 + ((n + 1) * n / 2 + (n + 1)) := by
    have h2 : 2 ∣ (n + 1) * n := (Nat.even_mul_pred_self (n + 1)).two_dvd
    obtain ⟨q, hq⟩ := h2
    have e : (n + 1) * (n + 4) = 2 * (q + 2 * (n + 1)) := by nlinarith
    rw [e, hq]; omega
  unfold kapB
  rw [NNReal.coe_pow, Real.coe_toNNReal _ (by positivity), hN, ← mul_pow, mul_one_div_cancel hp.ne', one_pow]

end wrap

section final

theorem sliceOmBlock : SliceOmBlock := by
  intro k r E _ _ _ z z' F h p n t c hp hle γ hloc hint
  subst hp
  have hP : D.ptSize (h ++ [(n + 1, t), (1, c)]) = D.ptSize h + (n + 1 + 1) := ptSize_two h n t c
  have hlocH : D.IsLocPt h (D.ptSize h) := ⟨fun b hb => hloc.1 b (List.mem_append_left _ hb), rfl⟩
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  set ph := D.ptSize h with hph
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t), (1, c)])),
      ((Fub.sigQ (D.ptPerm h) (Om.σB (n + 1))) (Fin.cast hP a)).val =
        (D.ptPerm (h ++ [(n + 1, t), (1, c)]) a).val := by
    intro a
    have ha : a.val < ph + (n + 1 + 1) := by have := a.isLt; omega
    rw [hspec a, partner_two h n t c a.val ha]
    by_cases h1 : a.val < ph
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (n + 1 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Fub.sigQ_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd ph ⟨a.val - ph, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, Fub.sigQ_natAdd, Fin.val_natAdd]
      by_cases h2 : a.val < ph + (n + 1)
      · rw [if_pos h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.castAdd 1 ⟨a.val - ph, by omega⟩ := Fin.ext rfl
        rw [e2, Om.σB, Fub.sigQ_castAdd, Fin.val_castAdd]
        simp only [Fin.revPerm_apply, Fin.val_rev]
        omega
      · rw [if_neg h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.natAdd (n + 1) (0 : Fin 1) :=
          Fin.ext (by simp; omega)
        rw [e2, Om.σB, Fub.sigQ_natAdd, Fin.val_natAdd]
        simp
        omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t), (1, c)])),
      Fub.dQ (D.ptDiag h) (Fub.dQ (fun _ : Fin (n + 1) => t) (fun _ : Fin 1 => c)) (Fin.cast hP a) =
        D.ptDiag (h ++ [(n + 1, t), (1, c)]) a := by
    intro a
    have ha : a.val < ph + (n + 1 + 1) := by have := a.isLt; omega
    simp only [D.ptDiag]
    rw [scal_two h n t c a.val ha]
    by_cases h1 : a.val < ph
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (n + 1 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Fub.dQ, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd ph ⟨a.val - ph, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, Fub.dQ, Fin.addCases_right]
      by_cases h2 : a.val < ph + (n + 1)
      · rw [if_pos h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.castAdd 1 ⟨a.val - ph, by omega⟩ := Fin.ext rfl
        rw [e2, Fub.dQ, Fin.addCases_left]
      · rw [if_neg h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.natAdd (n + 1) (0 : Fin 1) :=
          Fin.ext (by simp; omega)
        rw [e2, Fub.dQ, Fin.addCases_right]
  obtain ⟨hT1, hT2⟩ := Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t), (1, c)])) hP _ _ hσ _ _ hd
    (D.castV (by omega) z) (D.castV (by omega) z') (D.castF (by omega) F) γ
  have hc := coreQ (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t), (1, c)])) (D.ptPerm h) (D.ptDiag h) (Om.σB (n + 1))
    (Fub.dQ (fun _ : Fin (n + 1) => t) (fun _ : Fin 1 => c)) _ _ _ γ (hT1 hint)
  unfold D.sliceAt
  rw [dif_pos hle, hT2, hc, Om.omBlock_eq, smul_smul, ← Complex.ofReal_mul]
  rw [kapB_mul n, Complex.ofReal_one, one_smul]
  simp only [Dx2.SL.castV_castV, Dx2.SL.castF_castF]

end final

end Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory

theorem Formalism.FourierDecayAlt.P.slice_orbital_block : Formalism.FourierDecayAlt.P.FormNormSumIdentities.SliceOmBlock := Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory.sliceOmBlock
end
end

section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory

noncomputable section

section tr

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem phiFun_tr {k p s ρ ρ' r : ℕ} (hρ : ρ = ρ') (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (e : r = p + s + ρ) (e' : r = p + s + ρ')
    (Z : G.Mat s) (γ : B.Mat k ρ) :
    U.PhiFun k ρ' σ d (D.castV e' z) (D.castV e' z') (D.castF e'.symm F) Z (D.castM hρ γ) =
      U.PhiFun k ρ σ d (D.castV e z) (D.castV e z') (D.castF e.symm F) Z γ := by
  subst hρ
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]

end tr

theorem finrank_UT_lt (m : ℕ) (a : ℝ) (ha : ((m : ℝ) + 1) * ((m : ℝ) + 4) < a) :
    (Module.finrank ℝ (UT (m + 1 + 1) → ℂ) : ℝ) < a := by
  have h1 : Module.finrank ℝ (UT (m + 1 + 1) → ℂ) = Fintype.card (UT (m + 1 + 1)) * 2 := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
  have h2 := Formalism.FourierDecayAlt.P.Dx2.SL.card_UT (m + 1 + 1)
  have h3 : ((Fintype.card (UT (m + 1 + 1)) * 2 : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    have : Fintype.card (UT (m + 1 + 1)) * 2 = (m + 2) * (m + 1) := by
      rw [mul_comm, h2, show m + 1 + 1 - 1 = m + 1 by omega]
    rw [this]; push_cast; ring
  rw [h1, h3]
  nlinarith

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory Formalism.FourierDecayAlt.P.FormNormSumIdentities

theorem slice_germ_points : Formalism.FourierDecayAlt.P.FormNormSumIdentities.YGSlice := by
  intro k r E _ _ _ z z' F h' m ρ e1 V _ _ _ Φ L γ Kc K a hh' hKc ha hΦ hL q hq hint
  have hW : (G.wMat (m + 1)).det ≠ 0 := (Formalism.FourierDecayAlt.P.Ux3.wMat_det (m + 1)).ne_zero
  rcases q with ⟨t, c⟩ | w0
  · obtain ⟨ht, hcK⟩ := hq
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hKc; simpa using hcK
    have hne : ∀ p, G.detM (G.orbM (m + 1) t c p) ≠ 0 := by
      intro p; rw [Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM]
      exact mul_ne_zero hW (fun h0 => hKc (h0 ▸ hcK))
    have himg : ∀ p, G.detM (G.orbM (m + 1) t c p) ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc :=
      fun p => ⟨c * t ^ (m + 1), hcK, (Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM _ _ _ _).symm⟩
    have hI := integrable_blockIntegrand U.betaU m Φ t c ht K a ha (fun p => (hΦ _ (hne p)).1)
      (fun p => (hΦ _ (hne p)).2)
    show L (((kapB m : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) Φ t c) = _
    rw [L.map_smul, clm_omBlock L U.betaU (m + 1) Φ t c hI]
    have hloc : D.IsLocPt (ptG h' m (Sum.inl (t, c))) (D.ptSize (ptG h' m (Sum.inl (t, c)))) := by
      refine ⟨fun b hb => ?_, rfl⟩
      simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with hb | hb | hb
      · exact hh'.1 b hb
      · subst hb; exact ⟨by omega, ht⟩
      · subst hb; exact ⟨le_rfl, hc0⟩
    have hle : D.ptSize (ptG h' m (Sum.inl (t, c))) ≤ r := by rw [ptSize_ptG]; omega
    have hSB := Formalism.FourierDecayAlt.P.slice_orbital_block k r E z z' F h' (ptG h' m (Sum.inl (t, c))) m t c rfl hle
      (D.castM (by rw [ptSize_ptG]; omega) γ) hloc hint
    rw [hSB]
    congr 1
    unfold G.OmBlock
    congr 1
    funext p
    simp only [G.blockIntegrand]
    congr 1
    have hp := hL _ (hne p) (himg p)
    simp only [G.orbM] at hp
    rw [hp]
    exact (phiFun_tr (by rw [ptSize_ptG]; omega) _ _ z z' F _ _ _ γ).symm
  · obtain ⟨D0, hDK, hz⟩ := hq
    have hz0 : w0 ≠ 0 := by
      rintro rfl
      apply hKc
      have : (0 : ℂ) = (-1) ^ (m + 3) * D0 := by simpa using hz
      have h1 : D0 = 0 := by
        rcases mul_eq_zero.1 this.symm with h | h
        · exact absurd h (pow_ne_zero _ (by norm_num))
        · exact h
      exact h1 ▸ hDK
    have hne : ∀ v, G.detM (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv (m + 1) w0 v) ≠ 0 := by
      intro v
      have := Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM m w0 D0 hz v
      show G.detM (Formalism.FourierDecayAlt.P.OrbitTailEstimates.longM (m + 1 + 1) w0 v) ≠ 0
      rw [this]
      exact mul_ne_zero hW (fun h0 => hKc (h0 ▸ hDK))
    have himg : ∀ v, G.detM (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv (m + 1) w0 v) ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc :=
      fun v => ⟨D0, hDK, (Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM m w0 D0 hz v).symm⟩
    have hI := integrable_longIntegrand (m + 1) Φ w0 hz0 K a (finrank_UT_lt m a ha)
      (fun v => (hΦ _ (hne v)).1) (fun v => (hΦ _ (hne v)).2)
    show L (((Real.pi ^ ((m + 2) * (m + 1) / 2) : ℝ) : ℂ) • G.OmLong U.betaU (m + 1) Φ w0) = _
    rw [L.map_smul, clm_omLong L U.betaU (m + 1) Φ w0 hI]
    have hloc : D.IsLocPt (ptG h' m (Sum.inr w0)) (D.ptSize (ptG h' m (Sum.inr w0))) := by
      refine ⟨fun b hb => ?_, rfl⟩
      simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with hb | hb
      · exact hh'.1 b hb
      · subst hb; exact ⟨by omega, hz0⟩
    have hle : D.ptSize (ptG h' m (Sum.inr w0)) ≤ r := by rw [ptSize_ptG]; omega
    have hSO := Formalism.FourierDecayAlt.P.slice_measure_identity k r E z z' F h' (ptG h' m (Sum.inr w0)) (m + 1) w0 rfl hle
      (D.castM (by rw [ptSize_ptG]; omega) γ) hloc hint
    rw [hSO]
    congr 1
    unfold G.OmLong
    congr 1
    funext v
    congr 1
    have hp := hL _ (hne v) (himg v)
    exact hp.trans (phiFun_tr (by rw [ptSize_ptG]; omega) _ _ z z' F _ _ _ γ).symm

end Formalism.FourierDecayAlt.P
end

section
namespace Formalism.FourierDecayAlt.P

theorem germ_at_place : FormNormSumIdentities.GermPlace :=
  FormNormSumIdentities.germPlace_of slice_integral_cutoff slice_germ_points form_model

theorem germ_rate_lower_bound : GermRateSplit.GermRateLowB :=
  FormNormSumIdentities.germRateLowB_of germ_at_place germ_null_set_compact germ_constant

end Formalism.FourierDecayAlt.P
end
