import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmLongContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PosCoreQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectNonneg

section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCTx6 Formalism.FourierDecayAlt.P.JCTx6.Pos Formalism.FourierDecayAlt.P.PBE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem continuous_unipotent_vector_scalar (n : ℕ) (v : G.UT (n + 1) → ℂ) : Continuous (fun t : ℂ => Zv n t v) := by
  show Continuous (fun t : ℂ => fun i j => (G.ptLong (n + 1) t * G.upper v) i j)
  have h : Continuous (fun t : ℂ => (G.ptLong (n + 1) t * G.upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := by
    unfold G.ptLong
    exact (continuous_id.smul continuous_const).matrix_mul continuous_const
  exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp h)

set_option maxHeartbeats 1000000 in

theorem posCoreCont : ∃ Cc : ℝ, 0 ≤ Cc ∧
  ∀ (k ph n ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ), inWb k (ph + (n + 1) + ρ) z → inWb k (ph + (n + 1) + ρ) z' →
    ∀ (Θ : B.DiffOp k (ph + (n + 1) + ρ) Wp Wq) (o κ : ℕ), U.InDD k (ph + (n + 1)) ρ o κ Θ →
    ∀ (χ : ℝ → ℝ) (A₀ ε : ℝ), C6.IsCut0 χ → 0 < ε →
    ∀ (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t0 : ℂ), (∀ i, d i ≠ 0) → t0 ≠ 0 →
    ∀ (As mm : ℕ) (A : ℝ), o ≤ As → κ + (ph + (n + 1)) * o ≤ As → mm ≤ As →
      (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 ≤ As →
      A ≤ 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) →
      Cc * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ →
      ∃ ε' : ℝ, 0 < ε' ∧
      ∀ (f : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * As) f c →
      ∀ F : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp),
        (∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
          F g = B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) z z' x / ε) : ℝ) : ℂ) • f x) g) →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          B.CCle A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ) Kb ∧
          (∀ γ ∈ B.GV k ρ, U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ ≠ 0 →
            ε' ≤ Gf k ρ (U.lowV k (ph + (n + 1)) ρ z) (U.lowV k (ph + (n + 1)) ρ z') γ) ∧
          B.CCle A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ - U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t0) z z' F (fun a => a.elim0) γ) (Dd t) := by
  have hIntG := Formalism.FourierDecayAlt.P.JCTx6.Int.intG
  have hTrans := Formalism.FourierDecayAlt.P.JCTx6.Int.orbit_slice_integrable
  obtain ⟨CcU, hCcU⟩ := Formalism.FourierDecayAlt.P.corollary_u2_germ_hypothesis 127 0
  refine ⟨max CcU 0, le_max_right _ _, ?_⟩
  intro k ph n ρ Wp Wq _ _ _ _ _ _ z z' hz hz' Θ o κ hΘ χ A₀ ε hχ hε σ d t0 hd ht0 As mm A ho hκ
    hmm hAs hA hA₀

  have hw : (G.wMat (n + 1)).det ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (n + 1)
  set c₀ : ℂ := (U.hMat σ d).det * (t0 ^ (n + 1) * (G.wMat (n + 1)).det) with hc₀def
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht0) hw)
  have hc₀n : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := bump_exists hc₀
  obtain ⟨δ, hδ, hχε⟩ := isCutG_scale hχ hε
  set ε' : ℝ := δ * ε / (2 * ‖c₀‖) ^ 2 with hε'def
  have hε' : 0 < ε' := by positivity
  let UD : U.UData k ph (n + 1) ρ Wp Wq Unit :=
    ⟨σ, d, z, z', fun _ => Θ, χD, fun x => χ (ε⁻¹ * x), δ * ε, ε', o, κ, 0, mm, As⟩
  have hAs1 : 1 ≤ As := le_trans (Nat.one_le_pow _ _ (by omega)) hAs
  have hOk : UD.Ok 0 := by
    refine ⟨hd, by omega, hz, hz', fun _ => hΘ, hχD, hχε, hε', ?_, ho, hκ, by simp [UD], hmm, hAs,
      by simpa using hAs1⟩
    intro w hw'
    have h2 := (hχDs w hw').2
    have h3 : ‖w‖ ^ 2 ≤ (2 * ‖c₀‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc ε' * ‖w‖ ^ 2 ≤ ε' * (2 * ‖c₀‖) ^ 2 := mul_le_mul_of_nonneg_left h3 hε'.le
      _ = δ * ε := by rw [hε'def]; field_simp
  have hA₀U : CcU * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ := by
    refine le_trans ?_ hA₀
    gcongr
    exact le_max_left _ _
  obtain ⟨ha1, -, -, C, hC⟩ := hCcU k ph (n + 1) ρ Wp Wq Unit UD hOk A₀ hA₀U
  set a := UD.a 0 A₀ with ha_def
  set Iv : ℝ := ∫ v, (1 + ‖v‖) ^ (-a) ∂(G.muPi U.betaU (G.UT (n + 1))) with hIv
  refine ⟨ε', hε', ?_⟩
  intro f c hc F hF
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  obtain ⟨V, indexVFirst, indexVSecond, hVc, ⟨MM⟩⟩ :=
    Formalism.FourierDecayAlt.P.compactly_supported_banach_model k ρ (Unit → (Wq →L[ℂ] Wp)) (UD.a 0 A₀) mm UD.S
  obtain ⟨Φ, hΦev, hΦreg⟩ := hC f c hc V MM

  obtain ⟨C1, hC1⟩ := Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt k (ph + (n + 1)) ρ Wp Wq z z' o κ Θ χD
    (fun x => χ (ε⁻¹ * x)) (δ * ε) hΘ hχD hχε 0 (3 * As) A₀ (by omega)
  have hStar := hC1 f c hc
  set F₁ := B.opApply Θ (U.cutDG k (ph + (n + 1)) ρ z z' χD (fun x => χ (ε⁻¹ * x)) f) with hF₁def

  have hcF : Continuous (fun t : ℂ => (U.hMat σ d).det * (t ^ (n + 1) * (G.wMat (n + 1)).det)) := by fun_prop
  obtain ⟨δ1, hδ1, hδ1c⟩ := Metric.continuous_iff.mp hcF t0 (‖c₀‖ / 4) (div_pos hc₀n (by norm_num))
  have ht0n : 0 < ‖t0‖ := norm_pos_iff.mpr ht0
  set δ0 : ℝ := min δ1 (‖t0‖ / 2) with hδ0def
  have hδ0 : 0 < δ0 := lt_min hδ1 (by positivity)
  have hnear : ∀ t : ℂ, dist t t0 < δ0 → ‖t0‖ / 2 ≤ ‖t‖ ∧ t ≠ 0 ∧
      dist ((U.hMat σ d).det * (t ^ (n + 1) * (G.wMat (n + 1)).det)) c₀ < ‖c₀‖ / 4 := by
    intro t ht
    have h1 : dist t t0 < ‖t0‖ / 2 := lt_of_lt_of_le ht (min_le_right _ _)
    have h2 : ‖t0‖ / 2 ≤ ‖t‖ := by
      have h3 := norm_sub_norm_le t0 t
      rw [dist_eq_norm] at h1
      rw [norm_sub_rev] at h3
      linarith
    refine ⟨h2, fun h0 => ?_, hδ1c t (lt_of_lt_of_le ht (min_le_left _ _))⟩
    rw [h0, norm_zero] at h2
    linarith

  have hB : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), dist (U.DjU k (ph + (n + 1)) ρ g) c₀ < ‖c₀‖ / 4 → F g = F₁ g := by
    intro g hg hgc
    have hne : U.DjU k (ph + (n + 1)) ρ g ≠ 0 := by
      intro h0
      rw [h0, dist_zero_left] at hgc
      linarith
    rw [hF g hg hne]
    refine opApply_congr_open Θ (O := {x | dist (U.DjU k (ph + (n + 1)) ρ x) c₀ < ‖c₀‖ / 4}) ?_ ?_ g ?_
    · exact isOpen_lt ((cont_DjU k (ph + (n + 1)) ρ).dist continuous_const) continuous_const
    · intro x hx
      simp only [U.cutDG]
      rw [hχD1 _ (le_of_lt hx), one_mul, div_eq_inv_mul]
    · exact hgc
  have hZne : ∀ t : ℂ, t ≠ 0 → ∀ v : G.UT (n + 1) → ℂ, G.detM (Zv n t v) ≠ 0 := by
    intro t ht v
    have e : G.detM (Zv n t v) = t ^ (n + 1) * (G.wMat (n + 1)).det := detM_Zv n t v
    rw [e]; exact mul_ne_zero (pow_ne_zero _ ht) hw
  have hOrb : ∀ t : ℂ, dist t t0 < δ0 → ∀ (ξ : U.Xi k ph (n + 1) ρ σ) (v : G.UT (n + 1) → ℂ) (γ : B.Mat k ρ),
      γ ∈ B.GV k ρ → F (U.gaXi k ρ σ d ξ (Zv n t v) γ) = F₁ (U.gaXi k ρ σ d ξ (Zv n t v) γ) := by
    intro t ht ξ v γ hγ
    obtain ⟨-, ht', hc'⟩ := hnear t ht
    apply hB _ (Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ _
      (hZne t ht' v) hγ)
    rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice]
    have e : G.detM (Zv n t v) = t ^ (n + 1) * (G.wMat (n + 1)).det := detM_Zv n t v
    rw [e]
    exact hc'

  have hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD) := hχD.2.1.isCompact.image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw', rfl⟩
    exact lt_of_lt_of_le (by positivity) (hχDs w hw').1
  have hthr : 2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) -
        2 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) * ((0 + o : ℕ) : ℝ)) /
        (8 * (2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1)) := by
    have hnd : ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) ≤ (As : ℝ) := by
      have h1 : 2 * (ph + (n + 1) + ρ) + k + 1 ≤ (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 :=
        Nat.le_self_pow (by norm_num) _
      exact_mod_cast h1.trans hAs
    have ha1' := ha1
    simp only [ha_def, U.UData.a, U.a1] at ha1'
    set R : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) with hR
    have hR0 : 0 ≤ R := Nat.cast_nonneg _
    have hD : 0 < 8 * (2 * R + 1) := by positivity
    set Nd : ℝ := ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) with hNd
    have hNd1 : 1 ≤ Nd := by rw [hNd]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hle : (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) -
          2 * (R + 1) * (((0 * (n + 1) ^ 2 + 1 + mm) + o : ℕ) : ℝ) - 5 * R * (((0 * (n + 1) ^ 2 : ℕ) : ℝ) + 1) -
          2 * R * (mm : ℝ)) / (8 * (2 * R + 1)) ≤
        (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) - 2 * (R + 1) * ((0 + o : ℕ) : ℝ)) /
          (8 * (2 * R + 1)) := by
      apply div_le_div_of_nonneg_right _ hD.le
      push_cast
      have hm0 : (0 : ℝ) ≤ mm := Nat.cast_nonneg _
      nlinarith
    have hlt : 2 * R * Nd < (((127 : ℕ) : ℝ) + 1) * (R + 1) ^ 3 * (As : ℝ) := by
      have hAs' : (1 : ℝ) ≤ As := by exact_mod_cast hAs1
      have h1 : 2 * R * Nd < 128 * (R + 1) * Nd := by nlinarith
      have h2 : 128 * (R + 1) * Nd ≤ 128 * (R + 1) ^ 3 * (As : ℝ) := by
        have h3 : (R + 1) ≤ (R + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
        have h4 : (R + 1) * Nd ≤ (R + 1) ^ 3 * (As : ℝ) :=
          mul_le_mul h3 hnd (by linarith) (by positivity)
        nlinarith
      norm_num
      linarith
    exact lt_of_lt_of_le hlt (le_trans ha1' hle)
  have hInt : ∀ t : ℂ, dist t t0 < δ0 → ∀ γ ∈ B.GV k ρ,
      Integrable (gInt k ph n ρ σ d t z z' F γ) (muG k ph n ρ σ) := by
    intro t ht γ hγ
    have ht' := (hnear t ht).2.1
    have h1 := hIntG k ph n ρ σ d t hd ht' _ hK hK0 0 _ hthr z z' (Wq →L[ℂ] Wp) F₁ (C1 * c) hStar γ hγ
    have e : gInt k ph n ρ σ d t z z' F γ = gInt k ph n ρ σ d t z z' F₁ γ := by
      funext y
      unfold gInt
      have e1 : U.gaXi k ρ σ d (y.1, y.2.1) (Matrix.of.symm (t • G.wMat (n + 1) * G.upper y.2.2)) γ =
          U.gaXi k ρ σ d (y.1, y.2.1) (Zv n t y.2.2) γ := rfl
      rw [e1, hOrb t ht _ _ γ hγ]
    rw [e]; exact h1
  have hcore : ∀ t : ℂ, dist t t0 < δ0 → ∀ γ ∈ B.GV k ρ,
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ =
        ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) •
          G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t :=
    fun t ht γ hγ => Dx2.SL.core σ d t z z' F γ (hTrans k ph n ρ σ d t z z' _ F γ (hInt t ht γ hγ))

  have ha128 : 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) ≤ a := by
    have h := ha1
    norm_num at h ⊢
    exact h
  have ha0 : 0 ≤ a := le_trans (by positivity) ha128
  have hψc : Continuous (fun v : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper v))) := by
    have h1 : Continuous fun v : G.UT (n + 1) → ℂ => G.superSum (G.upper v) := by
      unfold G.superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp Dx2.SL.cont_upper)
    unfold G.psi
    exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul h1))))
  have hΦc : ∀ t : ℂ, t ≠ 0 → Continuous (fun v : G.UT (n + 1) → ℂ => Φ (Zv n t v)) := by
    intro t ht
    have hZc : Continuous (fun v : G.UT (n + 1) → ℂ => Zv n t v) := by
      show Continuous (fun v : G.UT (n + 1) → ℂ =>
        (G.ptLong (n + 1) t * G.upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      exact continuous_const.matrix_mul Dx2.SL.cont_upper
    exact continuous_iff_continuousAt.2 fun v => ((hΦreg _ (hZne t ht v)).1.continuousAt).comp hZc.continuousAt
  have hCc : 0 ≤ C * c := by
    have h := (hΦreg _ (hZne t0 ht0 0)).2 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    have hp : 0 < (1 + ‖Zv n t0 0‖) ^ (-a) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hp
    linarith [norm_nonneg (Φ (Zv n t0 0))]
  have hbound : ∀ t : ℂ, t ≠ 0 → ∀ v : G.UT (n + 1) → ℂ,
      ‖G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v)‖ ≤ C * c * (min 1 ‖t‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro t ht v
    rw [norm_smul, Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.norm_psi, one_mul]
    have h := (hΦreg _ (hZne t ht v)).2 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_left (Zv_decay n ht v ha0) hCc
    rw [← mul_assoc] at this
    exact this
  have hfin : (Module.finrank ℝ (G.UT (n + 1) → ℂ) : ℝ) < a := by
    have e : Module.finrank ℝ (G.UT (n + 1) → ℂ) = Fintype.card (G.UT (n + 1)) * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    have hcard : Fintype.card (G.UT (n + 1)) ≤ (n + 1) * (n + 1) := by
      have := Fintype.card_subtype_le (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)
      simpa [Fintype.card_prod, Fintype.card_fin] using this
    have hcardR : ((Fintype.card (G.UT (n + 1)) * 2 : ℕ) : ℝ) ≤ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
      have : Fintype.card (G.UT (n + 1)) * 2 ≤ 2 * ((n + 1) * (n + 1)) := by omega
      exact_mod_cast this
    rw [e]
    refine lt_of_le_of_lt hcardR (lt_of_lt_of_le ?_ ha128)
    have hn : ((n : ℝ) + 1) ≤ ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg ph : (0:ℝ) ≤ ph), (Nat.cast_nonneg ρ : (0:ℝ) ≤ ρ)]
    have hAs' : (1 : ℝ) ≤ As := by exact_mod_cast hAs1
    set R1 : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1
    have hR1 : 1 ≤ R1 := by
      have : (0 : ℝ) ≤ ((ph + (n + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hn0 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have h1 : 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ 2 * (R1 * R1) := by gcongr
    have h2 : 2 * (R1 * R1) < 128 * R1 ^ 3 := by nlinarith
    have h3 : 128 * R1 ^ 3 ≤ 128 * R1 ^ 3 * (As : ℝ) := by nlinarith
    linarith
  set m0 : ℝ := min 1 (‖t0‖ / 2) with hm0
  have hm0p : 0 < m0 := lt_min one_pos (by positivity)
  have hbound' : ∀ t : ℂ, dist t t0 < δ0 → ∀ v : G.UT (n + 1) → ℂ,
      ‖G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v)‖ ≤ C * c * m0 ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro t ht v
    obtain ⟨h2, ht', -⟩ := hnear t ht
    refine (hbound t ht' v).trans ?_
    have hmle : m0 ≤ min 1 ‖t‖ := min_le_min le_rfl h2
    have h3 : (min 1 ‖t‖) ^ (-a) ≤ m0 ^ (-a) := Real.rpow_le_rpow_of_nonpos hm0p hmle (by linarith)
    have hv : 0 ≤ (1 + ‖v‖) ^ (-a) := Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hCc) hv
  have hgint : Integrable (fun v : G.UT (n + 1) → ℂ => C * c * m0 ^ (-a) * (1 + ‖v‖) ^ (-a))
      (G.muPi U.betaU (G.UT (n + 1))) := by
    rw [Dx2.SL.muPi_betaU]
    apply Integrable.smul_measure_nnreal
    exact (integrable_one_add_norm hfin).const_mul _

  let Wt : ℂ → V := fun t =>
    ∫ v, G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v) ∂(G.muPi U.betaU (G.UT (n + 1)))
  have hWc : ContinuousAt Wt t0 := by
    have hball : ∀ᶠ t in 𝓝 t0, dist t t0 < δ0 := Metric.ball_mem_nhds t0 hδ0
    refine continuousAt_of_dominated ?_ ?_ hgint ?_
    · filter_upwards [hball] with t ht
      exact (hψc.smul (hΦc t (hnear t ht).2.1)).aestronglyMeasurable
    · filter_upwards [hball] with t ht
      exact Eventually.of_forall (hbound' t ht)
    · refine Eventually.of_forall fun v => ?_
      exact continuousAt_const.smul (ContinuousAt.comp (g := Φ) (f := fun t : ℂ => Zv n t v) (x := t0)
        ((hΦreg _ (hZne t0 ht0 v)).1.continuousAt) (continuous_unipotent_vector_scalar n v).continuousAt)

  have key : ∀ t : ℂ, dist t t0 < δ0 → ∀ γ ∈ B.GV k ρ,
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ = MM.ev (((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) • Wt t) γ () := by
    intro t ht γ hγ
    have ht' := (hnear t ht).2.1
    have hφint : Integrable (fun v : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v))
        (G.muPi U.betaU (G.UT (n + 1))) :=
      hgint.mono' (hψc.smul (hΦc t ht')).aestronglyMeasurable (Eventually.of_forall (hbound' t ht))
    have hgN : 0 < B.gN γ ^ a := Real.rpow_pos_of_pos (Formalism.FourierDecayAlt.P.Ux1.gN_pos hγ) a
    let L₀ : V →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : Unit => Wq →L[ℂ] Wp) ()) ∘ₗ
        (LinearMap.proj (R := ℂ) (φ := fun _ : B.Mat k ρ => Unit → (Wq →L[ℂ] Wp)) γ) ∘ₗ MM.ev
    have hL₀ : ∀ w, L₀ w = MM.ev w γ () := fun w => rfl
    have hbd : ∀ w, ‖L₀ w‖ ≤ (B.gN γ ^ a)⁻¹ * ‖w‖ := by
      intro w
      rw [hL₀]
      have h1 := (MM.mem w).2 [] [] (by simp) (by simp) (by simp) γ hγ
      rw [inv_mul_eq_div, le_div_iff₀' hgN]
      exact le_trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ ()) hgN.le) h1
    let L : V →L[ℂ] (Wq →L[ℂ] Wp) := L₀.mkContinuous _ hbd
    have hL : ∀ w, L w = MM.ev w γ () := fun w => rfl
    have hΨ : ∀ v : G.UT (n + 1) → ℂ,
        U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F (Zv n t v) γ = MM.ev (Φ (Zv n t v)) γ () := by
      intro v
      rw [hΦev _ (hZne t ht' v) γ hγ]
      show _ = (U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' (UD.F1 f) (Zv n t v) γ) ()
      unfold U.PhiFun
      have e := (ContinuousLinearEquiv.funUnique Unit ℂ (Wq →L[ℂ] Wp)).integral_comp_comm
        (μ := U.muXi k ph (n + 1) ρ σ)
        (fun ξ => U.psiStar k ρ σ z z' ξ • UD.F1 f (U.gaXi k ρ σ d ξ (Zv n t v) γ))
      refine Eq.trans ?_ e
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      show U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (Zv n t v) γ) =
        U.psiStar k ρ σ z z' ξ • F₁ (U.gaXi k ρ σ d ξ (Zv n t v) γ)
      rw [hOrb t ht ξ v γ hγ]
    rw [hcore t ht γ hγ]
    have hOm : G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t = L (Wt t) := by
      show _ = L (∫ v, G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v) ∂(G.muPi U.betaU (G.UT (n + 1))))
      rw [← L.integral_comp_comm hφint]
      unfold G.OmLong
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      show G.psi U.betaU (G.superSum (G.upper v)) • U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F (Zv n t v) γ =
        L (G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v))
      rw [L.map_smul, hL, hΨ v]
    rw [hOm, hL, map_smul]
    rfl

  have hAa : A ≤ a := le_trans hA ha128
  have hCCv : ∀ w : V, B.CCle A mm (fun γ => MM.ev w γ ()) ‖w‖ := fun w =>
    Formalism.FourierDecayAlt.P.compactly_supported_monotone k ρ (Wq →L[ℂ] Wp) a A ‖w‖ mm _ hAa (ccle_unit (MM.mem w))
  set πc : ℂ := ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) with hπc
  have hWfc : ContinuousAt (fun t => πc • Wt t) t0 := continuousAt_const.smul hWc
  obtain ⟨δ2, hδ2, hδ2c⟩ := Metric.continuousAt_iff.mp hWfc 1 one_pos
  have hself : dist t0 t0 < δ0 := by rw [dist_self]; exact hδ0
  refine ⟨min δ0 δ2, ‖πc • Wt t0‖ + 1, fun t => ‖πc • Wt t - πc • Wt t0‖, lt_min hδ0 hδ2,
    tendsto_iff_norm_sub_tendsto_zero.mp hWfc, fun t ht => ?_⟩
  have ht0' : dist t t0 < δ0 := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 : dist t t0 < δ2 := lt_of_lt_of_le ht (min_le_right _ _)
  refine ⟨(hnear t ht0').2.1, ?_, ?_, ?_⟩
  · have h1 := Formalism.FourierDecayAlt.P.Ux1.cc_congr (fun γ hγ => (key t ht0' γ hγ).symm) (hCCv (πc • Wt t))
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c h1 ?_
    have h2 := hδ2c ht2
    simp only [dist_eq_norm] at h2
    have h3 := norm_le_insert' (πc • Wt t) (πc • Wt t0)
    linarith
  · intro γ hγ hne
    by_contra hlt
    have hnot : γ ∉ UD.S := fun h => hlt h
    apply hne
    rw [key t ht0' γ hγ, MM.off _ γ hγ hnot]
    rfl
  · have heq : ∀ γ ∈ B.GV k ρ, MM.ev (πc • Wt t - πc • Wt t0) γ () = U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ - U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t0) z z' F (fun a => a.elim0) γ := by
      intro γ hγ
      rw [key t ht0' γ hγ, key t0 hself γ hγ, map_sub]
      try rfl
    exact Formalism.FourierDecayAlt.P.Ux1.cc_congr heq (hCCv (πc • Wt t - πc • Wt t0))

end Formalism.FourierDecayAlt.P.LastBlockContinuity
end
end

section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem xs_eq_phi {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (i : ℕ) (hi : i ≤ r) (w : List C.Letter)
    (a : Wd.Ix (Fin w.length)) (h0 : C.LPt) (n : ℕ) (t : ℂ) (hc : r - i = r - D.ptSize (h0 ++ [(n + 1, t)]))
    (hpb : ∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) (ht : t ≠ 0) (hsz : D.ptSize (h0 ++ [(n + 1, t)]) = i)
    (e1 : r = D.ptSize h0 + (n + 1) + (r - i)) (e2 : D.ptSize h0 + (n + 1) + (r - i) = r)
    (hh : B.Mat k r → (Wq →L[ℂ] Wp)) :
    PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) hc hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ := by
  subst hsz
  have hP : D.ptSize (h0 ++ [(n + 1, t)]) = D.ptSize h0 + (n + 1) := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h0 (n + 1) t
  have hloc : D.IsLocPt (h0 ++ [(n + 1, t)]) (D.ptSize (h0 ++ [(n + 1, t)])) := by
    refine ⟨fun b hb => ?_, rfl⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hpb b hb
    · simp only [List.mem_singleton] at hb
      subst hb
      exact ⟨by omega, ht⟩
  have hlocH := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  have hσ : ∀ q : Fin (D.ptSize (h0 ++ [(n + 1, t)])),
      ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h0)) (Fin.cast hP q)).val = (D.ptPerm (h0 ++ [(n + 1, t)]) q).val := by
    intro q
    rw [hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h0 q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h0
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨q.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h0) ⟨q.val - D.ptSize h0, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ q : Fin (D.ptSize (h0 ++ [(n + 1, t)])),
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h0) t (Fin.cast hP q) = D.ptDiag (h0 ++ [(n + 1, t)]) q := by
    intro q
    simp only [D.ptDiag]
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h0 q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h0
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h0) ⟨q.val - D.ptSize h0, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]
  set ρ := r - D.ptSize (h0 ++ [(n + 1, t)]) with hρ
  have hS : ∀ (Gx : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ), D.sliceAt k r T.base.z T.base.z' Gx (h0 ++ [(n + 1, t)]) γ =
      U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) Gx) (fun a => a.elim0) γ := by
    intro Gx γ
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) γ
    unfold D.sliceAt
    rw [dif_pos (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  unfold PBE.xs
  rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]
  funext γ
  exact hS _ γ

theorem ccCoefM_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {e e' : ℝ} {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : JC.CCCoefM Bs A mm e F) (he : e' ≤ e) : JC.CCCoefM Bs A mm e' F :=
  ⟨h.1, h.2.1, fun g hg hne => le_trans he (h.2.2 g hg hne)⟩

theorem sliceContQa : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
    ∀ (h0 : C.LPt) (m : ℕ) (hc : ∀ t : ℂ, r - i = r - D.ptSize (h0 ++ [(m, t)])),
    (∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) → 1 ≤ m → D.ptSize h0 + m = i →
    ∀ t0 : ℂ, t0 ≠ 0 → ∀ (a : Wd.Ix (Fin w.length)), ∃ ε' : ℝ, 0 < ε' ∧
      ∀ (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) Kb ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) (Dd t) := by
  obtain ⟨Cp, hCp0, hCp⟩ := posCoreCont
  refine ⟨16 * Cp, by positivity, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0 a
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hPt : ∀ t : ℂ, D.ptSize (h0 ++ [(n + 1, t)]) = i := fun t => by
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append]; exact hsz
  have hd0 : ∀ q, D.ptDiag h0 q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h0 hpb q q.2
  have e1 : r = D.ptSize h0 + (n + 1) + (r - i) := by omega
  have e2 : D.ptSize h0 + (n + 1) + (r - i) = r := by omega
  have hj1 : 1 ≤ D.ptSize h0 + (n + 1) := by omega
  obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (D.ptSize h0 + (n + 1)) (r - i) Wp Wq (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (by omega) w a hj1
  have hU : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (D.ptSize h0 + (n + 1) + (r - i)), U.DjU k (D.ptSize h0 + (n + 1)) (r - i) g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) g =
        B.opApply Θ (D.castF e2 (D.cutF T.base χ hh ε)) g := by
    intro hh hsm g hg hD
    have hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ hh ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hsm ε
    have h1 : D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) =
        D.uwG k (D.ptSize h0 + (n + 1) + (r - i)) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.cutF T.base χ hh ε)) (D.ptSize h0 + (n + 1)) (by omega) w a := by
      rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hsz.symm _ _ w a
    rw [h1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD]
  have hFrel : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (D.ptSize h0 + (n + 1) + (r - i)), U.DjU k (D.ptSize h0 + (n + 1)) (r - i) g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) g =
        B.opApply Θ (fun x => ((χ (Gf k (D.ptSize h0 + (n + 1) + (r - i)) (D.castV e1 T.base.z)
          (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 hh x) g := by
    intro hh hsm g hg hD
    rw [hU hh hsm g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]
  set nd := 2 * r + k + 1 with hnd
  set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs
  obtain ⟨b1, b2, b3, b4, b5⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs r k N w.length (D.ptSize h0 + (n + 1)) hk2 hw (by omega)
  have hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r := by
    simp only [P5.mmUser, P5.nV, hPk, hPr, hnd]
  have hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by
    simp only [P5.Auser, P5.nV, hPk, hPr, hnd]
    try (push_cast; try ring)
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by exact_mod_cast b5
  have hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5 := by
    rw [hAs]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hsumR : (((D.ptSize h0 + (n + 1) + (r - i) : ℕ) : ℝ)) = (r : ℝ) := by exact_mod_cast e2
  obtain ⟨ε', hε', hQ⟩ := hCp k (D.ptSize h0) n (r - i) Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
    Θ _ _ hΘ χ A₀ ε hχ hε (D.ptPerm h0) (D.ptDiag h0) t0 hd0 ht0 As (P5.mmUser P0 N) (P5.Auser P0 N + 1)
    b1 b2 (by rw [hmmU]; exact b3) (by rw [e2]; exact b4)
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
  have hz1 : U.lowV k (D.ptSize h0 + (n + 1)) (r - i) (D.castV e1 T.base.z) = (T.bs i).z := by
    have hzl : T.base.z = D.castV (by omega) (liftVec k i (r - i) (T.bs i).z) := (T.z_lev _ hi).symm
    rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hsz _ _
  have hz1' : U.lowV k (D.ptSize h0 + (n + 1)) (r - i) (D.castV e1 T.base.z') = (T.bs i).z' := by
    have hzl' : T.base.z' = D.castV (by omega) (liftVec k i (r - i) (T.bs i).z') := (T.z'_lev _ hi).symm
    rw [hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hsz _ _
  refine ⟨ε', hε', fun hh c hsm hcl => ?_⟩
  obtain ⟨δ, Kb, Dd, hδ, hDd, hnear⟩ := hQ (D.castF e2 hh) c (PBE.ccle_castF e2 hcl) _ (hFrel hh hsm)
  have key : ∀ t : ℂ, t ≠ 0 → PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) (hc t) hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ :=
    fun t ht => xs_eq_phi T χ ε i hi w a h0 n t (hc t) hpb ht (hPt t) e1 e2 hh
  obtain ⟨-, -, hsupp0, -⟩ := hnear t0 (by rw [dist_self]; exact hδ)
  refine ⟨δ, Kb, Dd, hδ, hDd, fun t ht => ?_⟩
  obtain ⟨htne, hB, hsupp, hD⟩ := hnear t ht
  have hsub : PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) (hc t) hh a -
      PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t0)]) (hc t0) hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ -
        U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t0) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ := by
    rw [key t htne, key t0 ht0]; rfl
  rw [hsub, key t htne]
  refine ⟨htne, ⟨hB.1, ⟨_, hB⟩, fun γ hγ hne => ?_⟩, hB, ⟨hD.1, ⟨_, hD⟩, fun γ hγ hne => ?_⟩, hD⟩
  · have := hsupp γ hγ hne
    rwa [hz1, hz1'] at this
  · by_cases h1 : U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ = 0
    · have hne0 : U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
          (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t0) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ ≠ 0 := by
        intro h2; apply hne; simp only [h1, h2, sub_zero]
      have := hsupp0 γ hγ hne0
      rwa [hz1, hz1'] at this
    · have := hsupp γ hγ h1
      rwa [hz1, hz1'] at this

theorem sliceContQ : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
    ∀ (h0 : C.LPt) (m : ℕ) (hc : ∀ t : ℂ, r - i = r - D.ptSize (h0 ++ [(m, t)])),
    (∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) → 1 ≤ m → D.ptSize h0 + m = i →
    ∀ t0 : ℂ, t0 ≠ 0 → ∃ ε' : ℝ, 0 < ε' ∧ ∀ (a : Wd.Ix (Fin w.length))
      (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) Kb ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) (Dd t) := by
  obtain ⟨Cs, hCs0, hCs⟩ := sliceContQa
  refine ⟨Cs, hCs0, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0
  have H := fun a : Wd.Ix (Fin w.length) =>
    hCs Cc hCc k r Wp Wq T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0 a
  choose ef hef hP using H
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ef,
    (Finset.lt_inf'_iff Finset.univ_nonempty).2 (fun a _ => hef a), fun a hh c hsm hcl => ?_⟩
  have hle : Finset.univ.inf' Finset.univ_nonempty ef ≤ ef a := Finset.inf'_le _ (Finset.mem_univ a)
  obtain ⟨δ, Kb, Dd, hδ, hDd, hn⟩ := hP a hh c hsm hcl
  refine ⟨δ, Kb, Dd, hδ, hDd, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hn t ht
  exact ⟨h1, ccCoefM_mono h2 hle, h3, ccCoefM_mono h4 hle, h5⟩

end Formalism.FourierDecayAlt.P.LastBlockContinuity
end
end

section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBE NumberField

theorem formLev_tendsto {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) {ι : Type} (l : Filter ι)
    (x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (xn yn : ι → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (Bd : ℝ) (dn : ι → ℝ)
    (hdn : Tendsto dn l (𝓝 0))
    (hx : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (x e) Bd)
    (hy : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (y e) Bd)
    (hev : ∀ᶠ n in l, (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e) Bd) ∧
      (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e - x e) (dn n)) ∧
      (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e - y e) (dn n))) :
    Tendsto (fun n => D.formLev T s j w (xn n) (yn n)) l (𝓝 (D.formLev T s j w x y)) := by
  have hAu : P5.Auser P0 w.length + 1 ≤ P5.Auser P0 N + 1 := by linarith [auser_mono P0 hw]
  have hmu : P5.mmUser P0 w.length ≤ P5.mmUser P0 N := mmUser_mono P0 hw
  have hS := Formalism.FourierDecayAlt.P.level_form_sesquilinear_moderate Wp Wq P0 T s j w (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ hε₀ hAu hmu
  obtain ⟨Cf, hCf0, hCf⟩ := Formalism.FourierDecayAlt.P.JCx4.formLev_bound_mm P0 T s j w (P5.Auser P0 N + 1 + 1) (by linarith)
  have hmm5 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 N := by
    have := Formalism.FourierDecayAlt.P.JCx2.pd_thr_mm P0 j N (P5.mmUser P0 N) le_rfl
    have h2 : (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ (2 * (P0.r - (j : ℕ)) + P0.k + 1) * N :=
      Nat.mul_le_mul_left _ hw
    omega
  have h5 : 5 ≤ P5.mmUser P0 N := by unfold P5.mmUser; omega
  have hu : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u e) cu := by
    intro u cu h e
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmm5 (h e))
  have hv : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1 - 2 * (w.length : ℝ)) 5 (u e) cu := by
    intro u cu h e
    have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m h5 (h e))
  have key : ∀ n, (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e)) →
      (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e)) →
      (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e)) →
      D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y =
        D.formLev T s j w (xn n - x) (yn n) + D.formLev T s j w x (yn n - y) := by
    intro n hyn hdx hdy
    have e1 : xn n = x + (1 : ℂ) • (xn n - x) := by simp
    have e2 : yn n = y + (1 : ℂ) • (yn n - y) := by simp
    have s1 := (hS x (xn n - x) (yn n) 1 (fun e => (hx e).1) hdx hyn).1
    have s2 := (hS y (yn n - y) x 1 (fun e => (hy e).1) hdy (fun e => (hx e).1)).2
    rw [← e1] at s1
    rw [← e2] at s2
    rw [s1, s2]
    simp
    ring
  have hbd : ∀ᶠ n in l, ‖D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y‖ ≤ 2 * Cf * Bd * dn n := by
    filter_upwards [hev] with n hn
    obtain ⟨hyn, hdx, hdy⟩ := hn
    rw [key n (fun e => (hyn e).1) (fun e => (hdx e).1) (fun e => (hdy e).1)]
    have b1 := hCf (xn n - x) (yn n) (dn n) Bd (hu _ _ fun e => (hdx e).2) (hv _ _ fun e => (hyn e).2)
    have b2 := hCf x (yn n - y) Bd (dn n) (hu _ _ fun e => (hx e).2) (hv _ _ fun e => (hdy e).2)
    calc _ ≤ ‖D.formLev T s j w (xn n - x) (yn n)‖ + ‖D.formLev T s j w x (yn n - y)‖ := norm_add_le _ _
      _ ≤ Cf * dn n * Bd + Cf * Bd * dn n := add_le_add b1 b2
      _ = 2 * Cf * Bd * dn n := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => 2 * Cf * Bd * dn n) l (𝓝 0) := by
    simpa using hdn.const_mul (2 * Cf * Bd)
  exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hbd hlim

theorem continuousOn_weight_product (k r : ℕ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 < fr b s) (m : ℕ) :
    ∀ (H : C.LPt) (b : ℕ), ContinuousOn (fun q : ℝ × ℂ => C.nAux k r q.1 fr b (H ++ [(m, q.2)]))
      (Set.univ ×ˢ {0}ᶜ)
  | [], b => by
    simp only [List.nil_append, C.nAux, mul_one]
    split_ifs
    · exact (continuous_fst.pow _).continuousOn
    · refine ContinuousOn.zpow₀ ?_ _ ?_
      · exact (continuous_const.mul (continuous_norm.comp continuous_snd)).continuousOn
      · intro q hq
        left
        exact mul_ne_zero (hfr b m).ne' (norm_ne_zero_iff.mpr hq.2)
  | (s, t) :: H, b => by
    simp only [List.cons_append, C.nAux]
    refine ContinuousOn.mul ?_ (continuousOn_weight_product k r fr hfr m H (b + s))
    split_ifs
    · exact (continuous_fst.pow _).continuousOn
    · exact continuousOn_const

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem fr_pos (S : C.HidaSetting E Wp Wq) (b s : ℕ) : 0 < S.fr b s := by
  unfold C.HidaSetting.fr
  exact Real.rpow_pos_of_pos (Formalism.FourierDecayAlt.P.PBD.rd_pos' E) _

theorem nnS_cont (S : C.HidaSetting E Wp Wq) (P : C.LPt) (m : ℕ) :
    ContinuousOn (fun c : ℂ => PBL.nnS S (P ++ [(m, c)])) {0}ᶜ := by
  have h1 := continuousOn_weight_product S.G.k S.G.r S.fr (fr_pos S) m P 1
  have hmap : Set.MapsTo (fun c : ℂ => ((Complex.normSq c - S.T * S.T' : ℝ), c)) {0}ᶜ (Set.univ ×ˢ {0}ᶜ) :=
    fun c hc => ⟨Set.mem_univ _, hc⟩
  have h2 := h1.comp (Continuous.continuousOn (by fun_prop)) hmap
  refine h2.congr fun c _ => ?_
  simp only [Function.comp, PBL.nnS, C.nLoc]
  congr 1
  simp [D.ptGG, D.ptLast]

end setting

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem isLocPt_app {h : C.LPt} (hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) {m : ℕ} (hm : 1 ≤ m) {c : ℂ} (hc : c ≠ 0)
    {i : ℕ} (hsz : D.ptSize h + m = i) : D.IsLocPt (h ++ [(m, c)]) i := by
  refine ⟨fun b hb => ?_, ?_⟩
  · rcases List.mem_append.1 hb with hb | hb
    · exact hh b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact ⟨hm, hc⟩
  · rw [← hsz]
    simp [D.ptSize]

theorem heads_of_loc {h : C.LPt} {m : ℕ} {c : ℂ} {i : ℕ} (hl : D.IsLocPt (h ++ [(m, c)]) i) :
    ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0 := fun b hb => hl.1 b (List.mem_append_left _ hb)

theorem rrTop_cont (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef p.T.base F)
    (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (w : List C.Letter) (hw : KB.CutWord P p.l0 w)
    (h h' : C.LPt) (m : ℕ) (hm : 1 ≤ m) (hsz : D.ptSize h + m = P.r + 1) (hsz' : D.ptSize h' + m = P.r + 1) :
    ContinuousOn (fun cc : ℂ × ℂ => p.RR F (P.r + 1) w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
  by_cases hh : (∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) ∧ (∀ b ∈ h', 1 ≤ b.1 ∧ b.2 ≠ 0)
  · obtain ⟨hh1, hh2⟩ := hh
    have hform : ∀ cc ∈ (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)),
        p.RR F (P.r + 1) w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]) =
          (if w = [] then B.hsInner (p.V F (h ++ [(m, cc.1)])) (p.V F (h' ++ [(m, cc.2)]))
            else Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)])) := by
      intro cc hcc
      have l1 := isLocPt_app hh1 hm hcc.1 hsz
      have l2 := isLocPt_app hh2 hm hcc.2 hsz'
      unfold KB.Pl.RR D.RRplace
      rw [dif_pos ⟨l1, l2⟩, dif_neg (by omega), if_pos rfl]
      rfl
    by_cases hw0 : w = []
    · refine (hsV_continuousOn P p F hF h h' hh1 hh2 m hm hsz hsz').congr fun cc hcc => ?_
      rw [hform cc hcc, if_pos hw0]
    · refine (topOf_continuousOn P p F hF Cb hCb w hw h h' hh1 hh2 m hm hsz hsz').congr fun cc hcc => ?_
      rw [hform cc hcc, if_neg hw0]
  · refine (continuousOn_const (c := (0 : ℂ))).congr fun cc _ => ?_
    exact PBL.rr_zero_of_not p F _ w _ _ (fun hl => hh ⟨heads_of_loc hl.1, heads_of_loc hl.2⟩)

end place

section below

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hc_app {r i : ℕ} (h0 : C.LPt) (m : ℕ) (hsz : D.ptSize h0 + m = i) (t : ℂ) :
    r - i = r - D.ptSize (h0 ++ [(m, t)]) := by
  rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append, hsz]

def SlcOK {k r : ℕ} (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (i : ℕ) (hi : i ≤ r) (w : List C.Letter)
    (N : ℕ) (P0 : M.Par) (h0 : C.LPt) (m : ℕ) (hsz : D.ptSize h0 + m = i) (hcf : B.Mat k r → (Wq →L[ℂ] Wp))
    (t0 : ℂ) : Prop :=
  ∃ ε' : ℝ, 0 < ε' ∧ ∀ a : Wd.Ix (Fin w.length), ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧
    ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
      JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (xs T χ ε i hi w (h0 ++ [(m, t)]) (hc_app h0 m hsz t) hcf a) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xs T χ ε i hi w (h0 ++ [(m, t)]) (hc_app h0 m hsz t) hcf a) Kb ∧
      JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
        (xs T χ ε i hi w (h0 ++ [(m, t)]) (hc_app h0 m hsz t) hcf a - xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc_app h0 m hsz t0) hcf a) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
        (xs T χ ε i hi w (h0 ++ [(m, t)]) (hc_app h0 m hsz t) hcf a - xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc_app h0 m hsz t0) hcf a) (Dd t)

theorem ccCoefM_le {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {ε₁ ε₂ : ℝ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : JC.CCCoefM Bs A mm ε₁ F) (hle : ε₂ ≤ ε₁) : JC.CCCoefM Bs A mm ε₂ F :=
  ⟨h.1, h.2.1, fun g hg hne => le_trans hle (h.2.2 g hg hne)⟩

theorem rrBelow_cont (P : M.Par) (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (hcf : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (i : ℕ) (hi : i ≤ P.r) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N) (h h' : C.LPt) (m : ℕ) (hm : 1 ≤ m)
    (hsz : D.ptSize h + m = i) (hsz' : D.ptSize h' + m = i)
    (hS : (∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) → ∀ t0 : ℂ, t0 ≠ 0 → SlcOK p.T χ ε i hi w N P h m hsz hcf t0)
    (hS' : (∀ b ∈ h', 1 ≤ b.1 ∧ b.2 ≠ 0) → ∀ t0 : ℂ, t0 ≠ 0 → SlcOK p.T χ ε i hi w N P h' m hsz' hcf t0) :
    ContinuousOn (fun cc : ℂ × ℂ => p.RR (D.cutF p.T.base χ hcf ε) i w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
  by_cases hh : (∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) ∧ (∀ b ∈ h', 1 ≤ b.1 ∧ b.2 ≠ 0)
  · obtain ⟨hh1, hh2⟩ := hh
    set S : Set (ℂ × ℂ) := ({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ) with hSdef
    have hlt : i < P.r + 1 := by omega
    have hform : ∀ cc ∈ S, p.RR (D.cutF p.T.base χ hcf ε) i w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]) =
        D.formLev p.T (M.sgn P p.l0) ⟨i, hlt⟩ w
          (fun a => xs p.T χ ε i hi w (h ++ [(m, cc.1)]) (hc_app h m hsz cc.1) hcf a)
          (fun a => xs p.T χ ε i hi w (h' ++ [(m, cc.2)]) (hc_app h' m hsz' cc.2) hcf a) := by
      intro cc hcc
      have l1 := isLocPt_app hh1 hm hcc.1 hsz
      have l2 := isLocPt_app hh2 hm hcc.2 hsz'
      unfold KB.Pl.RR D.RRplace
      rw [dif_pos ⟨l1, l2⟩, dif_pos hi]
      rfl
    rintro ⟨c0, c0'⟩ ⟨hc0, hc0'⟩
    obtain ⟨ε1, hε1, H1⟩ := hS hh1 c0 hc0
    obtain ⟨ε2, hε2, H2⟩ := hS' hh2 c0' hc0'
    choose δ1 Kb1 Dd1 hδ1 hDd1 hb1 using H1
    choose δ2 Kb2 Dd2 hδ2 hDd2 hb2 using H2
    set ε₀ : ℝ := min ε1 ε2 with hε₀
    have hε₀p : 0 < ε₀ := lt_min hε1 hε2
    set Bd : ℝ := ∑ a, (|Kb1 a| + |Kb2 a|) with hBd
    have hK1 : ∀ a, Kb1 a ≤ Bd := fun a => le_trans (le_abs_self _) (le_trans (le_add_of_nonneg_right (abs_nonneg _))
      (Finset.single_le_sum (f := fun b => |Kb1 b| + |Kb2 b|) (fun b _ => by positivity) (Finset.mem_univ a)))
    have hK2 : ∀ a, Kb2 a ≤ Bd := fun a => le_trans (le_abs_self _) (le_trans (le_add_of_nonneg_left (abs_nonneg _))
      (Finset.single_le_sum (f := fun b => |Kb1 b| + |Kb2 b|) (fun b _ => by positivity) (Finset.mem_univ a)))
    set dn : ℂ × ℂ → ℝ := fun cc => ∑ a, (Dd1 a cc.1 + Dd2 a cc.2) with hdn
    have hdnT : Tendsto dn (𝓝[S] (c0, c0')) (𝓝 0) := by
      have h1 : Tendsto dn (𝓝 (c0, c0')) (𝓝 (∑ _a : Wd.Ix (Fin w.length), ((0 : ℝ) + 0))) :=
        tendsto_finsetSum _ fun a _ =>
          ((hDd1 a).comp (continuous_fst.tendsto (c0, c0'))).add ((hDd2 a).comp (continuous_snd.tendsto (c0, c0')))
      simp only [add_zero, Finset.sum_const_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have hball : ∀ᶠ cc in 𝓝[S] (c0, c0'), ∀ a, dist cc.1 c0 < δ1 a ∧ dist cc.2 c0' < δ2 a := by
      refine nhdsWithin_le_nhds (Filter.eventually_all.2 fun a => ?_)
      exact ((continuous_fst.tendsto (c0, c0')).eventually (Metric.ball_mem_nhds c0 (hδ1 a))).and
        ((continuous_snd.tendsto (c0, c0')).eventually (Metric.ball_mem_nhds c0' (hδ2 a)))
    have hs1 : dist c0 c0 < 0 + 1 := by rw [dist_self]; norm_num
    have hx0 : ∀ a, JC.CCCoefM (p.T.bs (i : ℕ)) (P5.Auser P N + 1) (P5.mmUser P N) ε₀
          (xs p.T χ ε i hi w (h ++ [(m, c0)]) (hc_app h m hsz c0) hcf a) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w (h ++ [(m, c0)]) (hc_app h m hsz c0) hcf a) Bd := by
      intro a
      obtain ⟨-, q1, q2, -, -⟩ := hb1 a c0 (by rw [dist_self]; exact hδ1 a)
      exact ⟨ccCoefM_le q1 (min_le_left _ _), Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c q2 (hK1 a)⟩
    have hy0 : ∀ a, JC.CCCoefM (p.T.bs (i : ℕ)) (P5.Auser P N + 1) (P5.mmUser P N) ε₀
          (xs p.T χ ε i hi w (h' ++ [(m, c0')]) (hc_app h' m hsz' c0') hcf a) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w (h' ++ [(m, c0')]) (hc_app h' m hsz' c0') hcf a) Bd := by
      intro a
      obtain ⟨-, q1, q2, -, -⟩ := hb2 a c0' (by rw [dist_self]; exact hδ2 a)
      exact ⟨ccCoefM_le q1 (min_le_right _ _), Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c q2 (hK2 a)⟩
    have hT := formLev_tendsto P p.T (M.sgn P p.l0) ⟨i, hlt⟩ w N hw ε₀ hε₀p (𝓝[S] (c0, c0'))
      (fun a => xs p.T χ ε i hi w (h ++ [(m, c0)]) (hc_app h m hsz c0) hcf a)
      (fun a => xs p.T χ ε i hi w (h' ++ [(m, c0')]) (hc_app h' m hsz' c0') hcf a)
      (fun cc a => xs p.T χ ε i hi w (h ++ [(m, cc.1)]) (hc_app h m hsz cc.1) hcf a)
      (fun cc a => xs p.T χ ε i hi w (h' ++ [(m, cc.2)]) (hc_app h' m hsz' cc.2) hcf a) Bd dn hdnT hx0 hy0 ?_
    · have hcc0 : ((c0, c0') : ℂ × ℂ) ∈ S := ⟨hc0, hc0'⟩
      have e0 : p.RR (D.cutF p.T.base χ hcf ε) i w (h ++ [(m, c0)]) (h' ++ [(m, c0')]) =
          D.formLev p.T (M.sgn P p.l0) ⟨i, hlt⟩ w
            (fun a => xs p.T χ ε i hi w (h ++ [(m, c0)]) (hc_app h m hsz c0) hcf a)
            (fun a => xs p.T χ ε i hi w (h' ++ [(m, c0')]) (hc_app h' m hsz' c0') hcf a) := hform (c0, c0') hcc0
      show Tendsto _ (𝓝[S] (c0, c0')) (𝓝 (p.RR (D.cutF p.T.base χ hcf ε) i w (h ++ [(m, c0)]) (h' ++ [(m, c0')])))
      rw [e0]
      refine hT.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with cc hcc
      exact (hform cc hcc).symm
    · filter_upwards [hball] with cc hcc
      have hn1 : ∀ b, 0 ≤ Dd1 b cc.1 := fun b =>
        Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg (hb1 b cc.1 (hcc b).1).2.2.2.2
      have hn2 : ∀ b, 0 ≤ Dd2 b cc.2 := fun b =>
        Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg (hb2 b cc.2 (hcc b).2).2.2.2.2
      have hle1 : ∀ a, Dd1 a cc.1 ≤ dn cc := fun a =>
        le_trans (le_add_of_nonneg_right (hn2 a))
          (Finset.single_le_sum (f := fun b => Dd1 b cc.1 + Dd2 b cc.2) (fun b _ => add_nonneg (hn1 b) (hn2 b))
            (Finset.mem_univ a))
      have hle2 : ∀ a, Dd2 a cc.2 ≤ dn cc := fun a =>
        le_trans (le_add_of_nonneg_left (hn1 a))
          (Finset.single_le_sum (f := fun b => Dd1 b cc.1 + Dd2 b cc.2) (fun b _ => add_nonneg (hn1 b) (hn2 b))
            (Finset.mem_univ a))
      refine ⟨fun a => ?_, fun a => ?_, fun a => ?_⟩
      · obtain ⟨-, q1, q2, -, -⟩ := hb2 a cc.2 (hcc a).2
        exact ⟨ccCoefM_le q1 (min_le_right _ _), Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c q2 (hK2 a)⟩
      · obtain ⟨-, -, -, q3, q4⟩ := hb1 a cc.1 (hcc a).1
        exact ⟨ccCoefM_le q3 (min_le_left _ _), Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c q4 (hle1 a)⟩
      · obtain ⟨-, -, -, q3, q4⟩ := hb2 a cc.2 (hcc a).2
        exact ⟨ccCoefM_le q3 (min_le_right _ _), Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c q4 (hle2 a)⟩
  · refine (continuousOn_const (c := (0 : ℂ))).congr fun cc _ => ?_
    exact PBL.rr_zero_of_not p _ _ w _ _ (fun hl => hh ⟨heads_of_loc hl.1, heads_of_loc hl.2⟩)

end below

section final

theorem ptSize_toStd' (r : ℕ) (g : ℝ) : ∀ (b : ℕ) (P : C.LPt), D.ptSize (D.toStd r g b P) = D.ptSize P
  | _, [] => rfl
  | b, (s, t) :: rest => by
    have ih := ptSize_toStd' r g (b + s) rest
    simp only [D.toStd, D.ptSize, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem bS_app {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (P : C.LPt) (m : ℕ) (c : ℂ) :
    PBL.bS S (P ++ [(m, c)]) = PBL.bS S (P ++ [(m, 1)]) := by
  simp [PBL.bS, D.bSt]

theorem level_forms_joint_continuity : GermFibreKernels.KerContB := by
  unfold GermFibreKernels.KerContB
  intro Cb
  obtain ⟨Cs, hCs0, hSQ⟩ := sliceContQ
  obtain ⟨c1, h1⟩ := limit_of_module_forms Cb
  refine ⟨max (Cs + 1) c1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  have hB' := hB
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  have hCI : KB.CutInside S := PBCut.cutInside_of_built hB
  have hgpos := PBL.g_pos_of_built hB
  obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
  have hcpt : ∀ ε, 0 < ε → KB.CptCoef (p v).T.base (PBASM.cutSeq S p f χ n v ε) := by
    intro ε hε
    refine (h1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop PBASM.cutN
      (by rw [hl0]; exact hInD) hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)

  have hX1 : (1 : ℝ) ≤ (S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3 := by
    have h1' : (1 : ℝ) ≤ 2 * (S.G.r : ℝ) + S.G.k + 1 := by
      have : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ S.G.k := Nat.cast_nonneg _
      linarith
    have : 1 ≤ (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3 := one_le_pow₀ h1'
    have : 0 ≤ (S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 := by positivity
    linarith
  have hR4 : 1 ≤ ((S.G.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _; linarith)
  have hA' : Cs * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ - 1 := by
    have h1' : (Cs + 1) * ((S.G.r : ℝ) + 1) ^ 4 *
        ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (by positivity)) hA
    have h2 : 1 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
        ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by nlinarith
    nlinarith

  have hk2 : 2 ≤ (D.parOf S v).k := (p v).hl.2.2
  set M := 3 * (11 * (S.Ntop * (2 * (D.parOf S v).r + (D.parOf S v).k + 1) ^ 2 +
    (2 * (D.parOf S v).r + (D.parOf S v).k + 1) ^ 3) + 5) with hM
  obtain ⟨bf, hbf⟩ := hCC M
  have hbf0 : 0 ≤ bf := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A₀ - 1) M (f v) bf := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := (D.parOf S v).k) (r := (D.parOf S v).r)
    (E := Wq (S.pl v) →L[ℂ] Wp (S.pl v)) M
  set hn : B.Mat (D.parOf S v).k (D.parOf S v).r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
    fun g => PBASM.cutN n g • f v g with hhn
  have hneq : hn = fun g => f v g + (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f v g) := by
    funext g
    simp only [hhn, PBE.cut_eq PBASM.cutN (fun n g => rfl) n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : B.CCle (A₀ - 1) M hn (bf + Kp * bf) := by
    rw [hneq]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hbf'
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hKp _ (by positivity) A₀ (f v) bf hbf))) ?_
    have h1' : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : B.CkOn ⊤ (B.GV (D.parOf S v).k (D.parOf S v).r) hn := by
    rw [hneq]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add hCk (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul (-1)
      (Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul (Formalism.FourierDecayAlt.P.JCx2.pd_psi_cd _) hCk))
  have hFn : ∀ ε, PBASM.cutSeq S p f χ n v ε = D.cutF (p v).T.base χ hn ε := by
    intro ε; funext g
    simp only [PBASM.cutSeq, D.cutF, hhn]
    rw [smul_comm]

  unfold GermFibreKernels.KerCont
  intro ε hε i hi a ha m hm P Q hP hQ
  have hGr : (PBL.setC S p (PBASM.cutSeq S p f χ n)).G.r = S.G.r := rfl
  rw [hGr] at hi
  obtain ⟨w, hw⟩ := ha
  have hlen : a.length ≤ S.Ntop := by rw [← hw]; exact le_trans (PBB.len_le_cnt S w v) w.2.2
  have hcw : KB.CutWord (D.parOf S v) (p v).l0 a := by rw [hl0, ← hw]; exact PBD.cutWord_of_adm S hGo hCI w v
  have hszP : D.ptSize (PBL.stdS S P) + m = i := by unfold PBL.stdS; rw [ptSize_toStd']; exact hP
  have hszQ : D.ptSize (PBL.stdS S Q) + m = i := by unfold PBL.stdS; rw [ptSize_toStd']; exact hQ
  have hRR : ContinuousOn (fun cc : ℂ × ℂ => (p v).RR (PBASM.cutSeq S p f χ n v ε) i a
      (PBL.stdS S P ++ [(m, cc.1)]) (PBL.stdS S Q ++ [(m, cc.2)])) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
    rcases Nat.lt_or_ge i (S.G.r + 1) with hlt | hge
    · have hi' : i ≤ (D.parOf S v).r := by show i ≤ S.G.r; omega
      rw [hFn ε]
      refine rrBelow_cont (D.parOf S v) (p v) χ ε hn i hi' a S.Ntop hlen (PBL.stdS S P) (PBL.stdS S Q) m hm
        hszP hszQ ?_ ?_
      · intro hh t0 ht0
        obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl (D.parOf S v).k (D.parOf S v).r (Wp (S.pl v)) (Wq (S.pl v)) (p v).T χ
          (A₀ - 1) S.Ntop (D.parOf S v) rfl rfl hk2 hcut hA' ε hε i hi' a hlen (PBL.stdS S P) m
          (hc_app _ m hszP) hh hm hszP t0 ht0
        exact ⟨ε', hε', fun e => H e hn (bf + Kp * bf) hns hnC⟩
      · intro hh t0 ht0
        obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl (D.parOf S v).k (D.parOf S v).r (Wp (S.pl v)) (Wq (S.pl v)) (p v).T χ
          (A₀ - 1) S.Ntop (D.parOf S v) rfl rfl hk2 hcut hA' ε hε i hi' a hlen (PBL.stdS S Q) m
          (hc_app _ m hszQ) hh hm hszQ t0 ht0
        exact ⟨ε', hε', fun e => H e hn (bf + Kp * bf) hns hnC⟩
    · have hi1 : i = S.G.r + 1 := by omega
      subst hi1
      exact rrTop_cont (D.parOf S v) (p v) _ (hcpt ε hε) Cb (by rw [hl0]; exact hInD) a hcw (PBL.stdS S P)
        (PBL.stdS S Q) m hm hszP hszQ

  have hg0 : (0 : ℝ) < (S.g : ℝ) / (2 * Real.pi) := div_pos hgpos (by positivity)
  set lP : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + D.ptSize P : ℕ) : ℤ) (m : ℤ) : ℝ) : ℂ) *
    Complex.I ^ (m - 1) with hlP
  set lQ : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + D.ptSize Q : ℕ) : ℤ) (m : ℤ) : ℝ) : ℂ) *
    Complex.I ^ (m - 1) with hlQ
  have hlP0 : lP ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (zpow_pos hg0 _).ne') (pow_ne_zero _ Complex.I_ne_zero)
  have hlQ0 : lQ ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (zpow_pos hg0 _).ne') (pow_ne_zero _ Complex.I_ne_zero)
  have eP : ∀ c : ℂ, PBL.stdS S (P ++ [(m, c)]) = PBL.stdS S P ++ [(m, lP * c)] := fun c =>
    PBL.toStd_append_blkT _ _ _ _ _ _
  have eQ : ∀ c : ℂ, PBL.stdS S (Q ++ [(m, c)]) = PBL.stdS S Q ++ [(m, lQ * c)] := fun c =>
    PBL.toStd_append_blkT _ _ _ _ _ _
  have hgN : ∀ cc : ℂ × ℂ, KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε i a (P ++ [(m, cc.1)]) (Q ++ [(m, cc.2)]) =
      (((√(PBL.nnS S (P ++ [(m, cc.1)])) * √(PBL.nnS S (Q ++ [(m, cc.2)])) : ℝ) : ℂ) *
        ((1 / (PBL.bS S (P ++ [(m, 1)]) * PBL.bS S (Q ++ [(m, 1)]) * PBL.ΓS S i) : ℝ) : ℂ) *
        (p v).RR (PBASM.cutSeq S p f χ n v ε) i a (PBL.stdS S P ++ [(m, lP * cc.1)])
          (PBL.stdS S Q ++ [(m, lQ * cc.2)])) /
        ((PBL.setC S p (PBASM.cutSeq S p f χ n)).sizeAt v a : ℂ) := by
    intro cc
    unfold KB.gN
    erw [PBL.gramLoc_setC hB]
    rw [bS_app S P m cc.1, bS_app S Q m cc.2, eP, eQ]
  refine ContinuousOn.congr ?_ (fun cc _ => hgN cc)
  refine ContinuousOn.div_const ?_ _
  refine ContinuousOn.mul (ContinuousOn.mul ?_ continuousOn_const) ?_
  · have e1 : ContinuousOn (fun cc : ℂ × ℂ => PBL.nnS S (P ++ [(m, cc.1)])) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) :=
      (nnS_cont S P m).comp continuousOn_fst (fun cc hcc => hcc.1)
    have e2 : ContinuousOn (fun cc : ℂ × ℂ => PBL.nnS S (Q ++ [(m, cc.2)])) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) :=
      (nnS_cont S Q m).comp continuousOn_snd (fun cc hcc => hcc.2)
    exact Complex.continuous_ofReal.comp_continuousOn
      ((Real.continuous_sqrt.comp_continuousOn e1).mul (Real.continuous_sqrt.comp_continuousOn e2))
  · have hmap : Set.MapsTo (fun cc : ℂ × ℂ => (lP * cc.1, lQ * cc.2)) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))
        (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := fun cc hcc => ⟨mul_ne_zero hlP0 hcc.1, mul_ne_zero hlQ0 hcc.2⟩
    exact hRR.comp (f := fun cc : ℂ × ℂ => (lP * cc.1, lQ * cc.2)) (Continuous.continuousOn (by fun_prop)) hmap

end final

end Formalism.FourierDecayAlt.P.LastBlockContinuity

theorem Formalism.FourierDecayAlt.P.kernel_continuity_built : Formalism.FourierDecayAlt.P.GermFibreKernels.KerContB := Formalism.FourierDecayAlt.P.LastBlockContinuity.level_forms_joint_continuity
end
end
