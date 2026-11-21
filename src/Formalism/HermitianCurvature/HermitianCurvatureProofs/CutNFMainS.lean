import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFDomS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHypS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPairPtw
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFId
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDomCutInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormDone
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENFMain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibMain

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hsVec_ofReal_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℝ) (X : Wq →L[ℂ] Wp) :
    B.hsVec ((c : ℂ) • X) = (c : ℂ) • B.hsVec X := by
  unfold B.hsVec
  rfl

theorem nfBetaLim_thr (R K Nn A : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ K) (hN : 0 ≤ Nn)
    (h : 10 * (R + 1) ^ 4 * (Nn * (2 * R + K + 1) ^ 2 + (2 * R + K + 1) ^ 3) ≤ A) :
    2 * (K + R) * (R + 1) + 1 ≤ A ∧ (2 * R + K + 1) ^ 2 < A / (9 * (R + 1)) := by
  set n := 2 * R + K + 1 with hn
  have hn1 : 1 ≤ n := by rw [hn]; linarith
  have h4 : R + 1 ≤ (R + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hn3 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have a1 : (R + 1) * n ^ 2 ≤ (R + 1) ^ 4 * n ^ 3 := mul_le_mul h4 hn3 (by positivity) (by positivity)
  have a2 : (R + 1) ^ 4 * n ^ 3 ≤ (R + 1) ^ 4 * (Nn * n ^ 2 + n ^ 3) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg n]) (by positivity)
  have key : 10 * ((R + 1) * n ^ 2) ≤ A := by
    have e : 10 * (R + 1) ^ 4 * (Nn * n ^ 2 + n ^ 3) = 10 * ((R + 1) ^ 4 * (Nn * n ^ 2 + n ^ 3)) := by ring
    rw [e] at h
    linarith
  have hpos : 0 < (R + 1) * n ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · have hnn : n ≤ n ^ 2 := by nlinarith
    have b1 : 2 * (K + R) * (R + 1) + 1 ≤ 2 * n * (R + 1) := by rw [hn]; nlinarith
    have b2 : 2 * n * (R + 1) ≤ 2 * ((R + 1) * n ^ 2) := by nlinarith
    linarith
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem truncated_pairing_eq_integral (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε : ℝ)
    (w : List C.Letter) :
    pair0 p F (D.cutF p.T.base χ F ε) w =
      ∫ q, ((χ (Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) / ε) : ℝ) : ℂ) *
        levelZeroRadialIntegral p w F q := by
  unfold pair0 B.beta betaBig
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  show (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))
        (B.hsVec (B.JF p.T.base (w.foldr (fun a H => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) H) F)
          (bigCell P.k P.r q.1 (p.T.base.μsec q.2)))) = _
  rw [Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, hsVec_ofReal_smul, inner_smul_left, Complex.conj_ofReal]
  unfold levelZeroRadialIntegral
  ring

theorem self_pairing_eq_integral (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    pair0 p F F w = ∫ q, levelZeroRadialIntegral p w F q := by
  unfold pair0 B.beta betaBig
  rfl

end place

theorem beta_limit_all_levels_holds : NFBetaLimAll := by
  intro Cb
  refine ⟨10, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  obtain ⟨hχ, -, -, hfA, hth, -⟩ := hH
  obtain ⟨δ, hδ, hχ0⟩ := hχ.2.1
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  set A := A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) with hAdef
  have hCC : ∀ m : ℕ, B.InCC A m F' := inCC_fpm_id p p₀ hfA
  obtain ⟨hAB', hT'⟩ := nfBetaLim_thr (P.r : ℝ) (P.k : ℝ) (N : ℝ) A (by positivity) (by positivity) (by positivity) hth
  have hAB : B.AB P.k P.r ≤ A := by unfold B.AB; exact hAB'
  have hT : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    push_cast
    simpa using hT'
  set Ds := p.T.base with hDs
  have hI : Integrable (levelZeroRadialIntegral p w F') := rr0Int_integrable p w hAB hT fun j _ => hCC j

  obtain ⟨Cχ, hCχ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hχ.1.continuous.continuousOn
  set Mχ := max Cχ 1 with hMdef
  have hM : ∀ x, ‖χ x‖ ≤ Mχ := by
    intro x
    rcases lt_or_ge x 0 with h | h
    · rw [hχ0 x (by linarith), norm_zero]; exact le_max_of_le_right zero_le_one
    rcases le_or_gt x 1 with h' | h'
    · exact (hCχ x ⟨h, h'⟩).trans (le_max_left _ _)
    · rw [hχ.2.2 x h'.le, norm_one]; exact le_max_right _ _

  set K := Formalism.FourierDecayAlt.P.CutMP.En.foldCV P.k P.r (M.sgn P p.l0) w F' with hK
  have hK0 : B.InCC A 0 K :=
    Formalism.FourierDecayAlt.P.CutMP.En.inCC_fold Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class A (M.sgn P p.l0) F' w 0 (hCC _)
  have cH' := jgq_continuousOn Ds hT (hCC 0)
  have cK' := jgq_continuousOn Ds hT hK0
  have hcv := Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff (V := Wp) (W := Wq)
  have ca : ContinuousOn (fun q => B.hsVec (B.JF Ds F' (B.gq Ds q))) (JF.QDom P.k P.r Ds.z Ds.z') :=
    hcv.continuous.comp_continuousOn cH'
  have cb : ContinuousOn (fun q => B.hsVec (B.JF Ds K (B.gq Ds q))) (JF.QDom P.k P.r Ds.z Ds.z') :=
    hcv.continuous.comp_continuousOn cK'
  have hgq : ContinuousOn (fun q => B.gq Ds q) (JF.QDom P.k P.r Ds.z Ds.z') :=
    (Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn Ds 0).continuousOn
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable (fun q =>
      ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) * levelZeroRadialIntegral p w F' q) volume := by
    intro ε
    have cχ : ContinuousOn (fun q => ((χ (Gf P.k P.r Ds.z Ds.z' (B.gq Ds q) / ε) : ℝ) : ℂ))
        (JF.QDom P.k P.r Ds.z Ds.z') :=
      Complex.continuous_ofReal.comp_continuousOn (hχ.1.continuous.comp_continuousOn
        (((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Ds.z Ds.z').continuous.comp_continuousOn hgq).div_const ε))
    have := aesm_weight_smul Ds (cχ.mul (ca.inner cb))
    refine this.congr (Eventually.of_forall fun q => ?_)
    show (bcWeight P.k P.r (Tz P.k P.r Ds.z) (Tz P.k P.r Ds.z') q : ℝ) • (((χ (Gf P.k P.r Ds.z Ds.z' (B.gq Ds q) / ε) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (B.JF Ds F' (B.gq Ds q))) (B.hsVec (B.JF Ds K (B.gq Ds q)))) = _
    rw [Complex.real_smul]
    show _ = ((χ (Gf P.k P.r Ds.z Ds.z' (B.gq Ds q) / ε) : ℝ) : ℂ) *
      ((bcWeight P.k P.r (Tz P.k P.r Ds.z) (Tz P.k P.r Ds.z') q : ℂ) *
        inner ℂ (B.hsVec (B.JF Ds F' (B.gq Ds q))) (B.hsVec (B.JF Ds K (B.gq Ds q))))
    ring

  have hlim : ∀ᵐ q : (Fin P.r → ℂ) × ℂ, Tendsto (fun ε : ℝ =>
      ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) * levelZeroRadialIntegral p w F' q) (𝓝[>] 0)
      (𝓝 (levelZeroRadialIntegral p w F' q)) := by
    refine Eventually.of_forall fun q => ?_
    by_cases hq : bcWeight P.k P.r (Tz P.k P.r Ds.z) (Tz P.k P.r Ds.z') q = 0
    · have h0 : levelZeroRadialIntegral p w F' q = 0 := by unfold levelZeroRadialIntegral; rw [hq]; simp
      simp only [h0, mul_zero]
      exact tendsto_const_nhds
    obtain ⟨-, hG⟩ := bigCell_pos p q hq
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
    have h1 : 1 ≤ Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε := by
      rw [le_div_iff₀ hε.1]; linarith [hε.2]
    rw [hχ.2.2 _ h1]
    simp
  have hT2 : Tendsto (fun ε : ℝ => ∫ q, ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) *
      levelZeroRadialIntegral p w F' q) (𝓝[>] 0) (𝓝 (∫ q, levelZeroRadialIntegral p w F' q)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun q => Mχ * ‖levelZeroRadialIntegral p w F' q‖)
      (Eventually.of_forall hmeas) (Eventually.of_forall fun ε => Eventually.of_forall fun q => ?_)
      (hI.norm.const_mul Mχ) hlim
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have e1 : (fun ε : ℝ => (pair0 p F' (D.cutF p.T.base χ F' ε) w).re) =
      fun ε => (∫ q, ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) *
        levelZeroRadialIntegral p w F' q).re := funext fun ε => by rw [truncated_pairing_eq_integral]
  rw [e1, self_pairing_eq_integral]
  exact (Complex.continuous_re.tendsto _).comp hT2

end

end Formalism.FourierDecayAlt.P.CutBP
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nfHypS_mono {Cb c c' : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A₀ : ℝ} {p₀ : ℕ} {χ χ' : ℝ → ℝ} {N : ℕ}
    (h : NFHypS Cb c p f A₀ p₀ χ N) (hc : c' ≤ c) (hχ' : C6.IsCut0 χ') : NFHypS Cb c' p f A₀ p₀ χ' N :=
  ⟨nfHyp_mono h.1 hc hχ', h.2.1, h.2.2⟩

def NFPolQuadAllS : Prop :=
  P5.ThmPActual → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHypS Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
      Integrable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w) ∧
      (pair0 p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
        (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re =
        ∫ c, topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c

def NFPolFormAllS : Prop :=
  P5.ThmPActual → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHypS Cb Cc p f A₀ p₀ χ N → ∀ χ' : ℝ → ℝ, C6.IsCut0 χ' → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∀ ε : ℝ, 0 < ε →
        Integrable (topPD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w) ∧
        (pair0 p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
          (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w).re =
          ∫ c, topPD p (D.cutF p.T.base χ' (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε)
            (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c

theorem nFTopFormAllS_of (hMeas : TopDMeasCpt) (hApx : NFApxDomAllS) : NFTopFormAllS := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  obtain ⟨C2, H2⟩ := hApx Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  have hH1 := nfHyp_monoC hH.1 (le_max_left C1 C2)
  have hH2 := nfHypS_monoC hH (le_max_right C1 C2)
  obtain ⟨hχ, hCb, hf, hfA, hthr, -⟩ := hH1
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have hF'ck : B.CkOn ⊤ (B.GV P.k P.r) F' := by
    rw [hF', fpm_id]
    exact ckOn_Gpow_smul _ _ p₀ hf
  obtain ⟨hcpt, hlim⟩ := H1 Wp Wq P p F' χ ε (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N (cutN P.k P.r) hCb hχ hε
    hF'ck (inCC_fpm_id p p₀ hfA) hthr (fun _ _ => rfl)
  set H := D.cutF p.T.base χ F' ε with hHdef
  have hcpt' : ∀ n, KB.CptCoef p.T.base (apx H n) := hcpt
  have hform : ∀ n, (p.RR (apx H n) 0 w [] []).re = ∫ c, topD p (apx H n) w c := fun n =>
    normal_form_compact_support_holds hA Wp Wq P p (apx H n) Y w Cb hCb (hcpt' n) hw
      (hMeas Wp Wq P p (apx H n) w Cb hCb (hcpt' n) hw.1)
  have hlim0 : Tendsto (fun n => ∫ c, topD p (apx H n) w c) atTop (𝓝 (p.RR H 0 w [] []).re) := by
    have := (Complex.continuous_re.tendsto _).comp (hlim 0 w hw.1 hN [] [])
    refine this.congr fun n => ?_
    exact hform n
  have hptw : ∀ c, Tendsto (fun n => topD p (apx H n) w c) atTop (𝓝 (topD p H w c)) := by
    intro c
    unfold topD TBB.Ew TBB.NP
    exact (Complex.continuous_re.tendsto _).comp
      (tendsto_const_nhds.mul (hlim (P.r + 1) w hw.1 hN (TBB.bigPt P.r c) (TBB.bigPt P.r c)))
  obtain ⟨h, hint, hb⟩ := H2 Wp Wq P p f A₀ p₀ χ Y N hH2 w hw hN ε hε
  have hdct : Tendsto (fun n => ∫ c, topD p (apx H n) w c) atTop (𝓝 (∫ c, topD p H w c)) :=
    tendsto_integral_of_dominated_convergence h
      (fun n => hMeas Wp Wq P p (apx H n) w Cb hCb (hcpt' n) hw.1) hint hb
      (Filter.Eventually.of_forall hptw)
  exact tendsto_nhds_unique hlim0 hdct

theorem nFTopIntS_of (hMeas : TopDMeasCpt) (hApx : NFApxDomAllS) (Cb : ℝ) : ∃ Cc : ℝ,
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
      NFHypS Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
        Integrable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w) := by
  obtain ⟨C1, H1⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  obtain ⟨C2, H2⟩ := hApx Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  have hH1 := nfHyp_monoC hH.1 (le_max_left C1 C2)
  have hH2 := nfHypS_monoC hH (le_max_right C1 C2)
  obtain ⟨hχ, hCb, hf, hfA, hthr, -⟩ := hH1
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have hF'ck : B.CkOn ⊤ (B.GV P.k P.r) F' := by
    rw [hF', fpm_id]
    exact ckOn_Gpow_smul _ _ p₀ hf
  obtain ⟨hcpt, hlim⟩ := H1 Wp Wq P p F' χ ε (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N (cutN P.k P.r) hCb hχ hε
    hF'ck (inCC_fpm_id p p₀ hfA) hthr (fun _ _ => rfl)
  set H := D.cutF p.T.base χ F' ε with hHdef
  have hcpt' : ∀ n, KB.CptCoef p.T.base (apx H n) := hcpt
  have hptw : ∀ c, Tendsto (fun n => topD p (apx H n) w c) atTop (𝓝 (topD p H w c)) := by
    intro c
    unfold topD TBB.Ew TBB.NP
    exact (Complex.continuous_re.tendsto _).comp
      (tendsto_const_nhds.mul (hlim (P.r + 1) w hw.1 hN (TBB.bigPt P.r c) (TBB.bigPt P.r c)))
  obtain ⟨h, hint, hb⟩ := H2 Wp Wq P p f A₀ p₀ χ Y N hH2 w hw hN ε hε
  have hm : AEStronglyMeasurable (topD p H w) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => hMeas Wp Wq P p (apx H n) w Cb hCb (hcpt' n) hw.1) (Filter.Eventually.of_forall hptw)
  refine hint.mono' hm ?_
  have hb' : ∀ᵐ c, ∀ n, ‖topD p (apx H n) w c‖ ≤ h c := ae_all_iff.2 hb
  filter_upwards [hb'] with c hc
  exact le_of_tendsto' ((continuous_norm.tendsto _).comp (hptw c)) hc

theorem nfPolQuadAllS_of (hMeas : TopDMeasCpt) (hApx : NFApxDomAllS) : NFPolQuadAllS := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := nFTopFormAllS_of hMeas hApx hA Cb
  obtain ⟨C2, H2⟩ := nFTopIntS_of hMeas hApx Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  have hH1 := nfHypS_mono hH (le_max_left C1 C2) hH.1.1
  have hH2 := nfHypS_mono hH (le_max_right C1 C2) hH.1.1
  refine ⟨H2 Wp Wq P p f A₀ p₀ χ Y N hH2 w hw hN ε hε, ?_⟩
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hF := ckOn_fpm p p₀ hH.1.2.2.1 hid
  have hc := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hH.1.1 hF ε
  rw [← residual_pairing_eq_self_pairing p hc hw.1]
  exact H1 Wp Wq P p f A₀ p₀ χ Y N hH1 w hw hN ε hε

theorem nfPolFormAllS_of (s1 : NFPolQuadAllS) (s2 : NFPairMidAll) (s3 : NFTopMidAll) : NFPolFormAllS := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := s1 hA Cb
  obtain ⟨C2, H2⟩ := s2 Cb
  obtain ⟨C3, H3⟩ := s3 Cb
  refine ⟨max C1 (max C2 C3), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH χ' hχ' w hw hN ε hε
  have m1 : C1 ≤ max C1 (max C2 C3) := le_max_left _ _
  have m2 : C2 ≤ max C1 (max C2 C3) := le_max_of_le_right (le_max_left _ _)
  have m3 : C3 ≤ max C1 (max C2 C3) := le_max_of_le_right (le_max_right _ _)
  have hχ : C6.IsCut0 χ := hH.1.1
  have hm := isCut0_midCut hχ' hχ
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  obtain ⟨iu, qu⟩ := H1 Wp Wq P p f A₀ p₀ χ' Y N (nfHypS_mono hH m1 hχ') w hw hN ε hε
  obtain ⟨iv, qv⟩ := H1 Wp Wq P p f A₀ p₀ χ Y N (nfHypS_mono hH m1 hχ) w hw hN ε hε
  obtain ⟨im, qm⟩ := H1 Wp Wq P p f A₀ p₀ (midCut χ' χ) Y N (nfHypS_mono hH m1 hm) w hw hN ε hε
  have hpair := H2 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH.1 m2 hχ) χ' hχ' w hw hN ε hε
  have htop := H3 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH.1 m3 hχ) χ' hχ' w hw hN ε hε
  have e : topPD p (D.cutF p.T.base χ' F' ε) (D.cutF p.T.base χ F' ε) w = fun c =>
      2 * topD p (D.cutF p.T.base (midCut χ' χ) F' ε) w c - topD p (D.cutF p.T.base χ' F' ε) w c / 2 -
        topD p (D.cutF p.T.base χ F' ε) w c / 2 := by
    funext c
    have := htop c
    linarith
  have hi1 : Integrable (fun c => 2 * topD p (D.cutF p.T.base (midCut χ' χ) F' ε) w c) := im.const_mul 2
  have hi2 : Integrable (fun c => topD p (D.cutF p.T.base χ' F' ε) w c / 2) := iu.div_const 2
  have hi3 : Integrable (fun c => topD p (D.cutF p.T.base χ F' ε) w c / 2) := iv.div_const 2
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (hi1.sub hi2).sub hi3
  · have hi12 : Integrable (fun c => 2 * topD p (D.cutF p.T.base (midCut χ' χ) F' ε) w c -
        topD p (D.cutF p.T.base χ' F' ε) w c / 2) := hi1.sub hi2
    rw [e, integral_sub hi12 hi3, integral_sub hi1 hi2, integral_const_mul, integral_div, integral_div,
      ← qu, ← qv, ← qm, hpair]
    ring

theorem nfTopIdAllS_of (hA : P5.ThmPActual) (h3 : NFTopDomAllS) (s1 : NFPolFormAllS) (s2 : NFPairPtwAll)
    (s4 : NFBetaLimAll) : NFTopIdAllS := by
  intro Cb
  obtain ⟨C1, H1⟩ := s1 hA Cb
  obtain ⟨C2, H2⟩ := s2 Cb
  obtain ⟨C3, H3⟩ := h3 Cb
  obtain ⟨C4, H4⟩ := s4 Cb
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  have hχ : C6.IsCut0 χ := hH.1.1
  obtain ⟨δ, hδ, hχ0⟩ := hχ.2.1
  set κ : ℝ := min δ 1 / 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    have : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  have hκδ : κ < δ := by
    have : min δ 1 ≤ δ := min_le_left _ _
    linarith
  set χκ : ℝ → ℝ := fun x => χ (x / κ) with hχκdef
  have hχκ : C6.IsCut0 χκ := by
    refine ⟨hχ.1.comp (contDiff_id.div_const κ), ⟨κ * δ, mul_pos hκ hδ, fun x hx => hχ0 _ ?_⟩, fun x hx => hχ.2.2 _ ?_⟩
    · rw [div_lt_iff₀ hκ]
      linarith
    · rw [le_div_iff₀ hκ]
      linarith
  have hχκ1 : ∀ x, κ ≤ x → χκ x = 1 := fun x hx => hχ.2.2 _ ((le_div_iff₀ hκ).2 (by linarith))
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hF := ckOn_fpm p p₀ hH.1.2.2.1 hid
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have m1 : C1 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_left (le_max_left _ _)
  have m2 : C2 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_left (le_max_right _ _)
  have m3 : C3 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_right (le_max_left _ _)
  have m4 : C4 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_right (le_max_right _ _)

  have hβ : Tendsto (fun ε : ℝ => (pair0 p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w).re) (𝓝[>] 0)
      (𝓝 (pair0 p F' F' w).re) := by
    refine (H4 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH.1 m4 hχ) w hw hN).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [pairing_truncation_locality p hF hχκ hκδ hχ0 hχκ1 w hε]

  obtain ⟨-, hA, hAi, hAb⟩ := H3 Wp Wq P p f A₀ p₀ χκ Y N (nfHypS_mono hH m3 hχκ) w hw hN
  obtain ⟨-, hB, hBi, hBb⟩ := H3 Wp Wq P p f A₀ p₀ χ Y N (nfHypS_mono hH m3 hχ) w hw hN
  have hT : Tendsto (fun ε : ℝ => ∫ c, topPD p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w c) (𝓝[>] 0)
      (𝓝 (∫ c, topD p F' w c)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun c => (hA c + hB c) / 2) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (H1 Wp Wq P p f A₀ p₀ χ Y N (nfHypS_mono hH m1 hχ) χκ hχκ w hw hN ε hε).1.aestronglyMeasurable
    · filter_upwards [hAb, hBb] with ε ha hb
      filter_upwards [ha, hb] with c hac hbc
      rw [Real.norm_eq_abs]
      refine (topPD_cs p _ _ w c).trans ?_
      have e1 := (le_abs_self (topD p (D.cutF p.T.base χκ F' ε) w c)).trans (le_of_eq (Real.norm_eq_abs _).symm)
      have e2 := (le_abs_self (topD p (D.cutF p.T.base χ F' ε) w c)).trans (le_of_eq (Real.norm_eq_abs _).symm)
      linarith
    · exact (hAi.add hBi).div_const 2
    · filter_upwards [H2 Wp Wq P p f A₀ p₀ χ Y N (nfHyp_mono hH.1 m2 hχ) χκ hχκ w hw hN] with c hc
      exact tendsto_const_nhds.congr' (hc.mono fun ε h => h.symm)
  have hE : (fun ε : ℝ => (pair0 p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w).re) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε => ∫ c, topPD p (D.cutF p.T.base χκ F' ε) (D.cutF p.T.base χ F' ε) w c := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (H1 Wp Wq P p f A₀ p₀ χ Y N (nfHypS_mono hH m1 hχ) χκ hχκ w hw hN ε hε).2
  have huniq := tendsto_nhds_unique (hβ.congr' hE) hT
  show ∫ c, topD p F' w c = (p.RR F' 0 w [] []).re
  rw [← huniq, residual_pairing_eq_self_pairing p hF hw.1]

end

end Formalism.FourierDecayAlt.P.CutBP
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem limEvT_fpm_of_NFS (hA : P5.ThmPActual) (h1 : NFTopFormAllS) (h2 : NFTopPtwAll) (h3 : NFTopDomAllS)
    (h4 : NFTopIdAllS) (Cb : ℝ) :
    ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
      NFHypS Cb Cc p f A₀ p₀ χ N →
      LimEvT p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  obtain ⟨C1, H1⟩ := h1 hA Cb
  obtain ⟨C2, H2⟩ := h2 Cb
  obtain ⟨C3, H3⟩ := h3 Cb
  obtain ⟨C4, H4⟩ := h4 Cb
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH
  have mono : ∀ c, c ≤ max (max C1 C2) (max C3 C4) → NFHypS Cb c p f A₀ p₀ χ N := fun c hc => by
    refine ⟨?_, hH.2.1, hH.2.2⟩
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH.1
    refine ⟨a1, a2, a3, a4, le_trans ?_ a5, a6⟩
    have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
      positivity
    have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
        x * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
      fun x => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hc hX
  exact limEvT_of_NF p χ _ Y N
    (fun w hw hN => H1 Wp Wq P p f A₀ p₀ χ Y N (mono C1 (le_max_of_le_left (le_max_left _ _))) w hw hN)
    (fun w hw hN => H2 Wp Wq P p f A₀ p₀ χ Y N (mono C2 (le_max_of_le_left (le_max_right _ _))).1 w hw hN)
    (fun w hw hN => H3 Wp Wq P p f A₀ p₀ χ Y N (mono C3 (le_max_of_le_right (le_max_left _ _))) w hw hN)
    (fun w hw hN => H4 Wp Wq P p f A₀ p₀ χ Y N (mono C4 (le_max_of_le_right (le_max_right _ _))) w hw hN)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem thmBpAt_main5 (hA : P5.ThmPActual) (h1 : NFTopFormAllS) (h2 : NFTopPtwAll) (h3 : NFTopDomAllS)
    (h4 : NFTopIdAllS) (hJC : NFJCutFF) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      B.JF p.T.base f ∈ FFKB p →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ := thmBpAt_main2 hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := limEvT_fpm_of_NFS hA h1 h2 h3 h4 Cb
  refine ⟨C₄, c₃, Cc, Cc', Cn, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hJf hth1 hth2 hth3
    hth4 hN2 hexp hWG hLG hI5 hBd
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3 hexp hWG hLG
    hI5 (hn Wp Wq P p f A₀ p₀ χ Y N ⟨⟨hχ, hCb, hf, hfA, hth4, hN2⟩, hJf, hJC Wp Wq P p f hf⟩) hBd

end

end Formalism.FourierDecayAlt.P.CutBP
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def flCutS (k r : ℕ) (n : ℕ) (g : B.Mat k r) : ℂ :=
  ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)

theorem domination_measurability_holds : NFDomMeas := by
  intro Cb
  obtain ⟨Cc, hFL⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  obtain ⟨hχ, hInD, hfck, hfcc, hA, -⟩ := hH
  have hck : B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) := by
    rw [fpm_id]; exact ckOn_Gpow_smul _ _ p₀ hfck
  obtain ⟨hcpt, hlim⟩ := hFL Wp Wq P p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) χ ε
    (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N (flCutS P.k P.r) hInD hχ hε hck (inCC_fpm_id p p₀ hfcc) hA
    (fun n g => rfl)
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n => topD p (fun g => flCutS P.k P.r n g •
      D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε g) w)
    (fun n => top_domination_measurable_compact Wp Wq P p _ w Cb hInD (hcpt n) hw.1) (ae_of_all _ fun c => ?_)
  have h := hlim (P.r + 1) w hw.1 hN (TBB.bigPt P.r c) (TBB.bigPt P.r c)
  unfold topD TBB.Ew TBB.NP
  exact (Complex.continuous_re.tendsto _).comp (h.const_mul _)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_main6 (hA : P5.ThmPActual) (hT : NFTieHatS) (hH : NFHatProdKBS) (hJC : NFJCutFF) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      B.JF p.T.base f ∈ FFKB p →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by

  have hTM : TopDMeasCpt := Formalism.FourierDecayAlt.P.CutBP.top_domination_measurable_compact

  have hCore : NFCoreNS := Formalism.FourierDecayAlt.P.CutBP.nFCoreNS_of_cut Formalism.FourierDecayAlt.P.CutBP.leibniz_vector_estimate_holds hT hH Formalism.FourierDecayAlt.P.CutBP.trace_norm_bound_constant_one Formalism.FourierDecayAlt.P.CutBP.operator_multiplication_admissible
  have hDP : NFDomPtwS := Formalism.FourierDecayAlt.P.CutBP.nfDomPtwS_of_cut Formalism.FourierDecayAlt.P.CutBP.unfolding_top_term_holds Formalism.FourierDecayAlt.P.CutBP.vector_multiplication_holds Formalism.FourierDecayAlt.P.CutBP.truncated_supremum_bound_holds
    Formalism.FourierDecayAlt.P.CutBP.leibniz_vector_estimate_holds hCore Formalism.FourierDecayAlt.P.CutBP.empty_operator_list_holds
  have hApx : NFApxDomAllS := Formalism.FourierDecayAlt.P.CutBP.nfApxDomAllS_of_cut Formalism.FourierDecayAlt.P.CutBP.domination_at_zero_holds hDP Formalism.FourierDecayAlt.P.CutBP.dominated_L2_truncation_bound_holds
  have hForm : NFTopFormAllS := Formalism.FourierDecayAlt.P.CutBP.nFTopFormAllS_of hTM hApx
  have hDom : NFTopDomAllS := Formalism.FourierDecayAlt.P.CutBP.nfTopDomAllS_of_cut Formalism.FourierDecayAlt.P.CutBP.domination_at_zero_holds hDP Formalism.FourierDecayAlt.P.CutBP.dominated_L2_operator_bound_holds domination_measurability_holds

  have hPQ : NFPolQuadAllS := Formalism.FourierDecayAlt.P.CutBP.nfPolQuadAllS_of hTM hApx
  have hPF : NFPolFormAllS := Formalism.FourierDecayAlt.P.CutBP.nfPolFormAllS_of hPQ Formalism.FourierDecayAlt.P.CutBP.pairing_middle_all_levels_holds Formalism.FourierDecayAlt.P.CutBP.top_middle_all_levels_holds
  have hId : NFTopIdAllS := Formalism.FourierDecayAlt.P.CutBP.nfTopIdAllS_of hA hDom hPF Formalism.FourierDecayAlt.P.CutBP.pairing_pointwise_all_levels_holds Formalism.FourierDecayAlt.P.CutBP.beta_limit_all_levels_holds
  exact Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main5 hA hForm Formalism.FourierDecayAlt.P.CutBP.top_pointwise_all_levels_holds hDom hId hJC Cb C₃ CΛ C₀ hC₃ hCΛ hC₀

end

end Formalism.FourierDecayAlt.P.CutBP
end
