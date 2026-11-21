import Formalism.HermitianCurvature.StatementKB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists

section
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBB.K8

noncomputable section

def dw (c : ℂ) : ℝ := ((1 + ‖c‖) ^ 3)⁻¹

theorem dw_cont : Continuous dw :=
  ((continuous_const.add continuous_norm).pow 3).inv₀ fun c => pow_ne_zero _ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg c)).ne'


theorem dw_integrable : Integrable dw := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  show (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast

theorem bound_all {f : ℂ → ℂ} (hf : Continuous f) {C : ℝ} (h : ∀ c, c ≠ 0 → ‖f c‖ ≤ C * dw c) (c : ℂ) :
    ‖f c‖ ≤ C * dw c := by
  have hs : IsClosed {c : ℂ | ‖f c‖ ≤ C * dw c} :=
    isClosed_le (continuous_norm.comp hf) (continuous_const.mul dw_cont)
  have hsub : ({0}ᶜ : Set ℂ) ⊆ {c | ‖f c‖ ≤ C * dw c} := fun c hc => h c hc
  have := hs.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at this
  exact this (Set.mem_univ c)

theorem fourier_cont {f : ℂ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

theorem ae_ne_zero : ∀ᵐ c : ℂ ∂volume, c ≠ 0 := by
  simp [ae_iff]

theorem limit_fourier (g : ℕ → ℂ → ℂ) (g0 : ℂ → ℂ) (φ : ℕ → ℂ → ℂ) (C C' : ℝ)
    (hφc : ∀ n, Continuous (φ n)) (hφg : ∀ n c, c ≠ 0 → φ n c = g n c)
    (hconv : ∀ c, Tendsto (fun n => g n c) atTop (𝓝 (g0 c)))
    (hb : ∀ n c, c ≠ 0 → ‖g n c‖ ≤ C * dw c)
    (hT : ∀ n w, ‖𝓕 (φ n) w‖ ≤ C' * dw w) :
    ∃ ψ : ℂ → ℂ, Continuous ψ ∧ (∀ c, c ≠ 0 → ψ c = g0 c) ∧ (∀ c, ‖ψ c‖ ≤ C * dw c) ∧
      Tendsto (fun n => ∫ c, φ n c) atTop (𝓝 (∫ c, ψ c)) := by
  have hφb : ∀ n c, ‖φ n c‖ ≤ C * dw c := fun n =>
    bound_all (hφc n) fun c hc => by rw [hφg n c hc]; exact hb n c hc
  have hBi : Integrable (fun c => C * dw c) := dw_integrable.const_mul C
  have hB'i : Integrable (fun c => C' * dw c) := dw_integrable.const_mul C'
  have hφi : ∀ n, Integrable (φ n) := fun n =>
    hBi.mono' (hφc n).aestronglyMeasurable (Eventually.of_forall (hφb n))
  have hFt : ∀ w, Tendsto (fun n => 𝓕 (φ n) w) atTop (𝓝 (𝓕 g0 w)) := by
    intro w
    show Tendsto (fun n => ∫ v, 𝐞 (-⟪v, w⟫) • φ n v) atTop (𝓝 (∫ v, 𝐞 (-⟪v, w⟫) • g0 v))
    refine tendsto_integral_of_dominated_convergence (fun c => C * dw c) (fun n => ?_) hBi (fun n => ?_) ?_
    · exact ((Real.fourierIntegral_convergent_iff w).mpr (hφi n)).aestronglyMeasurable
    · exact Eventually.of_forall fun c => by rw [Circle.norm_smul]; exact hφb n c
    · filter_upwards [ae_ne_zero] with c hc
      simp only [hφg _ c hc]
      exact (hconv c).const_smul _
  have hGm : AEStronglyMeasurable (𝓕 g0) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (fourier_cont (hφi n)).aestronglyMeasurable)
      (ae_of_all _ hFt)
  have hGb : ∀ w, ‖𝓕 g0 w‖ ≤ C' * dw w := fun w => le_of_tendsto' (hFt w).norm fun n => hT n w
  have hGi : Integrable (𝓕 g0) := hB'i.mono' hGm (Eventually.of_forall hGb)
  have hinv : ∀ n, 𝓕⁻ (𝓕 (φ n)) = φ n := fun n =>
    (hφc n).fourierInv_fourier_eq (hφi n)
      (hB'i.mono' (fourier_cont (hφi n)).aestronglyMeasurable (Eventually.of_forall (hT n)))
  set ψ : ℂ → ℂ := 𝓕⁻ (𝓕 g0) with hψ
  have hψlim : ∀ c, Tendsto (fun n => φ n c) atTop (𝓝 (ψ c)) := by
    intro c
    have : (fun n => φ n c) = fun n => 𝓕⁻ (𝓕 (φ n)) c := funext fun n => by rw [hinv n]
    rw [this, hψ]
    simp only [Real.fourierInv_eq]
    refine tendsto_integral_of_dominated_convergence (fun w => C' * dw w) (fun n => ?_) hB'i (fun n => ?_) ?_
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        (fourier_cont (hφi n))).aestronglyMeasurable
    · exact Eventually.of_forall fun w => by rw [Circle.norm_smul]; exact hT n w
    · exact ae_of_all _ fun w => (hFt w).const_smul _
  refine ⟨ψ, ?_, fun c hc => ?_, fun c => le_of_tendsto' (hψlim c).norm fun n => hφb n c, ?_⟩
  · have : ψ = fun c => 𝓕 (𝓕 g0) (-c) := funext fun c => Real.fourierInv_eq_fourier_neg _ c
    rw [this]
    exact (fourier_cont hGi).comp continuous_neg
  · refine tendsto_nhds_unique (hψlim c) ?_
    have : (fun n => φ n c) = fun n => g n c := funext fun n => hφg n c hc
    rw [this]
    exact hconv c
  · exact tendsto_integral_of_dominated_convergence (fun c => C * dw c)
      (fun n => (hφc n).aestronglyMeasurable) hBi (fun n => ae_of_all _ (hφb n)) (ae_of_all _ hψlim)

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def Lm (g : ℕ) (l : ℂ) : ℂ := -(((2 / (g : ℝ) : ℝ)) : ℂ) * conj l

theorem psiL_eq (S : C.HidaSetting E Wp Wq) (l c z : ℂ) :
    z * KB.psiL S l c = 𝐞 (-⟪c, Lm S.g l⟫) • z := by
  rw [Circle.smul_def, Real.fourierChar_apply, KB.psiL, mul_comm z]
  congr 2
  have hi : ⟪c, Lm S.g l⟫ = -(2 / (S.g : ℝ)) * (l * c).re := by
    simp [Lm, Complex.inner, Complex.mul_re]
    ring
  rw [hi]
  push_cast
  ring

theorem Lm_inv (g : ℕ) (hg : (g : ℝ) ≠ 0) (w : ℂ) : Lm g ((((-(g : ℝ) / 2 : ℝ)) : ℂ) * conj w) = w := by
  simp only [Lm, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  rw [← mul_assoc, ← Complex.ofReal_neg, ← Complex.ofReal_mul]
  have : (-(2 / (g : ℝ)) * (-(g : ℝ) / 2)) = 1 := by field_simp
  rw [this]
  simp

theorem decay_scale (g : ℝ) (hg : 1 ≤ g) (w : ℂ) :
    ((1 + ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖) ^ 3)⁻¹ ≤ 8 * dw w := by
  have hn : ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖ = g / 2 * ‖w‖ := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (by linarith : (0:ℝ) < g)]
    norm_num
  rw [hn]
  have h0 : 0 < (1 + ‖w‖) / 2 := by positivity
  have h1 : (1 + ‖w‖) / 2 ≤ 1 + g / 2 * ‖w‖ := by nlinarith [norm_nonneg w]
  calc ((1 + g / 2 * ‖w‖) ^ 3)⁻¹ ≤ (((1 + ‖w‖) / 2) ^ 3)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le h1 3)
    _ = 8 * dw w := by unfold dw; field_simp; ring

theorem g_ge_one (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : (1 : ℝ) ≤ S.g := by
  have : 1 ≤ S.g := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hg1.ne' hg2.ne')
  exact_mod_cast this

theorem gramLoc_tendsto (S : C.HidaSetting E Wp Wq)
    (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    (v : Fin S.f) {ε : ℝ} (hε : 0 < ε) (i : ℕ) (w : S.W) (p q : C.LPt) :
    Tendsto (fun n => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) p q) atTop
      (𝓝 (S.gramLoc v ε i (w.1 v) p q)) :=
  (hconv v ε hε i _ ⟨w, rfl⟩ p q).const_mul _

theorem intAll_limit (S : C.HidaSetting E Wp Wq)
    (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2)
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    (hInt : ∀ n, KB.IntAll (KB.withRR S (RR n)))
    (hB : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 →
      D.ptSize h' = i - 1 →
      ∃ C : ℝ, ∀ n, (∀ c : ℂ, c ≠ 0 →
          ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
        ∀ l : ℂ, ‖∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S l c‖ ≤
          C * ((1 + ‖l‖) ^ 3)⁻¹) :
    KB.IntAll S := by
  intro v ε hε i hi1 hi2 w h h' hh hh'
  obtain ⟨C, hC⟩ := hB v ε hε i hi1 hi2 (w.1 v) ⟨w, rfl⟩ h h' hh hh'
  have hC0 : 0 ≤ C := by
    have := ((hC 0).2 0).trans' (norm_nonneg _)
    simpa using this
  have H := fun n => hInt n v ε hε i hi1 hi2 w h h' hh hh'
  choose φ hφc hφe hφb hφi using H
  have hg := g_ge_one S hg1 hg2
  have hT : ∀ n w', ‖𝓕 (φ n) w'‖ ≤ 8 * C * dw w' := by
    intro n w'
    set l : ℂ := (((-(S.g : ℝ) / 2 : ℝ)) : ℂ) * conj w' with hl
    have hLm : Lm S.g l = w' := Lm_inv S.g (by linarith) w'
    have he : 𝓕 (φ n) w' = ∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) *
        KB.psiL S l c := by
      rw [Real.fourier_eq]
      refine integral_congr_ae ?_
      filter_upwards [ae_ne_zero] with c hc
      rw [psiL_eq, hLm, hφe n c hc]
    rw [he]
    have h8 := mul_le_mul_of_nonneg_left (decay_scale S.g hg w') hC0
    calc _ ≤ C * ((1 + ‖l‖) ^ 3)⁻¹ := (hC n).2 l
      _ ≤ C * (8 * dw w') := h8
      _ = 8 * C * dw w' := by ring
  obtain ⟨ψ, hψc, hψe, hψb, hψi⟩ := limit_fourier
    (fun n c => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]))
    (fun c => S.gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) φ C (8 * C) hφc hφe
    (fun c => gramLoc_tendsto S RR hconv v hε i w _ _) (fun n c hc => (hC n).1 c hc) hT
  refine ⟨ψ, hψc, hψe, ⟨C, hψb⟩, ?_⟩
  have h1 : Tendsto (fun n => ∫ c, φ n c) atTop
      (𝓝 (((KB.dlB S i 1 : ℝ) : ℂ) * S.gramLoc v ε (i - 1) (w.1 v) h h')) := by
    have : (fun n => ∫ c, φ n c) =
        fun n => ((KB.dlB S i 1 : ℝ) : ℂ) * (KB.withRR S (RR n)).gramLoc v ε (i - 1) (w.1 v) h h' :=
      funext fun n => hφi n
    rw [this]
    exact (gramLoc_tendsto S RR hconv v hε (i - 1) w h h').const_mul _
  exact tendsto_nhds_unique hψi h1

end setting

end

end Formalism.FourierDecayAlt.P.PBB.K8
end

section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBB

open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate

noncomputable section
open Classical

theorem integrable_decay3 : Integrable (fun c : ℂ => ((1 + ‖c‖) ^ 3)⁻¹) := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  simp only
  rw [Real.rpow_neg (by positivity)]
  norm_cast

section limB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem ae_coords_ne (S : C.HidaSetting E Wp Wq) : ∀ᵐ c : J.CV E, ∀ v, c (S.pl v) ≠ 0 := by
  have hnull : volume (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S ⁻¹' (⋃ v, {y : Fin S.f → ℂ | y v = 0})) = 0 := by
    rw [(Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S).measure_preimage (MeasurableSet.iUnion fun v =>
      measurableSet_eq_fun (measurable_pi_apply v) measurable_const).nullMeasurableSet]
    exact measure_iUnion_null fun v => Measure.pi_hyperplane _ v 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with c hc
  intro v hv
  exact hc (Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨v, by simp [Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply, hv]⟩))

theorem continuous_coord (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Continuous fun c : J.CV E => c (S.pl v) :=
  (EuclideanSpace.proj (𝕜 := ℂ) (S.pl v)).continuous

theorem continuous_psiInf (S : C.HidaSetting E Wp Wq) (l : E) : Continuous fun c : J.CV E => S.psiInf l c := by
  have : (fun c : J.CV E => S.psiInf l c) = fun c => ∏ v, KB.psiL S (S.σ v l) (c (S.pl v)) :=
    funext fun c => psiInf_eq_prod S l c
  rw [this]
  exact continuous_finsetProd _ fun v _ => (continuous_psiL S _).comp (continuous_coord S v)

theorem norm_psiInf (S : C.HidaSetting E Wp Wq) (l : E) (c : J.CV E) : ‖S.psiInf l c‖ = 1 := by
  rw [psiInf_eq_prod, norm_prod]
  simp [norm_psiL]

theorem aestronglyMeasurable_level_norm (S : C.HidaSetting E Wp Wq) (hInt : KB.IntAll S) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (hi1 : 1 ≤ i)
    (hi2 : i ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E)) (hY : ∀ h ∈ Y, TB.level h = i - 1)
    (κ : TB.Pt E → TB.Pt E → ℂ) : AEStronglyMeasurable (S.N1 ε i w.1 Y κ) volume := by
  have H : ∀ (v : Fin S.f) (h h' : Y), ∃ φ : ℂ → ℂ, Continuous φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = S.gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c)])
        (C.loc (S.σ v) h' ++ [(1, c)])) := by
    intro v h h'
    obtain ⟨φ, hc, he, -, -⟩ := hInt v ε hε i hi1 hi2 w (C.loc (S.σ v) h) (C.loc (S.σ v) h')
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h h.2)
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h' h'.2)
    exact ⟨φ, hc, he⟩
  choose φ hφc hφe using H
  set Φ : J.CV E → ℂ := fun c =>
    (∑ h : Y, ∑ h' : Y, κ h h' * ∏ v, φ v h h' (c (S.pl v))) / (C.Word.size S.P w.1 : ℂ) with hΦ
  have hΦc : Continuous Φ := by
    apply Continuous.div_const
    exact continuous_finsetSum _ fun h _ => continuous_finsetSum _ fun h' _ =>
      continuous_const.mul (continuous_finsetProd _ fun v _ => (hφc v h h').comp (continuous_coord S v))
  refine hΦc.aestronglyMeasurable.congr ?_
  filter_upwards [ae_coords_ne S] with c hc
  simp only [hΦ, C.HidaSetting.N1]
  congr 1
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun h' _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hφe v h h' _ (hc v)]

end limB

section limB2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem gram_withRR (S : C.HidaSetting E Wp Wq) (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (ε : ℝ) (k : ℕ) (w : C.Word S.f) (h h' : TB.Pt E) :
    (KB.withRR S RR).gram ε k w h h' = if k ≤ S.G.r + 1 then
      ∏ v, (KB.withRR S RR).gramLoc v ε k (w v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') else 0 := rfl

theorem level_norm_of_regularization_eq (S : C.HidaSetting E Wp Wq) (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (ε : ℝ) (i : ℕ) (w : C.Word S.f) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (c : J.CV E) :
    (KB.withRR S RR).N1 ε i w Y κ c = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (KB.withRR S RR).gramLoc v ε i (w v)
      (C.loc (S.σ v) h ++ [(1, c (S.pl v))]) (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
        (C.Word.size S.P w : ℂ) := rfl

variable (S : C.HidaSetting E Wp Wq) (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
  (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
    Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))

include hconv

theorem tendsto_gramLoc' (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (a : List C.Letter) (ha : D.AdmAt S v a)
    (p q : C.LPt) :
    Tendsto (fun n => ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G p) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G q) : ℝ) : ℂ) *
      RR n v ε i a p q) atTop (𝓝 (S.gramLoc v ε i a p q)) :=
  (hconv v ε hε i a ha p q).const_mul _

theorem tendsto_gram (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : k ≤ S.G.r + 1) (w' : S.W) (h h' : TB.Pt E) :
    Tendsto (fun n => (KB.withRR S (RR n)).gram ε k w'.1 h h') atTop (𝓝 (S.gram ε k w'.1 h h')) := by
  have e1 : (fun n => (KB.withRR S (RR n)).gram ε k w'.1 h h') = fun n =>
      ∏ v : Fin S.f, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h)) *
        √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h')) : ℝ) : ℂ) *
          RR n v ε k (w'.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') :=
    funext fun n => by rw [gram_withRR, if_pos hk]; rfl
  have e2 : S.gram ε k w'.1 h h' = ∏ v, S.gramLoc v ε k (w'.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') := by
    simp only [C.HidaSetting.gram, if_pos hk]
  rw [e1, e2]
  exact tendsto_finsetProd _ fun v _ => tendsto_gramLoc' S RR hconv v ε hε k (w'.1 v) ⟨w', rfl⟩ _ _

theorem tendsto_base_norm_of_regularization (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : k ≤ S.G.r + 1) (w' : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) :
    Tendsto (fun n => (KB.withRR S (RR n)).base.N0 ε k w' Y κ) atTop (𝓝 (S.base.N0 ε k w' Y κ)) := by
  have e : ∀ n, (KB.withRR S (RR n)).base.N0 ε k w' Y κ =
      (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * (KB.withRR S (RR n)).gram ε k w'.1 h h').re / C.Word.size S.P w'.1 :=
    fun n => rfl
  simp only [e]
  show Tendsto _ atTop (𝓝 ((∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε k w'.1 h h').re / C.Word.size S.P w'.1))
  exact ((Complex.continuous_re.tendsto _).comp (tendsto_finsetSum _ fun h _ => tendsto_finsetSum _
    fun h' _ => tendsto_const_nhds.mul (tendsto_gram S RR hconv ε hε k hk w' h h'))).div_const _

theorem tendsto_level_norm_of_regularization (ε : ℝ) (hε : 0 < ε) (i : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (c : J.CV E) :
    Tendsto (fun n => (KB.withRR S (RR n)).N1 ε i w.1 Y κ c) atTop (𝓝 (S.N1 ε i w.1 Y κ c)) := by
  have e1 : (fun n => (KB.withRR S (RR n)).N1 ε i w.1 Y κ c) = fun n =>
      (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v : Fin S.f,
        ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h ++ [(1, c (S.pl v))])) *
          √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) : ℝ) : ℂ) *
          RR n v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c (S.pl v))]) (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
          (C.Word.size S.P w.1 : ℂ) := funext fun n => rfl
  have e2 : S.N1 ε i w.1 Y κ c = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
        (C.loc (S.σ v) h ++ [(1, c (S.pl v))]) (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
          (C.Word.size S.P w.1 : ℂ) := rfl
  rw [e1, e2]
  exact (tendsto_finsetSum _ fun h _ => tendsto_finsetSum _ fun h' _ => tendsto_const_nhds.mul
    (tendsto_finsetProd _ fun v _ => tendsto_gramLoc' S RR hconv v ε hε i (w.1 v) ⟨w, rfl⟩ _ _)).div_const _

theorem tendsto_Nhat (hInt : ∀ n, KB.IntAll (KB.withRR S (RR n)))
    (hbd : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 →
      D.ptSize h' = i - 1 → ∃ C : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 →
        ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹)
    (ε : ℝ) (hε : 0 < ε) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E))
    (hY : ∀ h ∈ Y, TB.level h = i - 1) (κ : TB.Pt E → TB.Pt E → ℂ) (l : E) :
    Tendsto (fun n => (KB.withRR S (RR n)).Nhat ε i w.1 Y κ l) atTop (𝓝 (S.Nhat ε i w.1 Y κ l)) := by
  have e : ∀ n, (KB.withRR S (RR n)).Nhat ε i w.1 Y κ l =
      ((ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) : ℝ) : ℂ)⁻¹ *
        ∫ c : J.CV E, (KB.withRR S (RR n)).N1 ε i w.1 Y κ c * S.psiInf l c := fun n => rfl
  simp only [e]
  unfold C.HidaSetting.Nhat
  refine Tendsto.const_mul _ ?_
  have hB : ∀ v (h h' : Y), ∃ Cc : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 →
      ‖(KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c)])
        (C.loc (S.σ v) h' ++ [(1, c)])‖ ≤ Cc * ((1 + ‖c‖) ^ 3)⁻¹ :=
    fun v h h' => hbd v ε hε i hi1 hi2 (w.1 v) ⟨w, rfl⟩ _ _
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h h.2)
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h' h'.2)
  choose Cb hCb using hB
  set sz : ℂ := (C.Word.size S.P w.1 : ℂ) with hsz
  let g : (Fin S.f → ℂ) → ℝ := fun y =>
    (∑ h : Y, ∑ h' : Y, ‖κ h h'‖ * ∏ v, (Cb v h h' * ((1 + ‖y v‖) ^ 3)⁻¹)) / ‖sz‖
  have hgi : Integrable g := by
    refine Integrable.div_const (integrable_finsetSum _ fun h _ => integrable_finsetSum _ fun h' _ =>
      Integrable.const_mul (Integrable.fintype_prod (f := fun v c => Cb v h h' * ((1 + ‖c‖) ^ 3)⁻¹)
        fun v => integrable_decay3.const_mul _) _) _
  have hbi : Integrable (fun c : J.CV E => g (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S c)) :=
    (Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S).integrable_comp_of_integrable hgi
  refine tendsto_integral_of_dominated_convergence (fun c => g (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S c)) (fun n => ?_) hbi
    (fun n => ?_) ?_
  · exact (aestronglyMeasurable_level_norm (KB.withRR S (RR n)) (hInt n) ε hε i hi1 hi2 w Y hY κ).mul
      (continuous_psiInf S l).aestronglyMeasurable
  · filter_upwards [ae_coords_ne S] with c hc
    rw [norm_mul, norm_psiInf, mul_one, level_norm_of_regularization_eq, norm_div]
    simp only [g, Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    rw [← Finset.sum_coe_sort Y]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    rw [← Finset.sum_coe_sort Y]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h' _ => ?_)
    rw [norm_mul, norm_prod]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun v _ => norm_nonneg _)
      fun v _ => hCb v h h' _ _ (hc v)) (norm_nonneg _)
  · exact Eventually.of_forall fun c => (tendsto_level_norm_of_regularization S RR hconv ε hε i w Y κ c).mul_const _

end limB2

end

end Formalism.FourierDecayAlt.P.PBB
end

section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

theorem integral_formula_passes_to_limits : Formalism.FourierDecayAlt.KB.LimitInt := by
  intro E _ _ _ Wp Wq _ _ _ _ S RR hg1 hg2 hU hconv hInt hB
  have hbd : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h',
      D.ptSize h = i - 1 → D.ptSize h' = i - 1 → ∃ M : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 →
        ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ M * ((1 + ‖c‖) ^ 3)⁻¹ := by
    intro v ε hε i hi1 hi2 a ha h h' hh hh'
    obtain ⟨M, hM⟩ := hB v ε hε i hi1 hi2 a ha h h' hh hh'
    exact ⟨M, fun n => (hM n).1⟩
  refine ⟨PBB.K8.intAll_limit S RR hg1 hg2 hconv hInt hB, ?_⟩
  intro X hX ε hε i hi1 hi2 w hw hcnt
  set B := S.base.Wb (S.base.cnt w + C.Kst) with hBdef
  have hθ : ∀ n, ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb B (θ A)) ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ l ∈ S.base.Lad i, l ≠ 0 → ∀ A : Finset (Fin S.f),
          (∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖(KB.withRR S (RR n)).Nhat ε i w.1 Y κ l‖ ≤
            (∏ v ∈ A, X i v ^ C.Kst) *
              ∑ w' ∈ B, θ A w' * (KB.withRR S (RR n)).base.N0 ε (i - 1) w' Y κ :=
    fun n => hX n ε hε i hi1 hi2 w hw hcnt
  choose θ hprob hineq using hθ

  let F : ℕ → (Finset (Fin S.f) → B → ℝ) := fun n A x => θ n A x.1
  have hFb : ∀ n, F n ∈ Metric.closedBall (0 : Finset (Fin S.f) → B → ℝ) 1 := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro A
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro x
    have h0 := (hprob n A).1 x.1
    show ‖θ n A x.1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    calc θ n A x.1 ≤ ∑ w' ∈ B, θ n A w' :=
          Finset.single_le_sum (fun w' _ => (hprob n A).1 w') x.2
      _ = 1 := (hprob n A).2.2
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hFb
  have hco : ∀ A (x : B), Filter.Tendsto (fun n => θ (φ n) A x.1) Filter.atTop (nhds (a A x)) := by
    intro A x
    exact ((continuous_apply x).comp (continuous_apply A)).tendsto a |>.comp hlim
  let θ' : Finset (Fin S.f) → S.W → ℝ := fun A w' => if h : w' ∈ B then a A ⟨w', h⟩ else 0
  have hθ' : ∀ A w' (h : w' ∈ B), θ' A w' = a A ⟨w', h⟩ := fun A w' h => dif_pos h
  refine ⟨θ', ?_, ?_⟩
  · intro A
    refine ⟨?_, ?_, ?_⟩
    · intro w'
      by_cases h : w' ∈ B
      · rw [hθ' A w' h]
        exact ge_of_tendsto' (hco A ⟨w', h⟩) fun n => (hprob (φ n) A).1 w'
      · show 0 ≤ (if h : w' ∈ B then a A ⟨w', h⟩ else 0)
        rw [dif_neg h]
    · intro w' h
      show (if h : w' ∈ B then a A ⟨w', h⟩ else 0) = 0
      rw [dif_neg h]
    · have e1 : ∑ w' ∈ B, θ' A w' = ∑ x : B, a A x := by
        rw [← Finset.sum_coe_sort B]
        exact Finset.sum_congr rfl fun x _ => hθ' A x.1 x.2
      have e2 : ∀ n, ∑ x : B, θ (φ n) A x.1 = 1 := fun n => by
        rw [Finset.sum_coe_sort B (θ (φ n) A)]
        exact (hprob (φ n) A).2.2
      rw [e1]
      refine tendsto_nhds_unique (tendsto_finset_sum _ fun x _ => hco A x) ?_
      simp_rw [e2]
      exact tendsto_const_nhds
  · intro Y hY κ hκ l hl hl0 A
    have hL : Filter.Tendsto (fun n => (∏ v ∈ A, S.base.av v l ^ C.Kst) *
        ‖(KB.withRR S (RR (φ n))).Nhat ε i w.1 Y κ l‖) Filter.atTop
        (nhds ((∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖S.Nhat ε i w.1 Y κ l‖)) :=
      (((PBB.tendsto_Nhat S RR hconv hInt hbd ε hε i hi1 hi2 w Y hY κ l).comp
        hφ.tendsto_atTop).norm).const_mul _
    have hR : Filter.Tendsto (fun n => (∏ v ∈ A, X i v ^ C.Kst) *
        ∑ w' ∈ B, θ (φ n) A w' * (KB.withRR S (RR (φ n))).base.N0 ε (i - 1) w' Y κ) Filter.atTop
        (nhds ((∏ v ∈ A, X i v ^ C.Kst) * ∑ w' ∈ B, θ' A w' * S.base.N0 ε (i - 1) w' Y κ)) := by
      refine Filter.Tendsto.const_mul _ (tendsto_finset_sum _ fun w' hw' => ?_)
      refine Filter.Tendsto.mul ?_ ((PBB.tendsto_base_norm_of_regularization S RR hconv ε hε (i - 1) (by omega) w' Y κ).comp
        hφ.tendsto_atTop)
      rw [hθ' A w' hw']
      exact hco A ⟨w', hw'⟩
    exact le_of_tendsto_of_tendsto' hL hR fun n => hineq (φ n) Y hY κ hκ l hl hl0 A

end Formalism.FourierDecayAlt.P
end
