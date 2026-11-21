import Formalism.HermitianCurvature.HermitianCurvatureProofs.CptCopy2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjS
import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFTopFormCpt
import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFDomC
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.NFJCutFF
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.NFHatProdKBS
import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.NormalFormHatCompact

section
namespace CompanionTheory.BpCpt.NFId

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section beta

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem weight_zero (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∉ Qset D) :
    bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 := by
  have h1 : ¬ (0 < bcWeight k r (Tz k r D.z) (Tz k r D.z') q) := hq
  exact le_antisymm (not_lt.mp h1) (Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 k r _ _ q)

theorem jacobi_field_square_integrable (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : AB k r ≤ A) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 5 F) :
    AEStronglyMeasurable (fun q => hsVec (JF D F (gq D q))) (volume.restrict (Qset D)) ∧
      Integrable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖hsVec (JF D F (gq D q))‖ ^ 2)
        (volume.restrict (Qset D)) := by
  obtain ⟨_, _, _, hB1, _⟩ := b_any_of_xi k r Wp Wq D A hA
  obtain ⟨C0, hC0⟩ := hB1
  have hF4 : InCC A 4 F := JCx2.sq_inCC_mono le_rfl (by norm_num) hF
  obtain ⟨c4, hc4⟩ := hF4
  have hfin : normSq D F ≠ ⊤ := (hC0 F F c4 c4 hF hF hc4 hc4).1
  set w : (Fin r → ℂ) × ℂ → ℝ := bcWeight k r (Tz k r D.z) (Tz k r D.z') with hw
  set J : (Fin r → ℂ) × ℂ → _ := fun q => hsVec (JF D F (gq D q)) with hJ
  set h : (Fin r → ℂ) × ℂ → ℝ := fun q => w q * ‖J q‖ ^ 2 with hh
  set μQ : Measure ((Fin r → ℂ) × ℂ) := volume.restrict (Qset D) with hμQ
  have hw0 : ∀ q, 0 ≤ w q := fun q => JCTx2.bcWeight_nonneg' _ _ q
  have hh0 : ∀ q, 0 ≤ h q := fun q => mul_nonneg (hw0 q) (sq_nonneg _)
  have hcont : ContinuousOn F (GV k r) := B7.jc_cont ⟨c4, hc4⟩
  have hJm : AEStronglyMeasurable J μQ := by
    have h1 := B7.jc_aesm_J D hcont (1, 1)
    have e : (fun q => Jtau D (1, 1) F (gq D q)) = fun q => JF D F (gq D q) :=
      funext fun q => bessel_function_trivial_index k r Wp Wq D F (gq D q)
    rw [e] at h1
    exact JCTx2.hsVec_cont'.comp_aestronglyMeasurable h1
  have hwm : Measurable w := B7.measurable_bcWeight _ _
  have hhm : AEStronglyMeasurable h μQ := hwm.aestronglyMeasurable.mul (hJm.norm.pow 2)
  have hlin : normSq D F = ∫⁻ q, ENNReal.ofReal (h q) ∂μQ := by
    show (∫⁻ q, ENNReal.ofReal (h q)) = _
    rw [hμQ, setLIntegral_eq_of_support_subset]
    intro q hq
    by_contra hn
    apply hq
    have h0 : w q = 0 := weight_zero D hn
    simp only [hh, h0, zero_mul, ENNReal.ofReal_zero]
  refine ⟨hJm, hhm, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hh0), ← hlin]
  exact lt_top_iff_ne_top.2 hfin

theorem beta_restrict (D : RealPlaceData k r Wp Wq) (X Y : Mat k r → (Wq →L[ℂ] Wp)) :
    beta D X Y = ∫ q in Qset D, (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (hsVec (JF D Y (gq D q))) (hsVec (JF D X (gq D q))) := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rfl
  · intro q hq
    rw [weight_zero D hq]
    simp

theorem beta_cut_right (D : RealPlaceData k r Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {A : ℝ} (hA : AB k r ≤ A)
    {H F : Mat k r → (Wq →L[ℂ] Wp)} (hH : InCC A 5 H) (hF : InCC A 5 F) :
    Tendsto (fun ε => beta D H (Formalism.FourierDecayAlt.D.cutF D χ F ε)) (𝓝[>] 0) (𝓝 (beta D H F)) := by
  obtain ⟨hHm, hHi⟩ := jacobi_field_square_integrable D hA hH
  obtain ⟨hFm, hFi⟩ := jacobi_field_square_integrable D hA hF
  obtain ⟨M, hM0, hM⟩ := JCTx2.cut_bound hχ
  have hχc : Continuous χ := hχ.1.continuous
  have hGc : Continuous fun x : Mt k r => Gf k r D.z D.z' (Matrix.of x) :=
    (DifferentialOperatorClasses.gf_cont k r D.z D.z').comp continuous_id
  set w : (Fin r → ℂ) × ℂ → ℝ := bcWeight k r (Tz k r D.z) (Tz k r D.z') with hw
  have hw0 : ∀ q, 0 ≤ w q := fun q => JCTx2.bcWeight_nonneg' _ _ q
  have hwm : Measurable w := B7.measurable_bcWeight _ _
  have e : ∀ ε, beta D H (Formalism.FourierDecayAlt.D.cutF D χ F ε) = ∫ q in Qset D, ((χ (Gf k r D.z D.z' (gq D q) / ε) : ℝ) : ℂ) *
      ((w q : ℂ) * inner ℂ (hsVec (JF D F (gq D q))) (hsVec (JF D H (gq D q)))) := by
    intro ε
    rw [beta_restrict]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    simp only
    rw [JCTx2.JF_cutF, JCTx2.hsVec_smul', inner_smul_left, Complex.conj_ofReal]
    ring
  simp_rw [e]
  rw [beta_restrict]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun q => M * (w q * ‖hsVec (JF D F (gq D q))‖ ^ 2 + w q * ‖hsVec (JF D H (gq D q))‖ ^ 2)) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun ε => ?_
    have hχm : AEStronglyMeasurable (fun q => χ (Gf k r D.z D.z' (gq D q) / ε)) (volume.restrict (Qset D)) := by
      refine (((hχc.comp (hGc.div_const ε)).measurable.comp (B7.measurable_gqM D)).aestronglyMeasurable).congr ?_
      filter_upwards [B7.ae_mem_good_set_restrict D] with q hq
      simp only [Function.comp_apply]
      rw [B7.gqM_eq D hq]
      rfl
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hχm).mul
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable hwm.aestronglyMeasurable).mul (hFm.inner hHm))
  · refine Eventually.of_forall fun ε => ae_of_all _ fun q => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (hw0 q)]
    set a := ‖hsVec (JF D F (gq D q))‖
    set b := ‖hsVec (JF D H (gq D q))‖
    have h1 : ‖inner ℂ (hsVec (JF D F (gq D q))) (hsVec (JF D H (gq D q)))‖ ≤ a ^ 2 + b ^ 2 := by
      refine (norm_inner_le_norm _ _).trans ?_
      have ha : 0 ≤ a := norm_nonneg _
      have hb : 0 ≤ b := norm_nonneg _
      nlinarith [sq_nonneg (a - b), mul_nonneg ha hb]
    refine mul_le_mul (hM _) ?_ (mul_nonneg (hw0 q) (norm_nonneg _)) hM0
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left h1 (hw0 q)
  · exact (hFi.add hHi).const_mul _
  · filter_upwards [B7.ae_mem_good_set_restrict D] with q hq
    have hG : 0 < Gf k r D.z D.z' (gq D q) := (BigCellHermitian.gqDom D hq).2.2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds hG)] with ε hε hle
    rw [hχ.2.2 _ ((one_le_div (Set.mem_Ioi.mp hε)).mpr hle), Complex.ofReal_one, one_mul]

def fold (s : ℂ) (w : List C.Letter) (H : Mat k r → (Wq →L[ℂ] Wp)) : Mat k r → (Wq →L[ℂ] Wp) :=
  w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) H

theorem fold_add (s : ℂ) {X Y : Mat k r → (Wq →L[ℂ] Wp)} (hX : CkOn ⊤ (GV k r) X) (hY : CkOn ⊤ (GV k r) Y) :
    ∀ (w : List C.Letter), ∀ g ∈ GV k r,
      fold s w (X + (1 : ℂ) • Y) g = (fold s w X + (1 : ℂ) • fold s w Y) g
  | [], _, _ => rfl
  | a :: w, g, hg => by
    have G := Dx1.LZ.good_Tc (k := k) (r := r) (E := Wq →L[ℂ] Wp) s (a.2 : ℂ)
    have h1 := G.loc (fold s w (X + (1 : ℂ) • Y)) (fun y => fold s w X y + (1 : ℂ) • fold s w Y y)
      (fun y hy => fold_add s hX hY w y hy.1.1) g (Dx1.LZ.glev0 hg)
    have h2 := G.lin (fold s w X) (fold s w Y) 1 (Dx1.LZ.smooth_of_ck (fold_ckOn s w X hX))
      (Dx1.LZ.smooth_of_ck (fold_ckOn s w Y hY)) g (Dx1.LZ.glev0 hg)
    exact h1.trans h2

theorem fold_inCC (s : ℂ) {A : ℝ} {X : Mat k r → (Wq →L[ℂ] Wp)} (hX : CkOn ⊤ (GV k r) X) :
    ∀ (w : List C.Letter) (m : ℕ), InCC A (m + w.length * (2 * r + k + 1)) X → InCC A m (fold s w X)
  | [], m, h => by simpa [fold] using h
  | a :: w, m, h => by
    refine CutMP.ER.coefficient_vector_in_class k r Wp Wq s (a.2 : ℂ) A m (fold s w X) (fold_ckOn s w X hX)
      (fold_inCC s hX w _ ?_)
    have e : m + (2 * r + k + 1) + w.length * (2 * r + k + 1) = m + (a :: w).length * (2 * r + k + 1) := by
      rw [List.length_cons]; ring
    rw [e]; exact h

theorem q_expand (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : AB k r ≤ A) (s : ℂ) (w : List C.Letter)
    {X Y : Mat k r → (Wq →L[ℂ] Wp)} (hX : CkOn ⊤ (GV k r) X) (hY : CkOn ⊤ (GV k r) Y)
    (hXc : InCC A (5 + w.length * (2 * r + k + 1)) X) (hYc : InCC A (5 + w.length * (2 * r + k + 1)) Y) :
    beta D (fold s w (X + (1 : ℂ) • Y)) (X + (1 : ℂ) • Y) =
      beta D (fold s w X) X + beta D (fold s w X) Y + beta D (fold s w Y) X + beta D (fold s w Y) Y := by
  have hX5 : InCC A 5 X := JCx2.sq_inCC_mono le_rfl (by omega) hXc
  have hY5 : InCC A 5 Y := JCx2.sq_inCC_mono le_rfl (by omega) hYc
  have hfX := fold_inCC s hX w 5 hXc
  have hfY := fold_inCC s hY w 5 hYc
  have hS : InCC A 5 (X + (1 : ℂ) • Y) := JCx2.sq_inCC_add hX5 (JCx2.sq_inCC_smul 1 hY5)
  rw [JCx2.sq_beta_congr D (fold_add s hX hY w), (JCx2.sq_beta_sesq D hA hfX hfY hS 1).1,
    (JCx2.sq_beta_sesq D hA hX5 hY5 hfX 1).2, (JCx2.sq_beta_sesq D hA hX5 hY5 hfY 1).2]
  simp only [map_one, one_mul]
  ring

theorem q_symm (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : AB k r ≤ A) {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : conj s = s)
    (w : List C.Letter) {X Y : Mat k r → (Wq →L[ℂ] Wp)}
    (hX : CutMP.ER.Good D A (w.length * (2 * r + k + 1) + (2 * r + k + 1 + 5)) c X)
    (hY : CutMP.ER.Good D A (w.length * (2 * r + k + 1) + (2 * r + k + 1 + 5)) c Y) :
    beta D (fold s w X) Y = conj (beta D (fold s w Y) X) := by
  have h1 := CutMP.ER.fold_adj
    (CutMP.ER.capAdj_of_int (CutMP.ER.capAdjInt_of_scalar CutMP.ER.capacity_adjoint_scalar))
    CutMP.ER.capacity_theta_facts CutMP.ER.beta_form_congr_holds CutMP.ER.coefficient_vector_smoothness CutMP.ER.coefficient_vector_in_class
    CutMP.ER.coefficient_vector_support D hA hc hs w X Y hX hY
  have h2 := CutMP.ER.fold_rev CutMP.ER.coefficient_vector_smoothness CutMP.ER.coefficient_vector_congr CutMP.ER.coefficient_vector_commutation s w Y hY.1
  rw [beta_congr_right D h2] at h1
  exact h1.trans (CutMP.ER.beta_conj D X _)

theorem good_cut (D : RealPlaceData k r Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {c : ℝ} (h0 : ∀ x, x < c → χ x = 0)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F) {A₁ : ℝ} (hFA : ∀ m : ℕ, InCC A₁ m F) {ε : ℝ}
    (hε : 0 < ε) {m : ℕ} (hm : AB k r + 2 * ((r : ℝ) + 1) * (m : ℝ) ≤ A₁) :
    CutMP.ER.Good D (AB k r) m (c * ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε) := by
  refine ⟨JCTx6.Link2.ckOn_cutF D hχ hF ε, PBE.cutF_inCC D hχ hFA hε _ _ hm, fun g _ hg => ?_⟩
  by_contra hlt
  push Not at hlt
  apply hg
  have h1 : χ (Gf k r D.z D.z' g / ε) = 0 := h0 _ (by rw [div_lt_iff₀ hε]; exact hlt)
  simp only [Formalism.FourierDecayAlt.D.cutF, h1, Complex.ofReal_zero, zero_smul]

end beta

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem residue_zero_eq_beta_fold (p : KB.Pl P Wp Wq) {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hH : CkOn ⊤ (GV P.k P.r) H)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) :
    p.RR H 0 w [] [] = beta p.T.base (fold (M.sgn P p.l0) w H) H := by
  unfold KB.Pl.RR
  rw [level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hH (good_positioned_of_cut hw)]
  rfl

theorem q_loc (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV P.k P.r) F)
    {χ χ₁ : ℝ → ℝ} (hχ₁ : C6.IsCut0 χ₁) {κ δ : ℝ} (hκδ : κ < δ) (h0 : ∀ x, x < δ → χ x = 0)
    (h1 : ∀ x, κ ≤ x → χ₁ x = 1) (s : ℂ) (w : List C.Letter) {ε : ℝ} (hε : 0 < ε) :
    beta p.T.base (fold s w (D.cutF p.T.base χ₁ F ε)) (D.cutF p.T.base χ F ε) =
      beta p.T.base (fold s w F) (D.cutF p.T.base χ F ε) := by
  unfold B.beta betaBig
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only
  by_cases hq : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q = 0
  · simp [hq]
  obtain ⟨hgG, -⟩ := bigCell_pos p q hq
  by_cases hc : Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) / ε < δ
  · rw [JCTx2.JF_cutF, h0 _ hc, JCTx2.hsVec_smul']
    simp
  have hgt : κ * ε < Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) :=
    (lt_div_iff₀ hε).1 (lt_of_lt_of_le hκδ (not_lt.1 hc))
  have hU : IsOpen {x : B.Mat P.k P.r | κ * ε < Gf P.k P.r p.T.base.z p.T.base.z' x} :=
    isOpen_lt continuous_const (JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
  have he : ∀ x ∈ {x : B.Mat P.k P.r | κ * ε < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ GV P.k P.r,
      D.cutF p.T.base χ₁ F ε x = F x := by
    intro x hx
    unfold D.cutF
    rw [h1 _ ((le_div_iff₀ hε).2 (le_of_lt hx.1))]
    simp
  have hcut := JCTx6.Link2.ckOn_cutF p.T.base hχ₁ hF ε
  have e : JF p.T.base (fold s w (D.cutF p.T.base χ₁ F ε)) (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) =
      JF p.T.base (fold s w F) (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) :=
    jf_congr_level p.T.base hgG (fun x hx hGx =>
      fold_congr_open s hU hcut hF he w x ⟨by show κ * ε < _; rw [hGx]; exact hgt, hx⟩)
  rw [e]

theorem lim_top (p : KB.Pl P Wp Wq) {χ : ℝ → ℝ} {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List C.Letter}
    (hT : NFTopForm p χ F w) (hP : NFTopPtw p χ F w) (hD : NFTopDom p χ F w) :
    Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0) (𝓝 (∫ c, topD p F w c)) := by
  unfold NFTopForm at hT
  unfold NFTopPtw at hP
  unfold NFTopDom at hD
  obtain ⟨hmeas, h, hint, hbd⟩ := hD
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence h hmeas hbd hint
    (hP.mono fun c hc => tendsto_const_nhds.congr' (hc.mono fun ε hε => hε.symm))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hT ε hε).symm

theorem nfTopId_of_lim (p : KB.Pl P Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : CkOn ⊤ (GV P.k P.r) F) {A₁ : ℝ} (hFA : ∀ m : ℕ, InCC A₁ m F) {w : List C.Letter}
    (hw : KB.CutWord P p.l0 w)
    (hth : AB P.k P.r + 2 * ((P.r : ℝ) + 1) *
      ((w.length * (2 * P.r + P.k + 1) + (2 * P.r + P.k + 1 + 5) : ℕ) : ℝ) ≤ A₁)
    (hL : ∀ χ' : ℝ → ℝ, C6.IsCut0 χ' →
      Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ' F ε) 0 w [] []).re) (𝓝[>] 0) (𝓝 (∫ c, topD p F w c))) :
    NFTopId p χ F w := by
  obtain ⟨δ, hδ, hχ0⟩ := hχ.2.1
  set κ : ℝ := min δ 1 / 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    have : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  have hκδ : κ < δ := by
    have : min δ 1 ≤ δ := min_le_left _ _
    linarith
  have hκδ' : κ * δ ≤ δ := by nlinarith
  set χ₁ : ℝ → ℝ := fun x => χ (x / κ) with hχ₁def
  have hχ₁0 : ∀ x, x < κ * δ → χ₁ x = 0 := fun x hx => hχ0 _ (by rw [div_lt_iff₀ hκ]; linarith)
  have hχ₁1 : ∀ x, κ ≤ x → χ₁ x = 1 := fun x hx => hχ.2.2 _ ((le_div_iff₀ hκ).2 (by linarith))
  have hχ₁ : C6.IsCut0 χ₁ :=
    ⟨hχ.1.comp (contDiff_id.div_const κ), ⟨κ * δ, mul_pos hκ hδ, hχ₁0⟩, fun x hx => hχ₁1 x (hκ1.trans hx)⟩
  have hχ0' : ∀ x, x < κ * δ → χ x = 0 := fun x hx => hχ0 x (lt_of_lt_of_le hx hκδ')
  set χ₂ : ℝ → ℝ := fun x => (χ₁ x + χ x) / 2 with hχ₂def
  have hχ₂0 : ∀ x, x < κ * δ → χ₂ x = 0 := fun x hx => by simp only [hχ₂def, hχ₁0 x hx, hχ0' x hx]; norm_num
  have hχ₂ : C6.IsCut0 χ₂ :=
    ⟨(hχ₁.1.add hχ.1).div_const 2, ⟨κ * δ, mul_pos hκ hδ, hχ₂0⟩, fun x hx => by
      simp only [hχ₂def, hχ₁.2.2 x hx, hχ.2.2 x hx]; norm_num⟩
  set s : ℂ := M.sgn P p.l0 with hsdef
  have hs : conj s = s := by rw [hsdef]; unfold M.sgn; simp
  have hAB : AB P.k P.r ≤ A₁ := le_trans (le_add_of_nonneg_right (by positivity)) hth
  have key : ∀ ε : ℝ, 0 < ε → (beta p.T.base (fold s w F) (D.cutF p.T.base χ F ε)).re =
      (4 * (p.RR (D.cutF p.T.base χ₂ F ε) 0 w [] []).re - (p.RR (D.cutF p.T.base χ₁ F ε) 0 w [] []).re -
        (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) / 2 := by
    intro ε hε
    have gA := good_cut p.T.base hχ hχ0' hF hFA hε hth
    have gB := good_cut p.T.base hχ₁ hχ₁0 hF hFA hε hth
    have gS := good_cut p.T.base hχ₂ hχ₂0 hF hFA hε hth
    have hm : 5 + w.length * (2 * P.r + P.k + 1) ≤ w.length * (2 * P.r + P.k + 1) + (2 * P.r + P.k + 1 + 5) := by
      omega
    have e1 := q_expand p.T.base le_rfl s w gB.1 gA.1 (JCx2.sq_inCC_mono le_rfl hm gB.2.1)
      (JCx2.sq_inCC_mono le_rfl hm gA.2.1)
    have e2 := q_expand p.T.base le_rfl s w gS.1 gS.1 (JCx2.sq_inCC_mono le_rfl hm gS.2.1)
      (JCx2.sq_inCC_mono le_rfl hm gS.2.1)
    have e3 : D.cutF p.T.base χ₁ F ε + (1 : ℂ) • D.cutF p.T.base χ F ε =
        D.cutF p.T.base χ₂ F ε + (1 : ℂ) • D.cutF p.T.base χ₂ F ε := by
      funext g
      simp only [D.cutF, Pi.add_apply, one_smul, hχ₂def, ← add_smul]
      congr 1
      push_cast
      ring
    have e4 := q_symm p.T.base le_rfl (mul_pos (mul_pos hκ hδ) hε) hs w gA gB
    rw [e3, e2, e4, q_loc p hF hχ₁ hκδ hχ0 hχ₁1 s w hε] at e1
    rw [residue_zero_eq_beta_fold p gS.1 hw, residue_zero_eq_beta_fold p gB.1 hw, residue_zero_eq_beta_fold p gA.1 hw]
    have e5 := congrArg Complex.re e1
    simp only [Complex.add_re, Complex.conj_re] at e5
    linarith
  have hF5 : InCC (AB P.k P.r) 5 F := JCx2.sq_inCC_mono hAB le_rfl (hFA 5)
  have hH5 : InCC (AB P.k P.r) 5 (fold s w F) := fold_inCC s hF w 5 (JCx2.sq_inCC_mono hAB le_rfl (hFA _))
  have l1 := (Complex.continuous_re.tendsto _).comp (beta_cut_right p.T.base hχ le_rfl hH5 hF5)
  have l2 := ((((hL χ₂ hχ₂).const_mul 4).sub (hL χ₁ hχ₁)).sub (hL χ hχ)).div_const 2
  have l3 : Tendsto (fun ε : ℝ => (beta p.T.base (fold s w F) (D.cutF p.T.base χ F ε)).re) (𝓝[>] 0) _ :=
    l2.congr' (eventually_nhdsWithin_of_forall fun ε hε => (key ε hε).symm)
  have l4 : Tendsto (fun ε : ℝ => (beta p.T.base (fold s w F) (D.cutF p.T.base χ F ε)).re) (𝓝[>] 0)
      (𝓝 (beta p.T.base (fold s w F) F).re) := l1
  have := tendsto_nhds_unique l3 l4
  unfold NFTopId
  rw [residue_zero_eq_beta_fold p hF hw, ← this]
  ring

end place

theorem nfHyp_mono {Cb c c' : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A₀ : ℝ} {p₀ : ℕ} {χ χ' : ℝ → ℝ} {N : ℕ}
    (h : NFHyp Cb c p f A₀ p₀ χ N) (hc : c' ≤ c) (hχ' : C6.IsCut0 χ') : NFHyp Cb c' p f A₀ p₀ χ' N := by
  unfold NFHyp at h ⊢
  obtain ⟨_, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hχ', h2, h3, h4, le_trans ?_ h5, h6⟩
  have ha : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 := by positivity
  have hb : (0 : ℝ) ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc ha) hb

theorem nfTopIdAll_of_diag
    (h1 : ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
      NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
        NFTopForm p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w)
    (h2 : NFTopPtwAll) (h3 : NFTopDomAll) : NFTopIdAll := by
  intro Cb
  obtain ⟨C1, H1⟩ := h1 Cb
  obtain ⟨C2, H2⟩ := h2 Cb
  obtain ⟨C3, H3⟩ := h3 Cb
  refine ⟨max (max C1 C2) (max C3 100), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  have m1 : C1 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_left (le_max_left _ _)
  have m2 : C2 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_left (le_max_right _ _)
  have m3 : C3 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_right (le_max_left _ _)
  have m4 : 100 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_right (le_max_right _ _)
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  refine nfTopId_of_lim p hH.1 (ckOn_fpm p p₀ hH.2.2.1 hid) (inCC_fpm_id p p₀ hH.2.2.2.1) hw.1
    (CutMP.ER.bound_aux P.r P.k w.length N _ hN (nfHyp_mono hH m4 hH.1).2.2.2.2.1) fun χ' hχ' => ?_
  exact lim_top p (H1 Wp Wq P p f A₀ p₀ χ' Y N (nfHyp_mono hH m1 hχ') w hw hN)
    (H2 Wp Wq P p f A₀ p₀ χ' Y N (nfHyp_mono hH m2 hχ') w hw hN)
    (H3 Wp Wq P p f A₀ p₀ χ' Y N (nfHyp_mono hH m3 hχ') w hw hN)

end

end CompanionTheory.BpCpt.NFId
end

section
namespace Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def NFTopDomAllJ : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → B.JF p.T.base f ∈ FFKB p → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopDom p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w



theorem blockGrowthBound_apx_cutF (hA : P5.ThmPActualCpt) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hχ : C6.IsCut0 χ)
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (hnn : ∀ y, 0 < nn y) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N := fun _ hε n =>
  block_growth_bound_of_compact_coefCpt hA p nn _ Y K N Cb hCb (cptCoef_apx P p.T.base hχ hF hε n) hnn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem limEvT_J (hA : P5.ThmPActualCpt) (h3 : NFTopDomAllJ) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → B.JF p.T.base f ∈ FFKB p →
      LimEvT p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  obtain ⟨C1, H1⟩ := CompanionTheory.NFCpt.top_form_all_compact hA Cb
  obtain ⟨C2, H2⟩ := top_pointwise_all_levels_holds Cb
  obtain ⟨C3, H3⟩ := h3 Cb
  refine ⟨max (max C1 C2) (max C3 100), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH hJ w hw hN
  have m1 : C1 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_left (le_max_left _ _)
  have m2 : C2 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_left (le_max_right _ _)
  have m3 : C3 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_right (le_max_left _ _)
  have m4 : 100 ≤ max (max C1 C2) (max C3 100) := le_max_of_le_right (le_max_right _ _)
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hL := fun (χ' : ℝ → ℝ) (hχ' : C6.IsCut0 χ') => CompanionTheory.BpCpt.NFId.lim_top p
    (H1 Wp Wq P p f A₀ p₀ χ' Y N (CompanionTheory.BpCpt.NFId.nfHyp_mono hH m1 hχ') w hw hN)
    (H2 Wp Wq P p f A₀ p₀ χ' Y N (CompanionTheory.BpCpt.NFId.nfHyp_mono hH m2 hχ') w hw hN)
    (H3 Wp Wq P p f A₀ p₀ χ' Y N (CompanionTheory.BpCpt.NFId.nfHyp_mono hH m3 hχ') hJ w hw hN)
  have hId := CompanionTheory.BpCpt.NFId.nfTopId_of_lim p hH.1 (ckOn_fpm p p₀ hH.2.2.1 hid) (inCC_fpm_id p p₀ hH.2.2.2.1) hw.1
    (CutMP.ER.bound_aux P.r P.k w.length N _ hN (CompanionTheory.BpCpt.NFId.nfHyp_mono hH m4 hH.1).2.2.2.2.1) hL
  unfold NFTopId at hId
  rw [← hId]
  exact hL χ hH.1

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_J (h3 : NFTopDomAllJ)
    (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
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
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  have hA : P5.ThmPActualCpt := CutSE.actual_compact_theorem
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ := thmBpAt_main2Cpt hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := limEvT_J hA h3 Cb
  refine ⟨C₄, c₃, Cc, Cc', Cn, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hJ hth1 hth2 hth3
    hth4 hN2 hexp hWG hLG hBd
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3 hexp hWG hLG
    (blockGrowthBound_apx_cutF hA p nn χ _ Y K N Cb hCb hχ (ckOn_fpm p p₀ hf hid) hnn)
    (hn Wp Wq P p f A₀ p₀ χ Y N ⟨hχ, hCb, hf, hfA, hth4, hN2⟩ hJ) hBd

end

end Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

namespace Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination MeasureTheory
open scoped ENNReal

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_eqR_J (h3 : NFTopDomAllJ)
    (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (S : ShiftAtR p f b n₀)
      (Λ A₀ : ℝ) (p₀ : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ →
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      B.JF S.pp.T.base (fun g => (f g).comp (S.Ap g)) ∈ FFKB S.pp →
      B.JF S.pm.T.base (fun g => (f g).comp (S.Am g)) ∈ FFKB S.pm →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid S.pp nnp Yp Λ K N → TBBx5.LiftGrid S.pp nnp Yp Λ K N →
      TBBx5.WaveGrid S.pm nnm Ym Λ K N → TBBx5.LiftGrid S.pm nnm Ym Λ K N →
      LimBd S.pp nnp (fpmSh S.pp f S.Ap p₀) Yp N → LimBd S.pm nnm (fpmSh S.pm f S.Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  have hA : P5.ThmPActualCpt := CutSE.actual_compact_theorem
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ :=
    thmBpAt_eq_limEvTCpt hA Formalism.FourierDecayAlt.P.CutBP2.normaliser_across_places Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := limEvT_J hA h3 Cb
  refine ⟨C₄, c₃, Cc, Cc', Cn, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnnp hnnm hDDp
    hDDm hf hfA hJp hJm hth1 hth2 hth3 hth4 hN2 hexp hWGp hLGp hWGm hLGm hBdp hBdm
  have hI5p := blockGrowthBound_apx_cutF hA S.pp nnp χ _ Yp K N Cb hDDp hχ (ckOn_fpmSh S.pp p₀ hf (ckOn_of_polyOp S.polyP)) hnnp
  have hI5m := blockGrowthBound_apx_cutF hA S.pm nnm χ _ Ym K N Cb hDDm hχ (ckOn_fpmSh S.pm p₀ hf (ckOn_of_polyOp S.polyM)) hnnm
  have hth4' : Cn * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      (A₀ - ((n₀ * (P.r + 1) : ℕ) : ℝ)) - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by linarith
  have hLp : LimEvT S.pp χ (fpmSh S.pp f S.Ap p₀) Yp N := by
    have e := fpmSh_eq_fpm S.pp f S.Ap p₀
    have k := hn Wp S.Wqp (shP P S.up S.up') S.pp (fun g => (f g).comp (S.Ap g)) (A₀ - ((n₀ * (P.r + 1) : ℕ) : ℝ)) p₀ χ Yp N
      ⟨hχ, hDDp, ckOn_compSh hf (ckOn_of_polyOp S.polyP), inCC_compSh S.pp hfA S.polyP, hth4', hN2⟩ hJp
    exact Eq.mpr (congrArg (fun F => LimEvT S.pp χ F Yp N) e) k
  have hLm : LimEvT S.pm χ (fpmSh S.pm f S.Am p₀) Ym N := by
    have e := fpmSh_eq_fpm S.pm f S.Am p₀
    have k := hn Wp S.Wqm (shP P S.um S.um') S.pm (fun g => (f g).comp (S.Am g)) (A₀ - ((n₀ * (P.r + 1) : ℕ) : ℝ)) p₀ χ Ym N
      ⟨hχ, hDDm, ckOn_compSh hf (ckOn_of_polyOp S.polyM), inCC_compSh S.pm hfA S.polyM, hth4', hN2⟩ hJm
    exact Eq.mpr (congrArg (fun F => LimEvT S.pm χ F Ym N) e) k
  exact h P Wp Wq S.Wqp S.Wqm S.up S.up' S.um S.um' p S.pp S.pm f S.Ap S.Am S.ApPt S.AmPt b Λ
    (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ)) n₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ S.hzp S.hzp' S.hzm
    S.hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf (ckOn_of_polyOp S.polyP) (ckOn_of_polyOp S.polyM)
    (shifted_decay P Wp Wq S.Wqp S.up S.up' S.pp f S.Ap A₀ (n₀ * (P.r + 1)) p₀ hfA S.polyP)
    (shifted_decay P Wp Wq S.Wqm S.um S.um' S.pm f S.Am A₀ (n₀ * (P.r + 1)) p₀ hfA S.polyM)
    hth1 hth2 hth3 S.amaps hexp hWGp hLGp hWGm hLGm hI5p hI5m hLp hLm hBdp hBdm

end

end Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination
end

section
namespace Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem nfTopIdAll_of_dom (h3 : NFTopDomAll) : NFTopIdAll :=
  CompanionTheory.BpCpt.NFId.nfTopIdAll_of_diag (CompanionTheory.NFCpt.top_form_all_compact CutSE.actual_compact_theorem)
    top_pointwise_all_levels_holds h3

theorem nfTopDomAll_of_tieC (hT : CompanionTheory.NFCpt.NFTieHatC) : NFTopDomAll :=
  CompanionTheory.NFCpt.nfTopDomAll_of_C hT LimitNormalForms.normal_form_hat_product_bessel LimitNormalForms.normal_form_jacobi_cutoff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_dom (h3 : NFTopDomAll)
    (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
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
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  have hA : P5.ThmPActualCpt := CutSE.actual_compact_theorem
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := thmBpAt_main4Cpt hA CompanionTheory.NFCpt.top_form_all_compact
    top_pointwise_all_levels_holds h3 (nfTopIdAll_of_dom h3) Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3
    hth4 hN2 hexp hWG hLG hBd
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3 hth4 hN2 hexp
    hWG hLG (blockGrowthBound_apx_cutF hA p nn χ _ Y K N Cb hCb hχ (ckOn_fpm p p₀ hf hid) hnn) hBd

end

end Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

namespace Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination MeasureTheory
open scoped ENNReal

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_eqR_dom (h3 : NFTopDomAll)
    (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (S : ShiftAtR p f b n₀)
      (Λ A₀ : ℝ) (p₀ : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ →
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid S.pp nnp Yp Λ K N → TBBx5.LiftGrid S.pp nnp Yp Λ K N →
      TBBx5.WaveGrid S.pm nnm Ym Λ K N → TBBx5.LiftGrid S.pm nnm Ym Λ K N →
      LimBd S.pp nnp (fpmSh S.pp f S.Ap p₀) Yp N → LimBd S.pm nnm (fpmSh S.pm f S.Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  have hA : P5.ThmPActualCpt := CutSE.actual_compact_theorem
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := thmBpAt_eq_NFRCpt hA CompanionTheory.NFCpt.top_form_all_compact
    top_pointwise_all_levels_holds h3 (nfTopIdAll_of_dom h3) Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnnp hnnm hDDp
    hDDm hf hfA hth1 hth2 hth3 hth4 hN2 hexp hWGp hLGp hWGm hLGm hBdp hBdm
  exact h P Wp Wq p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnnp hnnm hDDp
    hDDm hf hfA hth1 hth2 hth3 hth4 hN2 hexp hWGp hLGp hWGm hLGm
    (blockGrowthBound_apx_cutF hA S.pp nnp χ _ Yp K N Cb hDDp hχ (ckOn_fpmSh S.pp p₀ hf (ckOn_of_polyOp S.polyP)) hnnp)
    (blockGrowthBound_apx_cutF hA S.pm nnm χ _ Ym K N Cb hDDm hχ (ckOn_fpmSh S.pm p₀ hf (ckOn_of_polyOp S.polyM)) hnnm) hBdp hBdm

end

end Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination
end

section
namespace Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem normal_form_top_domination : NFTopDomAll := nfTopDomAll_of_tieC NormalFormRelations.normal_form_hat_compact

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_top (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
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
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ :=
  thmBpAt_dom normal_form_top_domination Cb C₃ CΛ C₀ hC₃ hCΛ hC₀

end

end Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

namespace Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination MeasureTheory
open scoped ENNReal

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_eqR_top (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (S : ShiftAtR p f b n₀)
      (Λ A₀ : ℝ) (p₀ : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ →
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid S.pp nnp Yp Λ K N → TBBx5.LiftGrid S.pp nnp Yp Λ K N →
      TBBx5.WaveGrid S.pm nnm Ym Λ K N → TBBx5.LiftGrid S.pm nnm Ym Λ K N →
      LimBd S.pp nnp (fpmSh S.pp f S.Ap p₀) Yp N → LimBd S.pm nnm (fpmSh S.pm f S.Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ :=
  thmBpAt_eqR_dom normal_form_top_domination Cb C₃ CΛ C₀ hC₃ hCΛ hC₀

end

end Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination
end
