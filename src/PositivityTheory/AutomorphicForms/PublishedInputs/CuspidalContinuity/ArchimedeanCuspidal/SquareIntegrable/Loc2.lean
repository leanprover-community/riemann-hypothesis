import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCentralCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothnessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGaugeBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNonvanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishingAtZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefinedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerPureTensorFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLinearityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLocalTateIntegralStatement

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.SchwartzSpaceL2

theorem top (hpsi : SPsi) (hcen : SCen) (htr : STrans) (hsm : SSmooth) (hbd : SBound) (hne : SNe)
    (hun : SUnr) (hfe : FeGen) : Loc2 := by
  intro F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hun F ψ hψ μ₁ μ₂ h₁ h₂⟩
  · obtain ⟨φ, hφ, h⟩ := hne F ψ hψ μ₁ μ₂ h₁ h₂
    exact ⟨_, Submodule.subset_span ⟨φ, hφ, rfl⟩, h⟩
  · intro W hW h
    induction hW using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, rfl⟩ := hx
      obtain ⟨hm, he⟩ := htr F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ h
      have : (fun g => W2 ψ μ₁ μ₂ φ (g * h)) =
          (((μ₂ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (1 / 2)) •
            W2 ψ μ₁ μ₂ (rt φ h) := by
        funext g; rw [he g]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  · intro W hW x g
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hpsi F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ x g
    | zero => simp
    | add u v _ _ hu hv => simp only [Pi.add_apply, hu, hv]; ring
    | smul a u _ hu => simp only [Pi.smul_apply, smul_eq_mul, hu]; ring
  · intro W hW a g
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hcen F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ a g
    | zero => simp
    | add u v _ _ hu hv => simp only [Pi.add_apply, hu, hv]; ring
    | smul b u _ hu => simp only [Pi.smul_apply, smul_eq_mul, hu]; ring
  · intro W hW
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hsm F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ
    | zero => exact ⟨⊤, fun _ _ _ => rfl⟩
    | add u v _ _ hu hv =>
      obtain ⟨U, hU⟩ := hu
      obtain ⟨V, hV⟩ := hv
      refine ⟨U ⊓ V, fun g w hw => ?_⟩
      simp only [Pi.add_apply, hU g w hw.1, hV g w hw.2]
    | smul b u _ hu =>
      obtain ⟨U, hU⟩ := hu
      exact ⟨U, fun g w hw => by simp only [Pi.smul_apply, hU g w hw]⟩
  · intro W hW ε hε
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hbd F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ ε hε
    | zero => exact ⟨0, 0, fun a k _ => ⟨by simp, fun h => absurd rfl h⟩⟩
    | add u v _ _ hu hv =>
      obtain ⟨C₁, B₁, hu⟩ := hu
      obtain ⟨C₂, B₂, hv⟩ := hv
      refine ⟨C₁ + C₂, max B₁ B₂, fun a k hk => ⟨?_, fun hne => ?_⟩⟩
      · have h1 := (hu a k hk).1
        have h2 := (hv a k hk).1
        calc ‖(u + v) (dg2 a 1 * k)‖ ≤ ‖u (dg2 a 1 * k)‖ + ‖v (dg2 a 1 * k)‖ := norm_add_le _ _
          _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2
      · by_cases hu0 : u (dg2 a 1 * k) = 0
        · have : v (dg2 a 1 * k) ≠ 0 := by
            intro h0; apply hne; simp [hu0, h0]
          exact le_max_of_le_right ((hv a k hk).2 this)
        · exact le_max_of_le_left ((hu a k hk).2 hu0)
    | smul b u _ hu =>
      obtain ⟨C, B, hu⟩ := hu
      refine ⟨‖b‖ * C, B, fun a k hk => ⟨?_, fun hne => ?_⟩⟩
      · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hu a k hk).1 (norm_nonneg _)
      · refine (hu a k hk).2 fun h0 => hne ?_
        simp [h0]
  · intro W hW c hc s hs0 hs1
    suffices H : Integrable (fun a : Fˣ => W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
          mp a (1 / 2 - s)) (multHaar F) ∧
        Integrable (fun a : Fˣ => W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
        ∫ a, W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
          gam ψ (μ₁ * c) s * gam ψ (μ₂ * c) s *
            ∫ a, W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F from H.2.2
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hfe F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ c hc s hs0 hs1
    | zero => simp
    | add u v _ _ hu hv =>
      obtain ⟨hu1, hu2, hu3⟩ := hu
      obtain ⟨hv1, hv2, hv3⟩ := hv
      simp only [Pi.add_apply, add_mul]
      refine ⟨hu1.add hv1, hu2.add hv2, ?_⟩
      rw [integral_add hu1 hv1, integral_add hu2 hv2, hu3, hv3]
      ring
    | smul b u _ hu =>
      obtain ⟨hu1, hu2, hu3⟩ := hu
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      simp only [← mul_assoc] at hu1 hu2 hu3 ⊢
      refine ⟨?_, ?_, ?_⟩
      · simpa only [mul_assoc] using hu1.const_mul b
      · simpa only [mul_assoc] using hu2.const_mul b
      · simp only [mul_assoc]
        rw [integral_const_mul, integral_const_mul]
        simp only [← mul_assoc] at hu3 ⊢
        rw [hu3]
        ring

theorem top' (hpsi : SPsi) (hcen : SCen) (htr : STrans) (hsm : SSmooth) (hbd : SBound) (hne : SNe)
    (hun : SUnr) (hdz : SDZ) (hwd : SWd) (hpu : SPure) (hli : SLin) (hta : STate) (hfe : SFe) : Loc2 :=
  top hpsi hcen htr hsm hbd hne hun (hfe hdz hwd hpu hli htr hta)

end Ad3.SchwartzSpaceL2
end
end

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

set_option linter.unusedSectionVars false

namespace Ad3.SchwartzSpaceL2.PFe

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem isUnit1_mul {μ ν : Fˣ →* ℂˣ} (hμ : IsUnit1 μ) (hν : IsUnit1 ν) : IsUnit1 (μ * ν) := by
  refine ⟨?_, fun x => ?_⟩
  · exact hμ.1.mul hν.1
  · simp [MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ.2 x, hν.2 x]

theorem isUnit1_inv {μ : Fˣ →* ℂˣ} (hμ : IsUnit1 μ) : IsUnit1 μ⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · exact hμ.1.inv
  · simp [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hμ.2 x]

theorem mp_add (a : Fˣ) (s t : ℂ) : mp a s * mp a t = mp a (s + t) := by
  unfold mp
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (modulus_pos a.ne_zero).ne'))]

theorem mp_one (s : ℂ) : mp (1 : Fˣ) s = 1 := by
  unfold mp
  simp [modulus_one]

theorem det_weyl_GL2 : GeneralLinearGroup.det (w0 : GL (Fin 2) F) = 1 := by
  ext
  simp [w0, Matrix.det_fin_two]

theorem rightTranslate_pureTensor_weyl (f g : F → ℂ) : rt (pt f g) (w0 : GL (Fin 2) F) = pt g (fun x => f (-x)) := by
  funext x
  simp [rt, pt, w0, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

theorem pt_mem {f g : F → ℂ} (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F) :
    pt f g ∈ GodementSectionLocal.schwartzBruhat2 F := by
  refine ⟨?_, ?_⟩
  · exact (hf.1.comp_continuous (continuous_apply 0)).mul (hg.1.comp_continuous (continuous_apply 1))
  · refine HasCompactSupport.intro ((hf.2.isCompact.prod hg.2.isCompact).image
      (f := fun p : F × F => ![p.1, p.2]) ?_) ?_
    · exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
    · intro x hx
      by_contra h
      apply hx
      refine ⟨(x 0, x 1), ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩, ?_⟩
      · exact Function.mem_support.mpr fun h0 => h (by simp [pt, h0])
      · exact Function.mem_support.mpr fun h1 => h (by simp [pt, h1])
      · ext i; fin_cases i <;> rfl

theorem comp_neg_mem {f : F → ℂ} (hf : f ∈ schwartzBruhat F) :
    (fun x => f (-x)) ∈ schwartzBruhat F :=
  ⟨hf.1.comp_continuous continuous_neg, hf.2.comp_homeomorph (Homeomorph.neg F)⟩

theorem fourier_mem {ψ : AddChar F Circle} (hψ : IsStd ψ) {f : F → ℂ} (hf : f ∈ schwartzBruhat F) :
    localFourier (selfDualMeasure ψ) ψ f ∈ schwartzBruhat F :=
  localFourier_mem_schwartzBruhat (μ := selfDualMeasure ψ) (hψ := hψ.1) (hψ1 := hψ.2.1) hf

theorem character_inverse_identity_first (μ₁ μ₂ c : Fˣ →* ℂˣ) : μ₂ * c * (μ₁⁻¹ * μ₂)⁻¹ = μ₁ * c := by
  ext x
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem character_inverse_identity_second (μ₁ μ₂ c : Fˣ →* ℂˣ) : (μ₁ * c)⁻¹ * (μ₁⁻¹ * μ₂)⁻¹ = (μ₂ * c)⁻¹ := by
  ext x
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem rhs_pure (hDZ : SDZ) (hWd : SWd) {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ}
    (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) {f g : F → ℂ} (hf : f ∈ schwartzBruhat F)
    (hg : g ∈ schwartzBruhat F) {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2))
        (multHaar F) ∧
      ∫ a, W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F =
        localZeta f (μ₂ * c) s *
          localZeta (fun x => localFourier (selfDualMeasure ψ) ψ g (-x)) (μ₁ * c) s := by
  obtain ⟨hI, hE⟩ := hDZ F f hf (fun x => localFourier (selfDualMeasure ψ) ψ g (-x))
    (comp_neg_mem (fourier_mem hψ hg)) (μ₂ * c) (μ₁⁻¹ * μ₂) (isUnit1_mul h₂ hc)
    (isUnit1_mul (isUnit1_inv h₁) h₂) s hs
  beta_reduce at hI hE
  have hfun : (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) =
      fun a => (((μ₂ * c) a : ℂˣ) : ℂ) * mp a s *
        ∫ h : Fˣ, (((μ₁⁻¹ * μ₂) h : ℂˣ) : ℂ) * f ((h : F) * a) *
          localFourier (selfDualMeasure ψ) ψ g (-((h⁻¹ : Fˣ) : F)) ∂multHaar F := by
    funext a
    have key : mp a (1 / 2) * mp a (s - 1 / 2) = mp a s := by rw [mp_add]; congr 1; ring
    rw [hWd F ψ hψ μ₁ μ₂ h₁ h₂ f hf g hg a, ← key]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
    ring
  rw [hfun]
  exact ⟨hI, by rw [hE, character_inverse_identity_first]⟩

theorem lhs_pure (hDZ : SDZ) (hWd : SWd) (hTr : STrans) {ψ : AddChar F Circle} (hψ : IsStd ψ)
    {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) {f g : F → ℂ} (hf : f ∈ schwartzBruhat F)
    (hg : g ∈ schwartzBruhat F) {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ} (hs : s.re < 1) :
    Integrable (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
        mp a (1 / 2 - s)) (multHaar F) ∧
      ∫ a, W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
          mp a (1 / 2 - s) ∂multHaar F =
        localZeta g (μ₁ * c)⁻¹ (1 - s) *
          localZeta (fun x => localFourier (selfDualMeasure ψ) ψ (fun y => f (-y)) (-x)) (μ₂ * c)⁻¹ (1 - s) := by
  have hf' := comp_neg_mem hf
  have hs' : 0 < (1 - s).re := by simp; linarith
  obtain ⟨hI, hE⟩ := hDZ F g hg (fun x => localFourier (selfDualMeasure ψ) ψ (fun y => f (-y)) (-x))
    (comp_neg_mem (fourier_mem hψ hf')) (μ₁ * c)⁻¹ (μ₁⁻¹ * μ₂) (isUnit1_inv (isUnit1_mul h₁ hc))
    (isUnit1_mul (isUnit1_inv h₁) h₂) (1 - s) hs'
  beta_reduce at hI hE
  have hw : ∀ a : Fˣ, W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) = W2 ψ μ₁ μ₂ (pt g (fun y => f (-y))) (dg2 a 1) := by
    intro a
    rw [(hTr F ψ hψ μ₁ μ₂ h₁ h₂ _ (pt_mem hf hg) w0).2, det_weyl_GL2, rightTranslate_pureTensor_weyl, map_one, Units.val_one, mp_one,
      one_mul, one_mul]
  have hfun : (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
        mp a (1 / 2 - s)) =
      fun a => ((((μ₁ * c)⁻¹) a : ℂˣ) : ℂ) * mp a (1 - s) *
        ∫ h : Fˣ, (((μ₁⁻¹ * μ₂) h : ℂˣ) : ℂ) * g ((h : F) * a) *
          localFourier (selfDualMeasure ψ) ψ (fun y => f (-y)) (-((h⁻¹ : Fˣ) : F)) ∂multHaar F := by
    funext a
    have key : mp a (1 / 2) * mp a (1 / 2 - s) = mp a (1 - s) := by rw [mp_add]; congr 1; ring
    rw [hw a, hWd F ψ hψ μ₁ μ₂ h₁ h₂ g hg _ hf' a, ← key]
    have h2 : ((μ₂ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h1 : ((μ₁ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h3 : ((c a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hsc : ((μ₂ a : ℂˣ) : ℂ) * (((μ₁ a : ℂˣ) : ℂ) * ((μ₂ a : ℂˣ) : ℂ) * ((c a : ℂˣ) : ℂ))⁻¹ =
        (((μ₁ a : ℂˣ) : ℂ) * ((c a : ℂˣ) : ℂ))⁻¹ := by field_simp
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [← hsc]
    ring
  rw [hfun]
  exact ⟨hI, by rw [hE, character_inverse_identity_second]⟩

theorem pure (hDZ : SDZ) (hWd : SWd) (hTr : STrans) (hTate : STate) {ψ : AddChar F Circle} (hψ : IsStd ψ)
    {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) {f g : F → ℂ} (hf : f ∈ schwartzBruhat F)
    (hg : g ∈ schwartzBruhat F) {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Integrable (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
        mp a (1 / 2 - s)) (multHaar F) ∧
      Integrable (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2))
        (multHaar F) ∧
      ∫ a, W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
          mp a (1 / 2 - s) ∂multHaar F =
        gam ψ (μ₁ * c) s * gam ψ (μ₂ * c) s *
          ∫ a, W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F := by
  obtain ⟨hIL, hEL⟩ := lhs_pure hDZ hWd hTr hψ h₁ h₂ hf hg hc hs1
  obtain ⟨hIR, hER⟩ := rhs_pure hDZ hWd hψ h₁ h₂ hf hg hc hs0
  refine ⟨hIL, hIR, ?_⟩
  have hf' := comp_neg_mem hf
  have T2 := (hTate F ψ hψ (μ₂ * c) (isUnit1_mul h₂ hc) _ hf' s hs0 hs1).1
  have T1 := (hTate F ψ hψ (μ₁ * c) (isUnit1_mul h₁ hc) g hg s hs0 hs1).2
  rw [hEL, hER, localZeta_comp_neg (localFourier (selfDualMeasure ψ) ψ (fun y => f (-y))) (μ₂ * c)⁻¹ (1 - s),
    T2, localZeta_comp_neg f (μ₂ * c) s, T1,
    localZeta_comp_neg (localFourier (selfDualMeasure ψ) ψ g) (μ₁ * c) s]
  have hu : ((((μ₂ * c)⁻¹ (-1 : Fˣ)) : ℂˣ) : ℂ) * (((μ₂ * c) (-1 : Fˣ) : ℂˣ) : ℂ) = 1 := by
    rw [MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination (((μ₁ * c) (-1 : Fˣ) : ℂˣ) : ℂ) * gam ψ (μ₁ * c) s *
    localZeta (localFourier (selfDualMeasure ψ) ψ g) (μ₁ * c) s * gam ψ (μ₂ * c) s * localZeta f (μ₂ * c) s * hu

theorem sum_pure_tensors_whittaker (hLin : SLin) {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁)
    (h₂ : IsUnit1 μ₂) {n : ℕ} {f g : Fin n → F → ℂ} (hfg : ∀ i, f i ∈ schwartzBruhat F ∧ g i ∈ schwartzBruhat F)
    (t : Finset (Fin n)) :
    (∑ i ∈ t, pt (f i) (g i)) ∈ GodementSectionLocal.schwartzBruhat2 F ∧
      W2 ψ μ₁ μ₂ (∑ i ∈ t, pt (f i) (g i)) = ∑ i ∈ t, W2 ψ μ₁ μ₂ (pt (f i) (g i)) := by
  refine Finset.induction_on t ?_ ?_
  · refine ⟨by simpa using zero_mem _, ?_⟩
    have := (hLin F ψ hψ μ₁ μ₂ h₁ h₂ 0 (zero_mem _) 0 (zero_mem _)).2 0
    simpa using this
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨add_mem (pt_mem (hfg i).1 (hfg i).2) ih.1, ?_⟩
    rw [(hLin F ψ hψ μ₁ μ₂ h₁ h₂ _ (pt_mem (hfg i).1 (hfg i).2) _ ih.1).1, ih.2]

end Ad3.SchwartzSpaceL2.PFe

open Ad3.SchwartzSpaceL2.PFe in
theorem Ad3.SchwartzSpaceL2.pfe : Ad3.SchwartzSpaceL2.SFe := by
  intro hDZ hWd hPure hLin hTr hTate F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂ φ hφ c hc s hs0 hs1
  obtain ⟨n, f, g, hfg, rfl⟩ := hPure F φ hφ
  have hW := (sum_pure_tensors_whittaker hLin hψ h₁ h₂ hfg Finset.univ).2
  have hP := fun i => pure hDZ hWd hTr hTate hψ h₁ h₂ (hfg i).1 (hfg i).2 hc hs0 hs1
  have hL : (fun a : Fˣ => W2 ψ μ₁ μ₂ (∑ i, pt (f i) (g i)) (dg2 a 1 * w0) *
      (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) =
      fun a => ∑ i, W2 ψ μ₁ μ₂ (pt (f i) (g i)) (dg2 a 1 * w0) *
        (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) := by
    funext a
    rw [hW, Finset.sum_apply, Finset.sum_mul, Finset.sum_mul]
  have hR : (fun a : Fˣ => W2 ψ μ₁ μ₂ (∑ i, pt (f i) (g i)) (dg2 a 1) * ((c a : ℂˣ) : ℂ) *
      mp a (s - 1 / 2)) =
      fun a => ∑ i, W2 ψ μ₁ μ₂ (pt (f i) (g i)) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) := by
    funext a
    rw [hW, Finset.sum_apply, Finset.sum_mul, Finset.sum_mul]
  rw [hL, hR]
  refine ⟨integrable_finset_sum _ fun i _ => (hP i).1, integrable_finset_sum _ fun i _ => (hP i).2.1, ?_⟩
  rw [integral_finset_sum _ fun i _ => (hP i).1, integral_finset_sum _ fun i _ => (hP i).2.1,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (hP i).2.2
end
end

section
noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical AddMonoidAlgebra Matrix

namespace Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

theorem sum_Icc_telescope (f : ℤ → ℂ) (lo hi : ℤ) (h : lo ≤ hi + 1) :
    ∑ k ∈ Finset.Icc lo hi, (f k - f (k + 1)) = f lo - f (hi + 1) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  have e : ∀ i : ℕ, f (lo + (i : ℤ) + 1) = f (lo + ((i + 1 : ℕ) : ℤ)) := fun i => by
    push_cast; ring_nf
  simp_rw [e]
  rw [Finset.sum_range_sub' (fun i : ℕ => f (lo + (i : ℤ)))]
  simp only [Nat.cast_zero, add_zero]
  rw [Int.toNat_of_nonneg (by omega)]
  ring_nf

theorem evalAt_schur_two (w : Fin 2 → ℂˣ) (l : Fin 2 → ℤ) (hl : l 1 ≤ l 0) :
    evalAt w (schur l) =
      ∑ j ∈ Finset.Icc (-l 0) (-l 1), ((w 0 : ℂ)) ^ (-j) * ((w 1 : ℂ)) ^ (l 0 + l 1 + j) := by
  set P : LaurentRing 2 := ∑ j ∈ Finset.Icc (-l 0) (-l 1), monomial ![-j, l 0 + l 1 + j] with hP
  have hev : ∀ v : Fin 2 → ℂˣ, evalAt v P =
      ∑ j ∈ Finset.Icc (-l 0) (-l 1), ((v 0 : ℂ)) ^ (-j) * ((v 1 : ℂ)) ^ (l 0 + l 1 + j) := by
    intro v
    simp [hP, map_sum, evalAt_single, monomialChar_apply, Fin.prod_univ_two,
      Units.val_zpow_eq_zpow_val]
  have key : schur l = P := by
    refine mul_left_cancel₀ (alternant_staircase_ne_zero (n := 2)) ?_
    rw [alternant_mul_schur]
    refine eq_of_forall_evalAt fun v => ?_
    rw [map_mul, hev, alternant_eq_det, alternant_eq_det, AlgHom.map_det, AlgHom.map_det,
      det_fin_two, det_fin_two]
    simp [AlgHom.mapMatrix_apply, evalAt_single, monomialChar_apply, Fin.prod_univ_two, staircase,
      Units.val_zpow_eq_zpow_val, Pi.single_apply]
    set x : ℂ := (v 0 : ℂ)
    set y : ℂ := (v 1 : ℂ)
    have hx : x ≠ 0 := Units.ne_zero _
    have hy : y ≠ 0 := Units.ne_zero _
    set f : ℤ → ℂ := fun k => x ^ (1 - k) * y ^ (l 0 + l 1 + k) with hf
    have e : ∀ k : ℤ, (x - y) * ((x ^ k)⁻¹ * y ^ (l 0 + l 1 + k)) = f k - f (k + 1) := by
      intro k
      simp only [hf, zpow_add₀ hx, zpow_add₀ hy, zpow_sub₀ hx, zpow_one]
      field_simp
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => e k), sum_Icc_telescope f _ _ (by omega)]
    have e1 : (1:ℤ) - -l 0 = l 0 + 1 := by ring
    have e2 : l 0 + l 1 + -l 0 = l 1 := by ring
    have e3 : (1:ℤ) - (-l 1 + 1) = l 1 := by ring
    have e4 : l 0 + l 1 + (-l 1 + 1) = l 0 + 1 := by ring
    simp only [hf, e1, e2, e3, e4]
  rw [key, hev]

end Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2
end
end

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel NNReal

namespace Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem inner_eq (ψ : AddChar F Circle) (hψ : IsStd ψ) (y c : F) (hy : y ≠ 0) :
    ∫ x, (𝒪[F] : Set F).indicator (1 : F → ℂ) (y * (c + x)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ =
      (ψ c : ℂ) * (if ord y ≤ 0 then ((residueCard F : ℂ)) ^ (ord y) else 0) := by
  have h1 : ∫ x, (𝒪[F] : Set F).indicator (1 : F → ℂ) (y * (c + x)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ
      = ∫ x, (𝒪[F] : Set F).indicator (1 : F → ℂ) (y * x) * (ψ (-(x - c)) : ℂ) ∂selfDualMeasure ψ := by
    rw [← integral_add_left_eq_self
      (fun x => (𝒪[F] : Set F).indicator (1 : F → ℂ) (y * x) * (ψ (-(x - c)) : ℂ)) c]
    simp only [add_sub_cancel_left]
  rw [h1]
  have h2 : ∀ x, (𝒪[F] : Set F).indicator (1 : F → ℂ) (y * x) * (ψ (-(x - c)) : ℂ)
      = (ψ c : ℂ) * ((𝒪[F] : Set F).indicator (fun z => (ψ.mulShift (-y⁻¹) z : ℂ)) (y * x)) := by
    intro x
    by_cases hx : y * x ∈ (𝒪[F] : Set F)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, AddChar.mulShift_apply]
      have : -(x - c) = c + -y⁻¹ * (y * x) := by field_simp; ring
      rw [this, AddChar.map_add_eq_mul]
      simp
    · simp [Set.indicator_of_notMem hx]
  simp_rw [h2]
  rw [integral_const_mul, integral_comp_mul_left (selfDualMeasure ψ) hy
    (fun z => (𝒪[F] : Set F).indicator (fun z => (ψ.mulShift (-y⁻¹) z : ℂ)) z)]
  rw [integral_indicator (by rw [← coe_valBall_zero]; exact measurableSet_valBall 0),
    ← coe_valBall_zero, integral_valBall_char]
  have hcond : addCharConductor ψ = 0 := hψ.2.2
  have hy' : -y⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hy)
  have htriv : IsTrivialOn (ψ.mulShift (-y⁻¹)) 0 ↔ ord y ≤ 0 := by
    rw [isTrivialOn_mulShift_iff hy', isTrivialOn_iff hψ.1 hψ.2.1, hcond, ord_neg_eq, ord_inv hy]
    omega
  have hvol : (selfDualMeasure ψ).real (valBall F 0) = 1 := by
    rw [selfDualMeasure_real_valBall_zero, hcond]; simp
  rw [modulus_of_ne_zero hy]
  by_cases h : ord y ≤ 0
  · rw [if_pos (htriv.2 h), if_pos h, hvol]
    simp only [NNReal.coe_zpow, NNReal.coe_natCast, Complex.ofReal_one, smul_eq_mul]
    rw [Complex.real_smul]
    push_cast
    rw [_root_.zpow_neg, inv_inv]
    ring
  · rw [if_neg (fun h' => h (htriv.1 h')), if_neg h]
    simp

end Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2
end
end

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel NNReal

namespace Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

variable (F) in

abbrev phi0 : (Fin 2 → F) → ℂ := Set.indicator {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} 1

omit [MeasurableSpace F] [BorelSpace F] in
theorem characteristic_function_integral_apply (v : Fin 2 → F) :
    phi0 F v = (𝒪[F] : Set F).indicator 1 (v 0) * (𝒪[F] : Set F).indicator 1 (v 1) := by
  by_cases h0 : v 0 ∈ 𝒪[F] <;> by_cases h1 : v 1 ∈ 𝒪[F] <;>
    simp [phi0, Set.indicator_apply, Fin.forall_fin_two, h0, h1]

omit [MeasurableSpace F] [BorelSpace F] in
theorem characteristic_function_integral_invariant {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) (v : Fin 2 → F) :
    phi0 F (v ᵥ* (k : Matrix (Fin 2) (Fin 2) F)) = phi0 F v := by
  have hs : {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} = (GodementSectionLocal.box F 0 : Set (Fin 2 → F)) := by
    ext x
    simp [GodementSectionLocal.mem_box, mem_valBall_zero_iff]
  simp only [phi0]
  rw [hs]
  by_cases h : v ∈ GodementSectionLocal.box F 0
  · rw [Set.indicator_of_mem h,
      Set.indicator_of_mem ((GodementSectionLocal.vecMul_mem_box_iff hk 0 v).2 h)]
    rfl
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (mt (GodementSectionLocal.vecMul_mem_box_iff hk 0 v).1 h)]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem unip_entries {u : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2) :
    (u : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (u : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 ∧
      (u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  ⟨hu.2 0, hu.2 1, hu.1 (show id (0 : Fin 2) < id 1 by decide)⟩

omit [MeasurableSpace F] [BorelSpace F] in
theorem vec_eq {u k : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2)
    (hk : k ∈ GLnLocal.integralGL F 2) (l : Fin 2 → ℤ) (h x : F) :
    phi0 F (![h, h * x] ᵥ* ((u * Iwasawa.torusPow F 2 l * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      (𝒪[F] : Set F).indicator 1 (h * (GLnLocal.uniformizer F : F) ^ (l 0)) *
        (𝒪[F] : Set F).indicator 1 ((h * (GLnLocal.uniformizer F : F) ^ (l 1)) *
          ((u : Matrix (Fin 2) (Fin 2) F) 0 1 + x)) := by
  rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, characteristic_function_integral_invariant hk, ← vecMul_vecMul,
    Iwasawa.coe_torusPow, characteristic_function_integral_apply]
  obtain ⟨h00, h11, h10⟩ := unip_entries hu
  simp only [vecMul_diagonal]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h00, h11, h10]
  left
  congr 1
  ring

end Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2
end
end

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel NNReal

namespace Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem ord_unif_zpow (n : ℤ) : ord ((GLnLocal.uniformizer F : F) ^ n) = n := by
  rw [← Iwasawa.coe_uniformizerUnit, ← Units.val_zpow_eq_zpow_val, ord_units_zpow,
    Iwasawa.coe_uniformizerUnit, ord_uniformizer (GLnLocal.irreducible_uniformizer F), mul_one]

omit [MeasurableSpace F] [BorelSpace F] in
theorem unif_zpow_ne_zero (n : ℤ) : (GLnLocal.uniformizer F : F) ^ n ≠ 0 := by
  rw [← Iwasawa.coe_uniformizerUnit, ← Units.val_zpow_eq_zpow_val]
  exact Units.ne_zero _

omit [MeasurableSpace F] [BorelSpace F] in
theorem ord_det {u k : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2)
    (hk : k ∈ GLnLocal.integralGL F 2) (l : Fin 2 → ℤ) :
    ord ((GeneralLinearGroup.det (u * Iwasawa.torusPow F 2 l * k) : Fˣ) : F) = l 0 + l 1 := by
  obtain ⟨h00, h11, h10⟩ := unip_entries hu
  have hdu : GeneralLinearGroup.det u = 1 := by
    ext
    rw [GeneralLinearGroup.val_det_apply, det_fin_two, h00, h11, h10]
    simp
  have hdt : ((GeneralLinearGroup.det (Iwasawa.torusPow F 2 l) : Fˣ) : F) =
      (GLnLocal.uniformizer F : F) ^ (l 0) * (GLnLocal.uniformizer F : F) ^ (l 1) := by
    rw [GeneralLinearGroup.val_det_apply, Iwasawa.coe_torusPow, det_diagonal, Fin.prod_univ_two]
  rw [map_mul, map_mul, hdu, one_mul, Units.val_mul, hdt,
    ord_mul (mul_ne_zero (unif_zpow_ne_zero _) (unif_zpow_ne_zero _)) (Units.ne_zero _),
    ord_mul (unif_zpow_ne_zero _) (unif_zpow_ne_zero _), ord_unif_zpow, ord_unif_zpow,
    GodementSectionLocal.ord_det_eq_zero hk, add_zero]

omit [MeasurableSpace F] [BorelSpace F] in
theorem indicator_integers_eq {y : F} (hy : y ≠ 0) :
    (𝒪[F] : Set F).indicator (1 : F → ℂ) y = if 0 ≤ ord y then 1 else 0 := by
  have : y ∈ (𝒪[F] : Set F) ↔ 0 ≤ ord y := by
    rw [SetLike.mem_coe, ← mem_valBall_zero_iff, mem_valBall_iff_le_ord hy]
  by_cases h : 0 ≤ ord y
  · rw [Set.indicator_of_mem (this.2 h), if_pos h]; rfl
  · rw [Set.indicator_of_notMem (fun h' => h (this.1 h')), if_neg h]

theorem W_formula (ψ : AddChar F Circle) (hψ : IsStd ψ) (μ₁ μ₂ : Fˣ →* ℂˣ)
    (hr₁ : IsUnramifiedChar μ₁) (hr₂ : IsUnramifiedChar μ₂) {u k : GL (Fin 2) F}
    (hu : u ∈ Iwasawa.unipotent F 2) (hk : k ∈ GLnLocal.integralGL F 2) (l : Fin 2 → ℤ) :
    W2 ψ μ₁ μ₂ (phi0 F) (u * Iwasawa.torusPow F 2 l * k) =
      ((μ₂ (unifUnit F) : ℂˣ) : ℂ) ^ (l 0 + l 1) *
        ((((residueCard F : ℝ≥0) ^ (-(l 0 + l 1)) : ℝ≥0) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        ((ψ ((u : Matrix (Fin 2) (Fin 2) F) 0 1) : ℂ) * (residueCard F : ℂ) ^ (l 1) *
          ∑ j ∈ Finset.Icc (-l 0) (-l 1),
            ((((μ₁ (unifUnit F))⁻¹ * μ₂ (unifUnit F) : ℂˣ) : ℂ)) ^ j) := by
  have hdet := ord_det hu hk l
  set χ0 : ℂˣ := (μ₁ (unifUnit F))⁻¹ * μ₂ (unifUnit F) with hχ0
  set q : ℂ := (residueCard F : ℂ) with hq
  have hq0 : q ≠ 0 := residueCard_ne_zero_complex
  set C : ℂ := (ψ ((u : Matrix (Fin 2) (Fin 2) F) 0 1) : ℂ) * q ^ (l 1) with hC
  have hpt : ∀ h : Fˣ,
      (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
        (∫ x, phi0 F (![(h : F), h * x] ᵥ*
          ((u * Iwasawa.torusPow F 2 l * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
          (ψ (-x) : ℂ) ∂selfDualMeasure ψ) =
      ∑ j ∈ Finset.Icc (-l 0) (-l 1), (ordShell F j).indicator (fun _ => C * (χ0 : ℂ) ^ j) h := by
    classical
    intro h
    have hb0 : (h : F) * (GLnLocal.uniformizer F : F) ^ (l 1) ≠ 0 :=
      mul_ne_zero h.ne_zero (unif_zpow_ne_zero _)
    have ha0 : (h : F) * (GLnLocal.uniformizer F : F) ^ (l 0) ≠ 0 :=
      mul_ne_zero h.ne_zero (unif_zpow_ne_zero _)
    have hin : (∫ x, phi0 F (![(h : F), h * x] ᵥ*
          ((u * Iwasawa.torusPow F 2 l * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
          (ψ (-x) : ℂ) ∂selfDualMeasure ψ) =
        (𝒪[F] : Set F).indicator 1 ((h : F) * (GLnLocal.uniformizer F : F) ^ (l 0)) *
          ((ψ ((u : Matrix (Fin 2) (Fin 2) F) 0 1) : ℂ) * (if ord ((h : F) * (GLnLocal.uniformizer F : F) ^ (l 1)) ≤ 0 then
            q ^ (ord ((h : F) * (GLnLocal.uniformizer F : F) ^ (l 1))) else 0)) := by
      simp_rw [vec_eq hu hk l]
      rw [← inner_eq ψ hψ _ _ hb0, ← integral_const_mul]
      congr 1
      funext x
      ring
    rw [hin, indicator_integers_eq ha0, ord_mul h.ne_zero (unif_zpow_ne_zero _),
      ord_mul h.ne_zero (unif_zpow_ne_zero _), ord_unif_zpow, ord_unif_zpow]
    have hmu : (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) = (χ0 : ℂ) ^ ord (h : F) := by
      rw [quasiChar_apply_of_isUnramified hr₁ h, quasiChar_apply_of_isUnramified hr₂ h, hχ0,
        ← _root_.inv_zpow, ← mul_zpow, Units.val_zpow_eq_zpow_val]
    have hmp : mp h 1 = q ^ (-ord (h : F)) := by
      rw [mp, Complex.cpow_one, modulus_of_ne_zero h.ne_zero, hq]
      push_cast
      rfl
    rw [hmu, hmp]
    simp only [Set.indicator_apply, mem_ordShell]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_Icc]
    set o := ord (h : F)
    by_cases h1 : 0 ≤ o + l 0 <;> by_cases h2 : o + l 1 ≤ 0
    · rw [if_pos h1, if_pos h2, if_pos ⟨by omega, by omega⟩, hC, zpow_add₀ hq0, _root_.zpow_neg]
      field_simp
    · rw [if_neg h2, if_neg (show ¬(-l 0 ≤ o ∧ o ≤ -l 1) by omega)]; simp
    · rw [if_neg h1, if_neg (show ¬(-l 0 ≤ o ∧ o ≤ -l 1) by omega)]; simp
    · rw [if_neg h1, if_neg (show ¬(-l 0 ≤ o ∧ o ≤ -l 1) by omega)]; simp
  unfold W2
  rw [quasiChar_apply_of_isUnramified hr₂, hdet]
  congr 1
  · rw [mp, modulus_of_ne_zero (Units.ne_zero _), hdet, Units.val_zpow_eq_zpow_val]
  · refine (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans ?_
    have hint : ∀ j : ℤ, Integrable ((ordShell F j).indicator (fun _ : Fˣ => C * (χ0 : ℂ) ^ j))
        (multHaar F) := fun j =>
      (integrableOn_const (by rw [multHaar_ordShell]; exact ENNReal.one_ne_top)).integrable_indicator
        (measurableSet_ordShell j)
    rw [integral_finset_sum _ (fun j _ => hint j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_indicator_const _ (measurableSet_ordShell j), measureReal_def, multHaar_ordShell,
      ENNReal.toReal_one, one_smul]

end Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2
end
end

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel NNReal

namespace Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

theorem sqrt_half (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℤ) :
    ((((residueCard F : ℝ≥0) ^ (-n) : ℝ≥0) : ℝ) : ℂ) ^ (1 / 2 : ℂ) = Spherical.sqrtQ F ^ (-n) := by
  set s := NNReal.sqrt (residueCard F : ℝ≥0) with hs
  have hs2 : (residueCard F : ℝ≥0) = s ^ 2 := (NNReal.sq_sqrt _).symm
  have hpow : ((residueCard F : ℝ≥0)) ^ (-n) = (s ^ (-n)) ^ 2 := by
    rw [hs2, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]
  have key : ∀ r : ℝ, 0 ≤ r → ((r ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (r : ℂ) := by
    intro r hr
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_cpow (sq_nonneg r), ← Real.sqrt_eq_rpow, Real.sqrt_sq hr]
  rw [hpow, NNReal.coe_pow, key _ (NNReal.coe_nonneg _), NNReal.coe_zpow, Complex.ofReal_zpow]
  rfl

theorem alg (X Y S P : ℂ) (hX : X ≠ 0) (hY : Y ≠ 0) (hS : S ≠ 0) (a b j : ℤ) :
    Y ^ (a + b) * S ^ (-(a + b)) * (P * (S ^ 2) ^ b * (X⁻¹ * Y) ^ j) =
      P * S ^ (-(a - b)) * (X ^ (-j) * Y ^ (a + b + j)) := by
  have hS2 : (S ^ 2) ^ b = (S ^ b) ^ 2 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
  rw [mul_zpow, _root_.inv_zpow, hS2]
  simp only [zpow_add₀ hY, zpow_add₀ hS, _root_.zpow_neg, zpow_sub₀ hS]
  field_simp

end Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

namespace Ad3.SchwartzSpaceL2

theorem punr : SUnr := by
  intro F _ _ _ _ _ _ ψ hψ μ₁ μ₂ _ _ hr₁ hr₂
  funext g
  obtain ⟨⟨u, k⟩, hu, hk, hg⟩ := Spherical.exists_iwasawa_decomp g
  have hψ₀ : ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ) x = 1 := by
    intro x hx
    have := (isTrivialOn_iff hψ.1 hψ.2.1 0).2 (le_of_eq hψ.2.2) x (mem_valBall_zero_iff.2 hx)
    simp [this]
  rw [hg]
  generalize Iwasawa.iwasawaExponent F 2 g = l
  rw [Spherical.sphericalWhittaker_apply hψ₀ _ hu hk l]
  rw [UnramifiedWhittakerGL2.W_formula ψ hψ μ₁ μ₂ hr₁ hr₂ hu hk l, UnramifiedWhittakerGL2.sqrt_half]
  have hpsi : Whittaker.psiN (Circle.coeHom.compAddChar ψ) u =
      (ψ ((u : Matrix (Fin 2) (Fin 2) F) 0 1) : ℂ) := by
    simp [Whittaker.psiN, Whittaker.superdiagSum, Fin.sum_univ_two]
    rfl
  rw [hpsi]
  have hanti : Antitone l ↔ l 1 ≤ l 0 := by
    refine ⟨fun h => h (Fin.zero_le 1), fun h i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all
  by_cases hl : l 1 ≤ l 0
  · rw [if_pos (hanti.2 hl), UnramifiedWhittakerGL2.evalAt_schur_two _ l hl, Spherical.halfModulus_eq]
    have hrho : Spherical.rhoPair l = l 0 - l 1 := by
      simp [Spherical.rhoPair, Fin.sum_univ_two]
      ring
    have hq : (residueCard F : ℂ) = Spherical.sqrtQ F ^ 2 := (Spherical.sqrtQ_sq).symm
    rw [hrho, hq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Units.val_mul,
      Units.val_inv_eq_inv_val]
    exact UnramifiedWhittakerGL2.alg _ _ _ _ (Units.ne_zero _) (Units.ne_zero _) Spherical.sqrtQ_ne_zero _ _ _
  · rw [if_neg (mt hanti.1 hl), Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    simp

end Ad3.SchwartzSpaceL2
end
end

section
theorem Ad3.loc2 : Ad3.Loc2 :=
  Ad3.SchwartzSpaceL2.top' GlobalTheory.T.whittaker_additive_character_equivariance GlobalTheory.T.whittaker_central_character GlobalTheory.T.whittaker_right_translation GlobalTheory.T.whittaker_smoothness GlobalTheory.T.whittaker_gauge_bound GlobalTheory.T.whittaker_nonvanishing
    Ad3.SchwartzSpaceL2.punr GlobalTheory.T.whittaker_vanishing_at_zero GlobalTheory.T.whittaker_well_defined GlobalTheory.T.whittaker_pure_tensor_formula GlobalTheory.T.whittaker_linearity GlobalTheory.T.whittaker_local_tate_integral Ad3.SchwartzSpaceL2.pfe
end
