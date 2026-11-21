import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralRightTranslateInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCentralCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGaugeBound
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTemperedBoundDetOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhdEqPhk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierContinuousBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegrandEqIteratedIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIwasawaPullback
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLinearity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralDetSecondVectorFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralBoundedModulusPowerFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTranslateEntriesBounded

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2LocalData.GL2GodementVector

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in

theorem continuous_of_rightInv {W : GL (Fin 2) F → ℂ} (U : OpenSubgroup (GL (Fin 2) F))
    (h : ∀ g, ∀ u ∈ U, W (g * u) = W g) : Continuous W := by
  refine IsLocallyConstant.continuous (IsLocallyConstant.iff_exists_open _ |>.2 fun g => ?_)
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (U : Set (GL (Fin 2) F)),
    U.isOpen.preimage (continuous_const.mul continuous_id), by simp, fun x hx => ?_⟩
  have := h g _ hx
  simpa using this

def Good (ψ : AddChar F Circle) (W₀ : GL (Fin 2) F → ℂ) : Prop :=
  (∀ x g, W₀ (uni2 x * g) = (ψ x : ℂ) * W₀ g) ∧ (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = W₀ g) ∧
  (∃ U : OpenSubgroup (GL (Fin 2) F), ∀ g, ∀ u ∈ U, W₀ (g * u) = W₀ g) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, 0 ≤ C ∧ ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖W₀ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧
      (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)

omit [MeasurableSpace F] [BorelSpace F] in
theorem good_zero (ψ : AddChar F Circle) : Good ψ (0 : GL (Fin 2) F → ℂ) := by
  refine ⟨fun x g => by simp, fun a g => by simp, ⟨⊤, fun g u _ => by simp⟩,
    fun ε _ => ⟨0, 0, le_rfl, fun a k _ => ⟨by simp, fun h => absurd rfl h⟩⟩⟩

omit [MeasurableSpace F] [BorelSpace F] in
theorem good_add {ψ : AddChar F Circle} {W W' : GL (Fin 2) F → ℂ} (h : Good ψ W) (h' : Good ψ W') :
    Good ψ (W + W') := by
  obtain ⟨h1, h2, ⟨U, h3⟩, h4⟩ := h
  obtain ⟨h1', h2', ⟨U', h3'⟩, h4'⟩ := h'
  refine ⟨fun x g => by simp [h1, h1', mul_add], fun a g => by simp [h2, h2'],
    ⟨U ⊓ U', fun g u hu => ?_⟩, fun ε hε => ?_⟩
  · have hu' : u ∈ U ∧ u ∈ U' := by simpa using hu
    simp [h3 g u hu'.1, h3' g u hu'.2]
  · obtain ⟨C, B, hC, hb⟩ := h4 ε hε
    obtain ⟨C', B', hC', hb'⟩ := h4' ε hε
    refine ⟨C + C', max B B', add_nonneg hC hC', fun a k hk => ⟨?_, fun hne => ?_⟩⟩
    · rw [add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hb a k hk).1 (hb' a k hk).1)
    · by_cases h0 : W (dg2 a 1 * k) = 0
      · have h0' : W' (dg2 a 1 * k) ≠ 0 := fun e => hne (by simp [h0, e])
        exact ((hb' a k hk).2 h0').trans (le_max_right _ _)
      · exact ((hb a k hk).2 h0).trans (le_max_left _ _)

omit [MeasurableSpace F] [BorelSpace F] in
theorem good_smul {ψ : AddChar F Circle} {W : GL (Fin 2) F → ℂ} (c : ℂ) (h : Good ψ W) :
    Good ψ (c • W) := by
  obtain ⟨h1, h2, ⟨U, h3⟩, h4⟩ := h
  refine ⟨fun x g => by simp [h1]; ring, fun a g => by simp [h2],
    ⟨U, fun g u hu => by simp [h3 g u hu]⟩, fun ε hε => ?_⟩
  obtain ⟨C, B, hC, hb⟩ := h4 ε hε
  refine ⟨‖c‖ * C, B, mul_nonneg (norm_nonneg _) hC, fun a k hk => ⟨?_, fun hne => ?_⟩⟩
  · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb a k hk).1 (norm_nonneg _)
  · exact (hb a k hk).2 fun e => hne (by simp [e])

theorem godement_whittaker_vector_good {ψ : AddChar F Circle} (hψ : IsStd ψ) {ν : Fˣ →* ℂˣ} (hν : IsUnit1 ν)
    {φ : (Fin 2 → F) → ℂ} (hφ : φ ∈ GodementSectionLocal.schwartzBruhat2 F) :
    Good ψ (W2 ψ ν ν⁻¹ φ) := by
  have hν' : IsUnit1 ν⁻¹ := ⟨hν.1.inv, fun x => by simp [hν.2 x]⟩
  refine ⟨fun x g => GlobalTheory.CompanionTheory.WhittakerPsi.sPsi F ψ hψ ν ν⁻¹ hν hν' φ hφ x g, fun a g => ?_,
    GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth F ψ hψ ν ν⁻¹ hν hν' φ hφ, fun ε hε => ?_⟩
  · rw [GlobalTheory.CompanionTheory.WhittakerCentral.sCen F ψ hψ ν ν⁻¹ hν hν' φ hφ a g]
    simp
  · obtain ⟨C, B, hb⟩ := GlobalTheory.CompanionTheory.DampedWhittakerGauge.whittaker_torus_gauge_estimate F ψ hψ ν ν⁻¹ hν hν' φ hφ ε hε
    refine ⟨max C 0, B, le_max_right _ _, fun a k hk => ⟨?_, (hb a k hk).2⟩⟩
    exact (hb a k hk).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (NNReal.coe_nonneg _) _))

theorem good_of_mem {ψ : AddChar F Circle} (hψ : IsStd ψ) {ν : Fˣ →* ℂˣ} (hν : IsUnit1 ν)
    {W₀ : GL (Fin 2) F → ℂ} (hW : W₀ ∈ V2 ψ ν ν⁻¹) : Good ψ W₀ := by
  refine Submodule.span_induction ?_ (good_zero ψ) (fun _ _ _ _ h h' => good_add h h')
    (fun c _ _ h => good_smul c h) hW
  rintro _ ⟨φ, hφ, rfl⟩
  exact godement_whittaker_vector_good hψ hν hφ

theorem godement_vector_growth_support : ForS fun F _ _ _ _ _ _ ψ => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹,
    (∀ x g, W₀ (uni2 x * g) = (ψ x : ℂ) * W₀ g) ∧ (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = W₀ g) ∧ Continuous W₀ ∧
    ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, 0 ≤ C ∧ ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
      ‖W₀ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧ (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B) := by
  intro F _ _ _ _ _ _ ψ hψ ν hν W₀ hW
  obtain ⟨h1, h2, ⟨U, h3⟩, h4⟩ := good_of_mem hψ hν hW
  exact ⟨h1, h2, continuous_of_rightInv U h3, h4⟩

end GlobalTheory.CompanionTheory.GL2LocalData.GL2GodementVector
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.godement_vector_decay_bound : ForS fun F _ _ _ _ _ _ ψ => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹,
  (∀ x g, W₀ (uni2 x * g) = (ψ x : ℂ) * W₀ g) ∧ (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = W₀ g) ∧ Continuous W₀ ∧
  ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, 0 ≤ C ∧ ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖W₀ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧ (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2LocalData.GL2GodementVector.godement_vector_growth_support
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GJMeas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem continuous_detUnit : Continuous (GeneralLinearGroup.det : GL (Fin 2) F → Fˣ) := by
  rw [Units.continuous_iff]
  constructor
  · exact Continuous.matrix_det Units.continuous_val
  · have : Continuous fun g : GL (Fin 2) F => ((g⁻¹ : GL (Fin 2) F).val).det :=
      Continuous.matrix_det (Units.continuous_val.comp continuous_inv)
    convert this using 2 with g
    rw [← map_inv]
    rfl

theorem continuous_of_rightInvariant (W : GL (Fin 2) F → ℂ) (U : OpenSubgroup (GL (Fin 2) F))
    (h : ∀ g, ∀ u ∈ U, W (g * u) = W g) : Continuous W := by
  rw [continuous_iff_continuousAt]
  intro g
  have hopen : IsOpen ((fun x : GL (Fin 2) F => g⁻¹ * x) ⁻¹' (U : Set (GL (Fin 2) F))) :=
    U.isOpen.preimage (continuous_const.mul continuous_id)
  have hmem : ((fun x : GL (Fin 2) F => g⁻¹ * x) ⁻¹' (U : Set (GL (Fin 2) F))) ∈ nhds g :=
    hopen.mem_nhds (by simpa using U.one_mem)
  have hev : (fun _ : GL (Fin 2) F => W g) =ᶠ[nhds g] W := by
    filter_upwards [hmem] with x hx
    have := h g (g⁻¹ * x) hx
    simpa using this.symm
  exact (continuousAt_const).congr hev

theorem continuous_mp_det (z : ℂ) :
    Continuous fun g : GL (Fin 2) F => mp (GeneralLinearGroup.det g) z := by
  have h1 : Continuous fun g : GL (Fin 2) F =>
      ((modulus (((GeneralLinearGroup.det g : Fˣ)) : F) : ℝ) : ℂ) := by
    have h2 : Continuous fun g : GL (Fin 2) F => modulus (((GeneralLinearGroup.det g : Fˣ)) : F) :=
      continuous_modulus.comp (Units.continuous_val.comp continuous_detUnit)
    exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp h2)
  refine h1.cpow continuous_const fun g => ?_
  refine Complex.ofReal_mem_slitPlane.2 ?_
  exact_mod_cast modulus_pos (Units.ne_zero _)




end GlobalTheory.CompanionTheory.GJMeas
end
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhIwasawa

theorem continuous_and_iwasawa_bound : ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', Continuous W ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : GL (Fin 2) F,
  ‖W h‖ ≤ C * ((modulus (h.val).det : ℝ) / mx (e2r h) ^ 2) ^ (1 / 2 - ε) := by
  intro F _ _ _ _ _ _ ψ hψ ω G V' hω H W hW
  refine ⟨?_, fun ε hε => ?_⟩
  · obtain ⟨U, hU⟩ := H.smooth W hW
    exact GlobalTheory.CompanionTheory.GJMeas.continuous_of_rightInvariant W U hU
  · obtain ⟨C, B, hC, hCB⟩ := GlobalTheory.CompanionTheory.GJTwo.WhB.whittaker_bound_det_one F ψ hψ ω G V' hω H W hW ε hε
    refine ⟨C, hC, fun h => ?_⟩
    have hy : ((GeneralLinearGroup.det h : Fˣ) : F) = (h.val).det := rfl
    have hy0 : (h.val).det ≠ 0 := by
      rw [← hy]
      exact Units.ne_zero _
    have hg : ((dg2 (GeneralLinearGroup.det h)⁻¹ 1 * h : GL (Fin 2) F).val).det = 1 := by
      have hd : ((dg2 (GeneralLinearGroup.det h)⁻¹ 1 : GL (Fin 2) F).val).det = ((h.val).det)⁻¹ := by
        simp [dg2, Matrix.det_fin_two, hy]
      rw [Units.val_mul, Matrix.det_mul, hd, inv_mul_cancel₀ hy0]
    have hrow : (fun j => (dg2 (GeneralLinearGroup.det h)⁻¹ 1 * h : GL (Fin 2) F).val 1 j) = e2r h := by
      funext j
      fin_cases j <;> simp [dg2, e2r, Matrix.mul_apply, Fin.sum_univ_two]
    have hyg : dg2 (GeneralLinearGroup.det h) 1 * (dg2 (GeneralLinearGroup.det h)⁻¹ 1 * h) = h := by
      rw [← mul_assoc]
      have : (dg2 (GeneralLinearGroup.det h) 1 * dg2 (GeneralLinearGroup.det h)⁻¹ 1 : GL (Fin 2) F) = 1 := by
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, hy, hy0]
      rw [this, one_mul]
    have key := (hCB (GeneralLinearGroup.det h) _ hg).1
    rw [hyg, hrow, hy] at key
    exact key

end GlobalTheory.CompanionTheory.WhIwasawa
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_vector_gauge_bound : ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', Continuous W ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : GL (Fin 2) F,
  ‖W h‖ ≤ C * ((modulus (h.val).det : ℝ) / mx (e2r h) ^ 2) ^ (1 / 2 - ε) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WhIwasawa.continuous_and_iwasawa_bound
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Unfolding.PtB

section L

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in

theorem norm_mp_eq (a : Fˣ) (z : ℂ) : ‖mp a z‖ = (modulus (a : F) : ℝ) ^ z.re := by
  have h0 : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  rw [mp]
  exact Complex.norm_cpow_eq_rpow_re_of_pos h0 z

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

theorem diag_torus_factor_scalar (a b : Fˣ) : (dg2 (a * b) b : GL (Fin 2) F) = dg2 b b * dg2 a 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

theorem hI_central (p : Fˣ × Fˣ × GL (Fin 2) F) : hI p = dg2 p.2.1 p.2.1 * (dg2 p.1 1 * p.2.2) := by
  rw [hI, diag_torus_factor_scalar, mul_assoc]

omit [MeasurableSpace F] [BorelSpace F] in

theorem sup_norm_second_vector_diag_mul (c b : Fˣ) (x : GL (Fin 2) F) :
    mx (e2r (dg2 c b * x)) = (modulus (b : F) : ℝ) * mx (e2r x) := by
  have e0 : (dg2 c b * x).val 1 0 = (b : F) * x.val 1 0 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e1 : (dg2 c b * x).val 1 1 = (b : F) * x.val 1 1 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have hb : (0 : ℝ) ≤ (modulus (b : F) : ℝ) := NNReal.coe_nonneg _
  simp only [mx, e2r, Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1, modulus_mul, NNReal.coe_mul]
  exact (mul_max_of_nonneg _ _ hb).symm

theorem sup_norm_second_vector_maxCompact {k : GL (Fin 2) F} (hk : k ∈ K2 F) : mx (e2r k) = 1 := by
  have := GlobalTheory.CompanionTheory.GJTwo.WhB.mx_bottom_integral hk
  simpa [mx, e2r] using this

theorem modulus_det_hI_mul (p : Fˣ × Fˣ × GL (Fin 2) F) (hp : p.2.2 ∈ K2 F) (g : GL (Fin 2) F) :
    (modulus ((hI p * g).val).det : ℝ) =
      (modulus (p.1 : F) : ℝ) * (modulus (p.2.1 : F) : ℝ) ^ 2 * (modulus (g.val).det : ℝ) := by
  have hk : modulus ((p.2.2).val).det = 1 := GlobalTheory.CompanionTheory.GJTwo.WhB.modulus_det_integral hp
  have hd : ((dg2 (p.1 * p.2.1) p.2.1 : GL (Fin 2) F).val).det = (p.1 : F) * p.2.1 * p.2.1 := by
    simp [dg2, Matrix.det_fin_two]
  rw [hI, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hd, modulus_mul, modulus_mul,
    modulus_mul, modulus_mul, hk]
  push_cast
  ring

end L

theorem main : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ) (C₀ C₁ C₂ B R ε : ℝ),
  0 ≤ C₀ → 0 ≤ C₁ → 0 ≤ C₂ → 0 < ε → ε < 1 / 2 →
  (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = W₀ g) →
  (∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, ‖W₀ (dg2 a 1 * k)‖ ≤ C₀ * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧
    (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)) →
  (∀ h : GL (Fin 2) F, ‖W' h‖ ≤ C₁ * ((modulus (h.val).det : ℝ) / mx (e2r h) ^ 2) ^ (1 / 2 - ε)) →
  (∀ A ξ, ‖pFT ψ Φ A ξ‖ ≤ C₂ ∧ (pFT ψ Φ A ξ ≠ 0 → (∀ i j, (modulus (A i j) : ℝ) ≤ R) ∧ mx ξ ≤ R)) →
  ∀ (g : GL (Fin 2) F) (p : Fˣ × Fˣ × GL (Fin 2) F), p.2.2 ∈ K2 F →
    ‖Bq ψ W₀ W' Φ s g (hI p)‖ ≤ C₀ * C₁ * C₂ * Mj R B s.re ε g p := by
  intro F _ _ _ _ _ _ ψ _ W₀ W' Φ s C₀ C₁ C₂ B R ε h0 h1 h2 hε hε2 hcen hW₀ hW' hP g p hk
  have hW0eq : W₀ (hI p) = W₀ (dg2 p.1 1 * p.2.2) := by rw [hI_central, hcen]
  have hmx : mx (e2r (hI p)) = (modulus (p.2.1 : F) : ℝ) := by
    rw [hI, sup_norm_second_vector_diag_mul, sup_norm_second_vector_maxCompact hk, mul_one]
  have hA : (0 : ℝ) < (modulus (p.1 : F) : ℝ) := by exact_mod_cast modulus_pos p.1.ne_zero
  have hB : (0 : ℝ) < (modulus (p.2.1 : F) : ℝ) := by exact_mod_cast modulus_pos p.2.1.ne_zero
  by_cases hc : (∀ i j, (modulus (g.val i j) : ℝ) ≤ R) ∧ (modulus (p.2.1 : F) : ℝ) ≤ R ∧
      (modulus (p.1 : F) : ℝ) ≤ B
  · rw [Mj, if_pos hc]
    set A : ℝ := (modulus (p.1 : F) : ℝ) with hAdef
    set b : ℝ := (modulus (p.2.1 : F) : ℝ) with hbdef
    set Q : ℝ := (modulus (g.val).det : ℝ) / mx (e2r (p.2.2 * g)) ^ 2 with hQdef
    have hQ : 0 ≤ Q := by
      have hm : 0 ≤ mx (e2r (p.2.2 * g)) := le_max_of_le_left (NNReal.coe_nonneg _)
      exact div_nonneg (NNReal.coe_nonneg _) (by positivity)
    have e1 : ‖W₀ (hI p)‖ ≤ C₀ * A ^ (1 / 2 - ε) := by
      rw [hW0eq]; exact (hW₀ p.1 p.2.2 hk).1
    have hq : (modulus ((hI p * g).val).det : ℝ) / mx (e2r (hI p * g)) ^ 2 = A * Q := by
      have hrow : mx (e2r (hI p * g)) = b * mx (e2r (p.2.2 * g)) := by
        rw [hI, mul_assoc, sup_norm_second_vector_diag_mul]
      rw [modulus_det_hI_mul p hk, hrow, hQdef, mul_pow, ← hAdef, ← hbdef,
        show A * b ^ 2 * (modulus (g.val).det : ℝ) = b ^ 2 * (A * (modulus (g.val).det : ℝ)) by ring,
        mul_div_mul_left _ _ (pow_ne_zero 2 hB.ne'), mul_div_assoc]
    have e2 : ‖W' (hI p * g)‖ ≤ C₁ * (A * Q) ^ (1 / 2 - ε) := by
      have := hW' (hI p * g)
      rwa [hq] at this
    have e3 : ‖pFT ψ Φ g.val (e2r (hI p))‖ ≤ C₂ := (hP _ _).1
    have e4 : ‖mp (GeneralLinearGroup.det (hI p)) s‖ = A ^ s.re * b ^ (2 * s.re) := by
      have h2s : (2 * s).re = 2 * s.re := by simp
      rw [GlobalTheory.CompanionTheory.DampedZetaMajorant.Iter.mp_det_hI p hk, norm_mul, norm_mp_eq, norm_mp_eq, h2s]
    have hexp : A ^ (s.re + 1 - 2 * ε) = A ^ (1 / 2 - ε) * A ^ (1 / 2 - ε) * A ^ s.re := by
      rw [← Real.rpow_add hA, ← Real.rpow_add hA]
      congr 1; ring
    have hsplit : (A * Q) ^ (1 / 2 - ε) = A ^ (1 / 2 - ε) * Q ^ (1 / 2 - ε) :=
      Real.mul_rpow hA.le hQ
    have n1 : 0 ≤ A ^ (1 / 2 - ε) := Real.rpow_nonneg hA.le _
    have n2 : 0 ≤ (A * Q) ^ (1 / 2 - ε) := Real.rpow_nonneg (mul_nonneg hA.le hQ) _
    calc ‖Bq ψ W₀ W' Φ s g (hI p)‖
        = ‖W₀ (hI p)‖ * ‖W' (hI p * g)‖ * ‖pFT ψ Φ g.val (e2r (hI p))‖ *
            ‖mp (GeneralLinearGroup.det (hI p)) s‖ := by simp only [Bq, norm_mul]
      _ ≤ (C₀ * A ^ (1 / 2 - ε)) * (C₁ * (A * Q) ^ (1 / 2 - ε)) * C₂ * (A ^ s.re * b ^ (2 * s.re)) := by
          rw [e4]
          have n3 : 0 ≤ A ^ s.re * b ^ (2 * s.re) :=
            mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _)
          gcongr
      _ = C₀ * C₁ * C₂ * (A ^ (s.re + 1 - 2 * ε) * b ^ (2 * s.re) * Q ^ (1 / 2 - ε)) := by
          rw [hexp, hsplit]; ring
  · rw [Mj, if_neg hc, mul_zero]
    have hz : Bq ψ W₀ W' Φ s g (hI p) = 0 := by
      by_contra hne
      have hw : W₀ (hI p) ≠ 0 := fun e => hne (by simp [Bq, e])
      have hf : pFT ψ Φ g.val (e2r (hI p)) ≠ 0 := fun e => hne (by simp [Bq, e])
      obtain ⟨r1, r2⟩ := (hP _ _).2 hf
      rw [hmx] at r2
      rw [hW0eq] at hw
      exact hc ⟨r1, r2, (hW₀ p.1 p.2.2 hk).2 hw⟩
    rw [hz, norm_zero]

end GlobalTheory.CompanionTheory.GL2Unfolding.PtB
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.outer_zeta_integrand_bound : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ) (C₀ C₁ C₂ B R ε : ℝ),
  0 ≤ C₀ → 0 ≤ C₁ → 0 ≤ C₂ → 0 < ε → ε < 1 / 2 →
  (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = W₀ g) →
  (∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, ‖W₀ (dg2 a 1 * k)‖ ≤ C₀ * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧
    (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)) →
  (∀ h : GL (Fin 2) F, ‖W' h‖ ≤ C₁ * ((modulus (h.val).det : ℝ) / mx (e2r h) ^ 2) ^ (1 / 2 - ε)) →
  (∀ A ξ, ‖pFT ψ Φ A ξ‖ ≤ C₂ ∧ (pFT ψ Φ A ξ ≠ 0 → (∀ i j, (modulus (A i j) : ℝ) ≤ R) ∧ mx ξ ≤ R)) →
  ∀ (g : GL (Fin 2) F) (p : Fˣ × Fˣ × GL (Fin 2) F), p.2.2 ∈ K2 F →
    ‖Bq ψ W₀ W' Φ s g (hI p)‖ ≤ C₀ * C₁ * C₂ * Mj R B s.re ε g p := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Unfolding.PtB.main
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.DampedWhittakerLimit

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_mp (s : ℂ) : Continuous fun h : Fˣ => mp h s := by
  have hc : Continuous fun h : Fˣ => (((modulus (h : F) : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))
  simp only [mp]
  refine hc.cpow continuous_const fun h => ?_
  have h0 : (0 : ℝ) < (modulus (h : F) : ℝ) := by exact_mod_cast modulus_pos h.ne_zero
  exact Complex.ofReal_mem_slitPlane.2 h0



end

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]


end GlobalTheory.CompanionTheory.DampedWhittakerLimit
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Unfolding.AqCont

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem cont_det : Continuous (fun h : GL (Fin 2) F => (GeneralLinearGroup.det h : Fˣ)) := by
  have hd : Continuous (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) F →* F) := by
    show Continuous fun A : Matrix (Fin 2) (Fin 2) F => A.det
    exact continuous_id.matrix_det
  exact Continuous.units_map _ hd

theorem continuous_second_vector_GL2 : Continuous (e2r : GL (Fin 2) F → Fin 2 → F) := by
  refine continuous_pi fun i => ?_
  have hv : Continuous fun h : GL (Fin 2) F => (h.val : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have he : ∀ a b : Fin 2, Continuous fun h : GL (Fin 2) F => h.val a b := fun a b =>
    (continuous_apply_apply a b).comp hv
  fin_cases i
  · simpa [e2r] using he 1 0
  · simpa [e2r] using he 1 1

theorem cont_wR : Continuous (wR : Fˣ × Fˣ × GL (Fin 2) F → ℝ) := by
  have hc : Continuous fun p : Fˣ × Fˣ × GL (Fin 2) F => (modulus (p.1 : F) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_modulus.comp (Units.continuous_val.comp continuous_fst))
  refine hc.inv₀ fun p => ?_
  have h0 : (0 : ℝ) < (modulus (p.1 : F) : ℝ) := by exact_mod_cast modulus_pos p.1.ne_zero
  exact h0.ne'

theorem continuous_Aq : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ),
  Continuous W₀ → Continuous W' → Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2) →
  Continuous (Aq ψ W₀ W' Φ s) := by
  intro F _ _ _ _ _ _ ψ _ W₀ W' Φ s hW₀ hW' hP
  have hg : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F => q.2 := continuous_snd
  have hh : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F => hI q.1 * q.2⁻¹ :=
    (GlobalTheory.CompanionTheory.BochIw.cont_hI.comp continuous_fst).mul continuous_snd.inv
  have hhg : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F =>
      hI q.1 * q.2⁻¹ * q.2 := hh.mul hg
  have hm1 : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F =>
      mp (GeneralLinearGroup.det q.2) (s + 1 / 2) :=
    (GlobalTheory.CompanionTheory.DampedWhittakerLimit.continuous_mp (s + 1 / 2)).comp (cont_det.comp hg)
  have hm2 : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F =>
      mp (GeneralLinearGroup.det (hI q.1 * q.2⁻¹)) s :=
    (GlobalTheory.CompanionTheory.DampedWhittakerLimit.continuous_mp s).comp (cont_det.comp hh)
  have hw : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F =>
      ((GlobalTheory.CompanionTheory.DampedZetaMajorant.wR q.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (cont_wR.comp continuous_fst)
  have hp : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F =>
      pFT ψ Φ q.2.val (e2r (hI q.1 * q.2⁻¹)) :=
    hP.comp ((Units.continuous_val.comp hg).prodMk (continuous_second_vector_GL2.comp hh))
  unfold Aq Bq
  exact hm1.mul (hw.mul ((((hW₀.comp hh).mul (hW'.comp hhg)).mul hp).mul hm2))

end D

end GlobalTheory.CompanionTheory.GL2Unfolding.AqCont
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_outer_zeta_integrand : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ),
  Continuous W₀ → Continuous W' → Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2) →
  Continuous (Aq ψ W₀ W' Φ s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Unfolding.AqCont.continuous_Aq
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Unfolding.Ptw

theorem main : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ), Φ ∈ LFS.SB F →
  ∀ p : Fˣ × Fˣ × GL (Fin 2) F, p.2.2 ∈ K2 F →
    iw (LFS.Wp ψ W₀ Φ) W' s p = ∫ g, Aq ψ W₀ W' Φ s (p, g) ∂LFS.hG ψ := by
  intro F _ _ _ _ _ _ ψ hψ W₀ W' Φ s hΦ p hp
  have hW := GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.main F ψ hψ W₀ Φ hΦ (hI p)
  have hw : ((wR p : ℝ) : ℂ) = mp p.1 (-1) := by
    rw [wR, mp, Complex.cpow_neg_one]
    push_cast
    rfl
  have hpt : ∀ g : GL (Fin 2) F, Aq ψ W₀ W' Φ s (p, g) =
      (((wR p : ℝ) : ℂ) * mp (GeneralLinearGroup.det (hI p)) s * W' (hI p)) *
        (pFT ψ Φ g.val (e2r (hI p * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) * W₀ (hI p * g⁻¹)) := by
    intro g
    have e1 : hI p * g⁻¹ * g = hI p := by group
    have e2 : mp (GeneralLinearGroup.det (hI p * g⁻¹)) s =
        mp (GeneralLinearGroup.det (hI p)) s * mp (GeneralLinearGroup.det g) (-s) := by
      rw [map_mul, map_inv, Iter.mp_mul, Iter.mp_inv]
    have e3 : mp (GeneralLinearGroup.det g) (s + 1 / 2) * mp (GeneralLinearGroup.det g) (-s) =
        mp (GeneralLinearGroup.det g) (1 / 2) := by
      rw [← Iter.mp_add]
      congr 1
      ring
    simp only [Aq, Bq]
    rw [e1, e2]
    linear_combination (((wR p : ℝ) : ℂ) * mp (GeneralLinearGroup.det (hI p)) s * W' (hI p) *
      pFT ψ Φ g.val (e2r (hI p * g⁻¹)) * W₀ (hI p * g⁻¹)) * e3
  have hc : mp (GeneralLinearGroup.det (hI p)) (1 / 2) * mp p.1 (s - 3 / 2) * mp p.2.1 (2 * s - 1) =
      mp p.1 (-1) * mp (GeneralLinearGroup.det (hI p)) s := by
    have ea : mp p.1 (1 / 2) * mp p.1 (s - 3 / 2) = mp p.1 (-1) * mp p.1 s := by
      rw [← Iter.mp_add, ← Iter.mp_add]
      congr 1
      ring
    have eb : mp p.2.1 (2 * (1 / 2)) * mp p.2.1 (2 * s - 1) = mp p.2.1 (2 * s) := by
      rw [← Iter.mp_add]
      congr 1
      ring
    rw [Iter.mp_det_hI p hp, Iter.mp_det_hI p hp]
    linear_combination (mp p.2.1 (2 * (1 / 2)) * mp p.2.1 (2 * s - 1)) * ea +
      (mp p.1 (-1) * mp p.1 s) * eb
  have hiw : iw (LFS.Wp ψ W₀ Φ) W' s p =
      LFS.Wp ψ W₀ Φ (em (hI p)) * W' (hI p) * mp p.1 (s - 3 / 2) * mp p.2.1 (2 * s - 1) := rfl
  simp only [hpt]
  rw [integral_const_mul, hiw, hW, hw]
  linear_combination ((∫ g, pFT ψ Φ g.val (e2r (hI p * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) *
    W₀ (hI p * g⁻¹) ∂LFS.hG ψ) * W' (hI p)) * hc

end GlobalTheory.CompanionTheory.GL2Unfolding.Ptw
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_integral_eq_group_integral : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ), Φ ∈ LFS.SB F →
  ∀ p : Fˣ × Fˣ × GL (Fin 2) F, p.2.2 ∈ K2 F →
    iw (LFS.Wp ψ W₀ Φ) W' s p = ∫ g, Aq ψ W₀ W' Φ s (p, g) ∂LFS.hG ψ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Unfolding.Ptw.main
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RInvB

theorem integral_right_invariant : ForS fun F _ _ _ _ _ _ ψ => ∀ B : GL (Fin 2) F → ℂ, Continuous B →
    (∀ x h, B (uni2 x * h) = B h) →
    ∀ g : GL (Fin 2) F, ∫ p, ((wR p : ℝ) : ℂ) * B (hI p * g) ∂mIw ψ =
      ∫ p, ((wR p : ℝ) : ℂ) * B (hI p) ∂mIw ψ := by
  intro F _ _ _ _ _ _ ψ hψ B hB hN g
  have hl := GlobalTheory.T.iwasawa_integral_right_translate_invariant F ψ hψ
  have hd : Measurable fun p : Fˣ × Fˣ × GL (Fin 2) F => ENNReal.ofReal (wR p) :=
    GlobalTheory.CompanionTheory.BochIw.measurable_wR'.ennreal_ofReal
  have hlt : ∀ᵐ p ∂mIw ψ, ENNReal.ofReal (wR p) < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hT1 : Measurable fun p : Fˣ × Fˣ × GL (Fin 2) F => B (hI p) :=
    (hB.comp GlobalTheory.CompanionTheory.BochIw.cont_hI).measurable
  have hTg : Measurable fun p : Fˣ × Fˣ × GL (Fin 2) F => B (hI p * g) :=
    (hB.comp (GlobalTheory.CompanionTheory.BochIw.cont_hI.mul continuous_const)).measurable
  have hmap : Measure.map (fun p => B (hI p * g))
        ((mIw ψ).withDensity fun p => ENNReal.ofReal (wR p)) =
      Measure.map (fun p => B (hI p)) ((mIw ψ).withDensity fun p => ENNReal.ofReal (wR p)) := by
    ext S hS
    have hind : ∀ (T : Fˣ × Fˣ × GL (Fin 2) F → ℂ) (p : Fˣ × Fˣ × GL (Fin 2) F),
        (T ⁻¹' S).indicator (fun p => ENNReal.ofReal (wR p)) p =
          ENNReal.ofReal (wR p) * S.indicator (1 : ℂ → ENNReal) (T p) := fun T p => by
      by_cases hp : T p ∈ S
      · have hp' : p ∈ T ⁻¹' S := hp
        simp [Set.indicator_of_mem hp', Set.indicator_of_mem hp]
      · have hp' : p ∉ T ⁻¹' S := hp
        simp [Set.indicator_of_notMem hp', Set.indicator_of_notMem hp]
    have key := hl (fun h => S.indicator (1 : ℂ → ENNReal) (B h))
      ((measurable_one.indicator hS).comp hB.measurable) (fun x h => by simp only [hN]) g
    rw [Measure.map_apply hTg hS, Measure.map_apply hT1 hS, withDensity_apply _ (hTg hS),
      withDensity_apply _ (hT1 hS), ← lintegral_indicator (hTg hS), ← lintegral_indicator (hT1 hS)]
    simp only [hind]
    exact key
  have e : ∀ T : Fˣ × Fˣ × GL (Fin 2) F → ℂ, Measurable T →
      ∫ p, ((wR p : ℝ) : ℂ) * T p ∂mIw ψ =
        ∫ z, z ∂(Measure.map T ((mIw ψ).withDensity fun p => ENNReal.ofReal (wR p))) := by
    intro T hT
    rw [integral_map (f := fun z : ℂ => z) hT.aemeasurable aestronglyMeasurable_id,
      integral_withDensity_eq_integral_toReal_smul hd hlt]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [ENNReal.toReal_ofReal (GlobalTheory.CompanionTheory.BochIw.wR_pos' p).le, Complex.real_smul]
  rw [e _ hTg, e _ hT1, hmap]

end GlobalTheory.CompanionTheory.RInvB
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

theorem _root_.GlobalTheory.T.iwasawa_integral_translate_invariance : ForS fun F _ _ _ _ _ _ ψ => ∀ B : GL (Fin 2) F → ℂ, Continuous B → (∀ x h, B (uni2 x * h) = B h) →
  ∀ g : GL (Fin 2) F, ∫ p, ((wR p : ℝ) : ℂ) * B (hI p * g) ∂mIw ψ = ∫ p, ((wR p : ℝ) : ℂ) * B (hI p) ∂mIw ψ := by
  first | exact @GlobalTheory.CompanionTheory.RInvB.integral_right_invariant | exact GlobalTheory.CompanionTheory.RInvB.integral_right_invariant | (intros; apply GlobalTheory.CompanionTheory.RInvB.integral_right_invariant <;> assumption) | exact @GlobalTheory.CompanionTheory.RInvB.integral_right_invariant | exact GlobalTheory.CompanionTheory.RInvB.integral_right_invariant | (intros; apply GlobalTheory.CompanionTheory.RInvB.integral_right_invariant <;> assumption)
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.ZetaIntegralBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def Af (B e : ℝ) (a : Fˣ) : ENNReal :=
  Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} (fun a => ENNReal.ofReal ((modulus (a : F) : ℝ) ^ e)) a

def ball2 (R : ℝ) : Set (GL (Fin 2) F) := {g | ∀ i j, (modulus (g.val i j) : ℝ) ≤ R}

def Ck (R ε : ℝ) (g k : GL (Fin 2) F) : ENNReal :=
  Set.indicator (ball2 R) (fun g => ENNReal.ofReal
    (((modulus (g.val).det : ℝ) / mx (e2r (k * g)) ^ 2) ^ (1 / 2 - ε))) g

omit [MeasurableSpace F] [BorelSpace F] in
theorem mx_pos (g : GL (Fin 2) F) : 0 < mx (e2r g) := by
  by_contra h
  have h' : mx (e2r g) ≤ 0 := not_lt.1 h
  have h0 : (modulus (g.val 1 0) : ℝ) ≤ 0 := (le_max_left _ _).trans h'
  have h1 : (modulus (g.val 1 1) : ℝ) ≤ 0 := (le_max_right _ _).trans h'
  have e0 : g.val 1 0 = 0 := by
    by_contra hne
    have : (0 : ℝ) < (modulus (g.val 1 0) : ℝ) := by exact_mod_cast modulus_pos hne
    linarith
  have e1 : g.val 1 1 = 0 := by
    by_contra hne
    have : (0 : ℝ) < (modulus (g.val 1 1) : ℝ) := by exact_mod_cast modulus_pos hne
    linarith
  have hd : (g.val).det = 0 := by rw [Matrix.det_fin_two, e0, e1]; ring
  have hu : IsUnit (g.val).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  exact hu.ne_zero hd

omit [MeasurableSpace F] [BorelSpace F] in
theorem det_pos (g : GL (Fin 2) F) : 0 < (modulus (g.val).det : ℝ) := by
  have hu : IsUnit (g.val).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  exact_mod_cast modulus_pos hu.ne_zero

omit [MeasurableSpace F] [BorelSpace F] in
theorem cont_entry (i j : Fin 2) : Continuous fun g : GL (Fin 2) F => (modulus (g.val i j) : ℝ) :=
  NNReal.continuous_coe.comp (continuous_modulus.comp
    (Continuous.matrix_elem Units.continuous_val i j))

omit [MeasurableSpace F] [BorelSpace F] in
theorem cont_mx : Continuous fun g : GL (Fin 2) F => mx (e2r g) := by
  have : (fun g : GL (Fin 2) F => mx (e2r g)) =
      fun g => max (modulus (g.val 1 0) : ℝ) (modulus (g.val 1 1) : ℝ) := by
    funext g; simp [mx, e2r]
  rw [this]
  exact (cont_entry 1 0).max (cont_entry 1 1)

omit [MeasurableSpace F] [BorelSpace F] in
theorem cont_det : Continuous fun g : GL (Fin 2) F => (modulus (g.val).det : ℝ) :=
  NNReal.continuous_coe.comp (continuous_modulus.comp
    (Continuous.matrix_det Units.continuous_val))

theorem rpow_alg {d m σ ε : ℝ} (hd : 0 < d) (hm : 0 < m) :
    d ^ (σ + 1 / 2) * (d / m ^ 2) ^ (1 / 2 - ε) = d ^ (σ + 1 - ε) * m ^ (-(1 - 2 * ε)) := by
  have e1 : (m ^ 2) ^ (1 / 2 - ε) = m ^ (1 - 2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
    congr 1
    push_cast
    ring
  have e2 : d ^ (σ + 1 - ε) = d ^ (σ + 1 / 2) * d ^ (1 / 2 - ε) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  rw [Real.div_rpow hd.le (by positivity), e1, e2, Real.rpow_neg hm.le, div_eq_mul_inv]
  ring

theorem measurable_Af (B e : ℝ) : Measurable (Af (F := F) B e) := by
  have hm : Continuous fun a : Fˣ => (modulus (a : F) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val)
  exact Measurable.indicator (ENNReal.measurable_ofReal.comp (hm.measurable.pow_const e))
    (measurableSet_le hm.measurable measurable_const)

omit [MeasurableSpace F] [BorelSpace F] in
theorem isClosed_ball2 (R : ℝ) : IsClosed (ball2 (F := F) R) := by
  simp only [ball2, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (cont_entry i j) continuous_const

theorem measurable_Ck (R ε : ℝ) :
    Measurable fun q : GL (Fin 2) F × GL (Fin 2) F => Ck R ε q.1 q.2 := by
  haveI : SecondCountableTopology (GL (Fin 2) F) := GlobalTheory.CompanionTheory.LocalTestVectors.secondCountable_GL2
  have e : (fun q : GL (Fin 2) F × GL (Fin 2) F => Ck R ε q.1 q.2) =
      Set.indicator (Prod.fst ⁻¹' ball2 R) (fun q => ENNReal.ofReal
        (((modulus (q.1.val).det : ℝ) / mx (e2r (q.2 * q.1)) ^ 2) ^ (1 / 2 - ε))) := by
    funext q
    rfl
  rw [e]
  have h1 : Continuous fun q : GL (Fin 2) F × GL (Fin 2) F => (modulus (q.1.val).det : ℝ) :=
    cont_det.comp continuous_fst
  have h2 : Continuous fun q : GL (Fin 2) F × GL (Fin 2) F => mx (e2r (q.2 * q.1)) :=
    cont_mx.comp (continuous_snd.mul continuous_fst)
  exact Measurable.indicator (ENNReal.measurable_ofReal.comp
    ((h1.measurable.div (h2.measurable.pow_const 2)).pow_const _))
    (measurable_fst (isClosed_ball2 R).measurableSet)

theorem measurable_Ck_right (R ε : ℝ) (g : GL (Fin 2) F) : Measurable (Ck (F := F) R ε g) :=
  Measurable.comp (g := fun q : GL (Fin 2) F × GL (Fin 2) F => Ck R ε q.1 q.2)
    (f := fun k : GL (Fin 2) F => (g, k)) (measurable_Ck R ε) measurable_prodMk_left

theorem integrand_eq (R B σ ε : ℝ) (g : GL (Fin 2) F) (p : Fˣ × Fˣ × GL (Fin 2) F) :
    ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) =
      Af B (σ - 2 * ε) p.1 * (Af R (2 * σ) p.2.1 * Ck R ε g p.2.2) := by
  obtain ⟨a, b, k⟩ := p
  have ha : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have hb : (0 : ℝ) < (modulus (b : F) : ℝ) := by exact_mod_cast modulus_pos b.ne_zero
  have hE : 0 ≤ ((modulus (g.val).det : ℝ) / mx (e2r (k * g)) ^ 2) ^ (1 / 2 - ε) :=
    Real.rpow_nonneg (div_nonneg (det_pos g).le (by positivity)) _
  simp only [Mj, wR]
  by_cases h : (∀ i j, (modulus (g.val i j) : ℝ) ≤ R) ∧ (modulus (b : F) : ℝ) ≤ R ∧ (modulus (a : F) : ℝ) ≤ B
  · rw [if_pos h]
    obtain ⟨h1, h2, h3⟩ := h
    have m1 : g ∈ ball2 R := h1
    have m2 : b ∈ {a : Fˣ | (modulus (a : F) : ℝ) ≤ R} := h2
    have m3 : a ∈ {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} := h3
    rw [Af, Af, Ck, Set.indicator_of_mem m1, Set.indicator_of_mem m2, Set.indicator_of_mem m3,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e : (modulus (a : F) : ℝ) ^ (σ + 1 - 2 * ε) =
        (modulus (a : F) : ℝ) ^ (σ - 2 * ε) * (modulus (a : F) : ℝ) := by
      rw [show σ + 1 - 2 * ε = (σ - 2 * ε) + 1 by ring, Real.rpow_add ha, Real.rpow_one]
    rw [e]
    field_simp
  · rw [if_neg h, ENNReal.ofReal_zero, mul_zero]
    by_cases h1 : g ∈ ball2 R
    · by_cases h2 : (modulus (b : F) : ℝ) ≤ R
      · have h3 : ¬ (modulus (a : F) : ℝ) ≤ B := fun h3 => h ⟨h1, h2, h3⟩
        have m3 : a ∉ {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} := h3
        simp only [Af]
        rw [Set.indicator_of_notMem m3, zero_mul]
      · have m2 : b ∉ {a : Fˣ | (modulus (a : F) : ℝ) ≤ R} := h2
        simp only [Af]
        rw [Set.indicator_of_notMem m2, zero_mul, mul_zero]
    · simp only [Ck]
      rw [Set.indicator_of_notMem h1, mul_zero, mul_zero]

theorem inner_eq (ψ : AddChar F Circle) [SFinite (LFS.hG ψ)] (R B σ ε : ℝ) (g : GL (Fin 2) F) :
    ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) ∂mIw ψ =
      (∫⁻ a, Af B (σ - 2 * ε) a ∂multHaar F) * ((∫⁻ b, Af R (2 * σ) b ∂multHaar F) *
        ∫⁻ k, Ck R ε g k ∂(LFS.hG ψ).restrict (K2 F)) := by
  have hC : Measurable (Ck (F := F) R ε g) := measurable_Ck_right R ε g
  simp_rw [integrand_eq]
  unfold mIw
  rw [lintegral_prod_mul (f := Af B (σ - 2 * ε))
      (g := fun q : Fˣ × GL (Fin 2) F => Af R (2 * σ) q.1 * Ck R ε g q.2)
      (measurable_Af _ _).aemeasurable
      (((measurable_Af _ _).comp measurable_fst).mul (hC.comp measurable_snd)).aemeasurable,
    lintegral_prod_mul (f := Af R (2 * σ)) (g := Ck R ε g)
      (measurable_Af _ _).aemeasurable hC.aemeasurable]

theorem factor_le {R σ ε : ℝ} {k : GL (Fin 2) F} (hk : k ∈ K2 F) (g : GL (Fin 2) F) :
    ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (σ + 1 / 2)) * Ck R ε g k ≤
      Set.indicator (ball2 R) (fun g : GL (Fin 2) F => ENNReal.ofReal
        ((modulus (g.val).det : ℝ) ^ (σ + 1 - ε) * mx (e2r g) ^ (-(1 - 2 * ε)))) (k * g) := by
  by_cases hg : g ∈ ball2 R
  · have hkg : k * g ∈ ball2 R := fun i j => by
      have := GlobalTheory.CompanionTheory.LFCoords.modulus_mul_entry_le (κ := k.val) (k := g.val)
        ((GLnLocal.mem_integralGL_iff F 2).1 hk).1 hg i j
      simpa [Units.val_mul] using this
    have hd : modulus ((k * g).val).det = modulus (g.val).det := by
      rw [Units.val_mul, Matrix.det_mul, modulus_mul, GlobalTheory.CompanionTheory.KHBound.modulus_det_integralGL hk, one_mul]
    rw [Ck, Set.indicator_of_mem hg, Set.indicator_of_mem hkg,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (det_pos g).le _), hd,
      rpow_alg (det_pos g) (mx_pos (k * g))]
  · rw [Ck, Set.indicator_of_notMem hg, mul_zero]
    exact zero_le

theorem outer_finite : ForS fun F _ _ _ _ _ _ ψ => ∀ R B σ ε : ℝ, 0 < ε → 2 * ε < σ → ε < 1 / 2 →
  ∫⁻ g, ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (σ + 1 / 2)) *
    ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) ∂mIw ψ ∂LFS.hG ψ < ⊤ := by
  intro F _ _ _ _ _ _ ψ hψ R B σ ε h0 h1 h2
  haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
  haveI : SFinite (LFS.hG ψ) := by unfold LFS.hG; infer_instance
  have hKc : IsCompact (K2 F) := GLnLocal.isCompact_integralGL F 2
  have hKm : MeasurableSet (K2 F) := hKc.isClosed.measurableSet
  have hA₁ : (∫⁻ a, Af B (σ - 2 * ε) a ∂multHaar F) < ⊤ :=
    GlobalTheory.T.lintegral_bounded_modulus_power_finite F ψ hψ B (σ - 2 * ε) (by linarith)
  have hA₂ : (∫⁻ b, Af R (2 * σ) b ∂multHaar F) < ⊤ :=
    GlobalTheory.T.lintegral_bounded_modulus_power_finite F ψ hψ R (2 * σ) (by linarith)
  have hT : (∫⁻ g, Set.indicator (ball2 R) (fun g : GL (Fin 2) F => ENNReal.ofReal
      ((modulus (g.val).det : ℝ) ^ (σ + 1 - ε) * mx (e2r g) ^ (-(1 - 2 * ε)))) g ∂LFS.hG ψ) < ⊤ :=
    GlobalTheory.T.lintegral_det_second_vector_finite F ψ hψ R (σ + 1 - ε) (1 - 2 * ε) (by linarith) (by linarith) (by linarith)
  set A₁ := ∫⁻ a, Af B (σ - 2 * ε) a ∂multHaar F
  set A₂ := ∫⁻ b, Af R (2 * σ) b ∂multHaar F
  set H := Set.indicator (ball2 R) (fun g : GL (Fin 2) F => ENNReal.ofReal
      ((modulus (g.val).det : ℝ) ^ (σ + 1 - ε) * mx (e2r g) ^ (-(1 - 2 * ε))))
  set T := ∫⁻ g, H g ∂LFS.hG ψ
  set D := fun g : GL (Fin 2) F => ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (σ + 1 / 2))
  have hD : Measurable D := ENNReal.measurable_ofReal.comp
    (cont_det.measurable.pow_const _)
  have hJ : Measurable (Function.uncurry fun (g k : GL (Fin 2) F) => D g * Ck R ε g k) :=
    (hD.comp measurable_fst).mul (measurable_Ck R ε)
  have hAA : A₁ * A₂ ≠ ⊤ := (ENNReal.mul_lt_top hA₁ hA₂).ne
  have step : ∀ g : GL (Fin 2) F, D g *
      ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) ∂mIw ψ =
      (A₁ * A₂) * ∫⁻ k, D g * Ck R ε g k ∂(LFS.hG ψ).restrict (K2 F) := by
    intro g
    have hC : Measurable (Ck (F := F) R ε g) := measurable_Ck_right R ε g
    rw [inner_eq, lintegral_const_mul _ hC]
    ring
  have hin : ∀ k ∈ K2 F, ∫⁻ g, D g * Ck R ε g k ∂LFS.hG ψ ≤ T := by
    intro k hk
    calc ∫⁻ g, D g * Ck R ε g k ∂LFS.hG ψ ≤ ∫⁻ g, H (k * g) ∂LFS.hG ψ :=
          lintegral_mono fun g => factor_le hk g
      _ = T := lintegral_mul_left_eq_self H k
  have hfin : (LFS.hG ψ).restrict (K2 F) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hKc.measure_lt_top
  calc ∫⁻ g, D g * ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) ∂mIw ψ ∂LFS.hG ψ
      = ∫⁻ g, (A₁ * A₂) * ∫⁻ k, D g * Ck R ε g k ∂(LFS.hG ψ).restrict (K2 F) ∂LFS.hG ψ :=
        lintegral_congr step
    _ = (A₁ * A₂) * ∫⁻ g, ∫⁻ k, D g * Ck R ε g k ∂(LFS.hG ψ).restrict (K2 F) ∂LFS.hG ψ :=
        lintegral_const_mul' _ _ hAA
    _ = (A₁ * A₂) * ∫⁻ k, ∫⁻ g, D g * Ck R ε g k ∂LFS.hG ψ ∂(LFS.hG ψ).restrict (K2 F) := by
        rw [lintegral_lintegral_swap hJ.aemeasurable]
    _ ≤ (A₁ * A₂) * ∫⁻ _k, T ∂(LFS.hG ψ).restrict (K2 F) := by
        exact mul_le_mul' le_rfl (setLIntegral_mono' hKm hin)
    _ = (A₁ * A₂) * (T * (LFS.hG ψ).restrict (K2 F) Set.univ) := by rw [lintegral_const]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hA₁ hA₂) (ENNReal.mul_lt_top hT hfin)

end GlobalTheory.CompanionTheory.ZetaIntegralBound
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_iwasawa_majorant_finite : ForS fun F _ _ _ _ _ _ ψ => ∀ R B σ ε : ℝ, 0 < ε → 2 * ε < σ → ε < 1 / 2 →
  ∫⁻ g, ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (σ + 1 / 2)) *
    ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) ∂mIw ψ ∂LFS.hG ψ < ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ZetaIntegralBound.outer_finite
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Unfolding

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem second_row_unipotent_invariant (x : F) (h : GL (Fin 2) F) : e2r (uni2 x * h) = e2r h := by
  ext i
  fin_cases i <;> simp [e2r, uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem Bq_uni (ψ : AddChar F Circle) {W₀ W' : GL (Fin 2) F → ℂ} (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ)
    (h₀ : ∀ x g, W₀ (uni2 x * g) = (ψ x : ℂ) * W₀ g) (h₁ : ∀ x g, W' (uni2 x * g) = (ψ⁻¹ x : ℂ) * W' g)
    (g : GL (Fin 2) F) (x : F) (h : GL (Fin 2) F) :
    Bq ψ W₀ W' Φ s g (uni2 x * h) = Bq ψ W₀ W' Φ s g h := by
  have hc : (ψ x : ℂ) * (ψ⁻¹ x : ℂ) = 1 := by
    rw [← Circle.coe_mul, AddChar.inv_apply', mul_inv_cancel, Circle.coe_one]
  unfold Bq
  rw [h₀ x h, mul_assoc (uni2 x) h g, h₁ x (h * g), second_row_unipotent_invariant, map_mul, GlobalTheory.CompanionTheory.DampedZetaMajorant.Iter.det_unipotent_adele, one_mul]
  linear_combination (W₀ h * W' (h * g) * pFT ψ Φ g.val (e2r h) * mp (GeneralLinearGroup.det h) s) * hc

omit [MeasurableSpace F] [BorelSpace F] in
theorem wR_eq (p : Fˣ × Fˣ × GL (Fin 2) F) : ((wR p : ℝ) : ℂ) = mp p.1 (-1) := by
  rw [wR, mp, Complex.cpow_neg_one]
  push_cast
  rfl

theorem zeta_integrand_iwasawa_eq_bilinear (ψ : AddChar F Circle) (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ)
    (g : GL (Fin 2) F) (p : Fˣ × Fˣ × GL (Fin 2) F) (hp : p.2.2 ∈ K2 F) :
    z2I W₀ (tr2 W' g) (pFT ψ Φ g.val) s p = ((wR p : ℝ) : ℂ) * Bq ψ W₀ W' Φ s g (hI p) := by
  have e : mp p.1 (s - 1) = mp p.1 (-1) * mp p.1 s := by
    rw [← GlobalTheory.CompanionTheory.DampedZetaMajorant.Iter.mp_add]; congr 1; ring
  rw [z2I, Bq, GlobalTheory.CompanionTheory.DampedZetaMajorant.Iter.mp_det_hI p hp, wR_eq, e, tr2]
  ring

omit [MeasurableSpace F] [BorelSpace F] in
theorem cont_mp (s : ℂ) : Continuous fun h : Fˣ => mp h s := by
  have hc : Continuous fun h : Fˣ => (((modulus (h : F) : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))
  simp only [mp]
  refine hc.cpow continuous_const fun h => ?_
  have h0 : (0 : ℝ) < (modulus (h : F) : ℝ) := by exact_mod_cast modulus_pos h.ne_zero
  exact Complex.ofReal_mem_slitPlane.2 h0

omit [MeasurableSpace F] [BorelSpace F] in
theorem cont_det : Continuous fun h : GL (Fin 2) F => (GeneralLinearGroup.det h : Fˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)).matrix_det
  · have : (fun h : GL (Fin 2) F => (((GeneralLinearGroup.det h)⁻¹ : Fˣ) : F)) =
        fun h : GL (Fin 2) F => ((h⁻¹ : GL (Fin 2) F).val).det := by
      funext h
      rw [← map_inv]
      rfl
    exact this ▸ ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)).comp continuous_inv).matrix_det

omit [MeasurableSpace F] [BorelSpace F] in
theorem continuous_second_vector_GL2 : Continuous (e2r : GL (Fin 2) F → Fin 2 → F) := by
  refine continuous_pi fun i => ?_
  have hv := Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)
  fin_cases i
  · exact hv.matrix_elem 1 0
  · exact hv.matrix_elem 1 1

theorem cont_Bq (ψ : AddChar F Circle) {W₀ W' : GL (Fin 2) F → ℂ} {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (s : ℂ)
    (c₀ : Continuous W₀) (c₁ : Continuous W')
    (cP : Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2)) (g : GL (Fin 2) F) :
    Continuous (Bq ψ W₀ W' Φ s g) := by
  show Continuous fun h => W₀ h * W' (h * g) * pFT ψ Φ g.val (e2r h) * mp (GeneralLinearGroup.det h) s
  have a1 : Continuous fun h : GL (Fin 2) F => pFT ψ Φ g.val (e2r h) :=
    cP.comp (continuous_const.prodMk continuous_second_vector_GL2)
  exact ((c₀.mul (c₁.comp (continuous_id.mul continuous_const))).mul a1).mul ((cont_mp s).comp cont_det)

theorem fixg (ψ : AddChar F Circle) (hψ : IsStd ψ) {W₀ W' : GL (Fin 2) F → ℂ} {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (s : ℂ)
    (c₀ : Continuous W₀) (c₁ : Continuous W')
    (cP : Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2))
    (h₀ : ∀ x g, W₀ (uni2 x * g) = (ψ x : ℂ) * W₀ g) (h₁ : ∀ x g, W' (uni2 x * g) = (ψ⁻¹ x : ℂ) * W' g)
    (g : GL (Fin 2) F) :
    ∫ p, Aq ψ W₀ W' Φ s (p, g) ∂mIw ψ =
      mp (GeneralLinearGroup.det g) (s + 1 / 2) * Z2 ψ W₀ (tr2 W' g) (pFT ψ Φ g.val) s := by
  have key := GlobalTheory.T.iwasawa_integral_translate_invariance F ψ hψ (Bq ψ W₀ W' Φ s g) (cont_Bq ψ s c₀ c₁ cP g) (Bq_uni ψ Φ s h₀ h₁ g) g⁻¹
  have e : ∫ p, Aq ψ W₀ W' Φ s (p, g) ∂mIw ψ = mp (GeneralLinearGroup.det g) (s + 1 / 2) *
      ∫ p, ((wR p : ℝ) : ℂ) * Bq ψ W₀ W' Φ s g (hI p * g⁻¹) ∂mIw ψ := by
    simp only [Aq]
    exact integral_const_mul _ _
  rw [e, key]
  congr 1
  exact integral_congr_ae ((GlobalTheory.CompanionTheory.LocalTestVectors.ae_mem_maximal_compact ψ).mono fun p hp => (zeta_integrand_iwasawa_eq_bilinear ψ W₀ W' Φ s g p hp).symm)

omit [MeasurableSpace F] [BorelSpace F] in
theorem enorm_mp (a : Fˣ) (z : ℂ) :
    ‖mp a z‖ₑ = ENNReal.ofReal ((modulus (a : F) : ℝ) ^ z.re) := by
  have h0 : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  rw [← ofReal_norm, mp, Complex.norm_cpow_eq_rpow_re_of_pos h0]

omit [MeasurableSpace F] [BorelSpace F] in
theorem enorm_wR (p : Fˣ × Fˣ × GL (Fin 2) F) : ‖((wR p : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (wR p) := by
  have h0 : 0 ≤ wR p := inv_nonneg.2 (by positivity)
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0]

theorem aqi (ψ : AddChar F Circle) (hψ : IsStd ψ) (ω : Fˣ →* ℂˣ) (G : (Fˣ →* ℂˣ) → ℂ → ℂ)
    (V' : Submodule ℂ (GL (Fin 2) F → ℂ)) (hω : IsUnit1 ω) (H : WhT ψ⁻¹ ω G V') (ν : Fˣ →* ℂˣ) (hν : IsUnit1 ν)
    (W₀ : GL (Fin 2) F → ℂ) (hW₀ : W₀ ∈ V2 ψ ν ν⁻¹) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (hΦ : Φ ∈ LFS.SB F)
    (W' : GL (Fin 2) F → ℂ) (hW' : W' ∈ V') (s : ℂ) (hs : 0 < s.re) :
    Integrable (Aq ψ W₀ W' Φ s) ((mIw ψ).prod (LFS.hG ψ)) := by
  haveI : SFinite (LFS.hG ψ) := by unfold LFS.hG; infer_instance
  haveI : SFinite (mIw ψ) := by unfold mIw; infer_instance
  obtain ⟨h₀, hcen, c₀, hb₀⟩ := GlobalTheory.T.godement_vector_decay_bound F ψ hψ ν hν W₀ hW₀
  obtain ⟨c₁, hb₁⟩ := GlobalTheory.T.whittaker_vector_gauge_bound F ψ hψ ω G V' hω H W' hW'
  obtain ⟨cP, C₂, R, hC₂, hbP⟩ := GlobalTheory.T.partial_fourier_continuous_bounded_support F ψ hψ Φ hΦ
  obtain ⟨ε, hε, hε2, hσ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ 2 * ε < s.re :=
    ⟨min (s.re / 4) (1 / 4), lt_min (by positivity) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num),
      by have := min_le_left (s.re / 4) (1 / 4); linarith⟩
  obtain ⟨C₀, B, hC₀, hW⟩ := hb₀ ε hε
  obtain ⟨C₁, hC₁, hWb⟩ := hb₁ ε hε
  have hptb := GlobalTheory.T.outer_zeta_integrand_bound F ψ hψ W₀ W' Φ s C₀ C₁ C₂ B R ε hC₀ hC₁ hC₂ hε hε2 hcen hW hWb hbP
  have hbnd := GlobalTheory.T.lintegral_iwasawa_majorant_finite F ψ hψ R B s.re ε hε hσ hε2
  have hc := GlobalTheory.T.continuous_outer_zeta_integrand F ψ hψ W₀ W' Φ s c₀ c₁ cP
  have hm : Measurable (fun q => ‖Aq ψ W₀ W' Φ s q‖ₑ) := hc.enorm.measurable
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hm.aemeasurable]
  set CC : ENNReal := ENNReal.ofReal (C₀ * C₁ * C₂) with hCC
  have step : ∀ g : GL (Fin 2) F, ∫⁻ p, ‖Aq ψ W₀ W' Φ s (p, g)‖ₑ ∂mIw ψ ≤
      CC * (ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (s.re + 1 / 2)) *
        ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p) ∂mIw ψ) := by
    intro g
    set D : ENNReal := ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (s.re + 1 / 2)) with hD
    have hdet : ‖mp (GeneralLinearGroup.det g) (s + 1 / 2)‖ₑ = D := by
      rw [enorm_mp, hD]
      simp [Matrix.GeneralLinearGroup.val_det_apply]
    have hf : Measurable fun h => ‖Bq ψ W₀ W' Φ s g h‖ₑ := (cont_Bq ψ s c₀ c₁ cP g).enorm.measurable
    have hr := GlobalTheory.T.iwasawa_integral_right_translate_invariant F ψ hψ (fun h => ‖Bq ψ W₀ W' Φ s g h‖ₑ) hf
      (fun x h => by simp only [Bq_uni ψ Φ s h₀ (H.psi W' hW') g x h]) g⁻¹
    calc ∫⁻ p, ‖Aq ψ W₀ W' Φ s (p, g)‖ₑ ∂mIw ψ
        = ∫⁻ p, D * (ENNReal.ofReal (wR p) * ‖Bq ψ W₀ W' Φ s g (hI p * g⁻¹)‖ₑ) ∂mIw ψ := by
          refine lintegral_congr fun p => ?_
          simp only [Aq]
          rw [enorm_mul, enorm_mul, hdet, enorm_wR]
      _ = D * ∫⁻ p, ENNReal.ofReal (wR p) * ‖Bq ψ W₀ W' Φ s g (hI p * g⁻¹)‖ₑ ∂mIw ψ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = D * ∫⁻ p, ENNReal.ofReal (wR p) * ‖Bq ψ W₀ W' Φ s g (hI p)‖ₑ ∂mIw ψ := by rw [hr]
      _ ≤ D * ∫⁻ p, CC * (ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p)) ∂mIw ψ := by
          refine mul_le_mul' le_rfl ?_
          refine lintegral_mono_ae ((GlobalTheory.CompanionTheory.LocalTestVectors.ae_mem_maximal_compact ψ).mono fun p hp => ?_)
          have hb := hptb g p hp
          have : ‖Bq ψ W₀ W' Φ s g (hI p)‖ₑ ≤ CC * ENNReal.ofReal (Mj R B s.re ε g p) := by
            rw [hCC, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal hb
          calc ENNReal.ofReal (wR p) * ‖Bq ψ W₀ W' Φ s g (hI p)‖ₑ
              ≤ ENNReal.ofReal (wR p) * (CC * ENNReal.ofReal (Mj R B s.re ε g p)) := by gcongr
            _ = CC * (ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p)) := by ring
      _ = CC * (D * ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p) ∂mIw ψ) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          ring
  calc ∫⁻ g, ∫⁻ p, ‖Aq ψ W₀ W' Φ s (p, g)‖ₑ ∂mIw ψ ∂LFS.hG ψ
      ≤ ∫⁻ g, CC * (ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (s.re + 1 / 2)) *
        ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p) ∂mIw ψ) ∂LFS.hG ψ :=
        lintegral_mono step
    _ = CC * ∫⁻ g, ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (s.re + 1 / 2)) *
        ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B s.re ε g p) ∂mIw ψ ∂LFS.hG ψ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbnd

end D

theorem main : A1 := by
  intro F _ _ _ _ _ _ ψ hψ ω G V' hω H ν hν W₀ hW₀ Φ hΦ W' hW' s hs0 hs1
  haveI : SFinite (LFS.hG ψ) := by unfold LFS.hG; infer_instance
  haveI : SFinite (mIw ψ) := by unfold mIw; infer_instance
  have hA := aqi ψ hψ ω G V' hω H ν hν W₀ hW₀ Φ hΦ W' hW' s hs0
  obtain ⟨h1, h2, h3, _⟩ := GlobalTheory.T.godement_vector_decay_bound F ψ hψ ν hν W₀ hW₀
  have hc' := (GlobalTheory.T.whittaker_vector_gauge_bound F ψ hψ ω G V' hω H W' hW').1
  have hP := (GlobalTheory.T.partial_fourier_continuous_bounded_support F ψ hψ Φ hΦ).1
  have hpt : ∀ᵐ p ∂mIw ψ, iw (LFS.Wp ψ W₀ Φ) W' s p = ∫ g, Aq ψ W₀ W' Φ s (p, g) ∂LFS.hG ψ :=
    (GlobalTheory.CompanionTheory.LocalTestVectors.ae_mem_maximal_compact ψ).mono fun p hp => GlobalTheory.T.iwasawa_integral_eq_group_integral F ψ hψ W₀ W' Φ s hΦ p hp
  have hg := fixg ψ hψ (W₀ := W₀) (W' := W') (Φ := Φ) s h3 hc' hP h1 (H.psi W' hW')
  refine ⟨?_, ?_, ?_⟩
  · exact hA.integral_prod_left.congr (hpt.mono fun _ h => h.symm)
  · have := hA.integral_prod_right
    simpa only [hg] using this
  · unfold zetaGL3GL2
    rw [integral_congr_ae hpt,
      integral_integral_swap (f := fun p g => Aq ψ W₀ W' Φ s (p, g)) hA]
    simp only [hg]

end GlobalTheory.CompanionTheory.GL2Unfolding
end
end
