import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaRegionMeasureBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerIwasawaGrowthBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricSumBelowThreshold
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import BuildAid.ForwardExisting

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_gl_two_holds : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (g : GL (Fin 2) F), ∃ (x : F) (m n : ℤ), ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ := by
  first | exact @GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two | exact GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two | (intros; apply GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two <;> assumption)
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_coordinates_bounded_region : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (x : F) (m n L : ℤ) (κ : GL (Fin 2) F) (R : ℝ) (t : Fˣ), κ ∈ GLnLocal.integralGL F 2 → R ≤ (residueCard F : ℝ) ^ L → (Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ)⁻¹ ∈ Ad3.LFS.om R t → m ≤ L ∧ n ≤ L ∧ (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n) ≤ (residueCard F : ℝ) ^ L := by
  first | exact @GlobalTheory.CompanionTheory.LFCoords.coords | exact GlobalTheory.CompanionTheory.LFCoords.coords | (intros; apply GlobalTheory.CompanionTheory.LFCoords.coords <;> assumption)
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_region_measure_bound : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (μ : Measure (GL (Fin 2) F)) [μ.IsMulLeftInvariant] (m n L : ℤ), IsOpen {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ∧ (n ≤ L → μ {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ≤ ENNReal.ofReal ((residueCard F : ℝ) ^ (L - n)) * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))) := by
  first | exact @GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume | exact GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume | (intros; apply GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume <;> assumption)
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_iwasawa_growth_bound : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (C : ℝ), (∀ x g, W' (Ad3.uni2 x * g) = (ψ x : ℂ) * W' g) → (∀ (a : Fˣ) g, W' (Ad3.dg2 a a * g) = W' g) → (∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 a 1 * κ)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 4 : ℝ)) → ∀ (t₁ t₂ b₁ b₂ : Fˣ) (x : F), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ))‖ ≤ C * (modulus ((t₁ * b₁ * (t₂ * b₂)⁻¹ : Fˣ) : F) : ℝ) ^ (1 / 4 : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerIwasawa.whittaker_bound_iwasawa | exact GlobalTheory.CompanionTheory.WhittakerIwasawa.whittaker_bound_iwasawa | (intros; apply GlobalTheory.CompanionTheory.WhittakerIwasawa.whittaker_bound_iwasawa <;> assumption)
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_sum_below_threshold : ∀ (q s Y : ℝ), 1 < q → 0 < s → 0 < Y → (∑' n : ℤ, (if q ^ n ≤ Y then ENNReal.ofReal (q ^ (s * (n : ℝ))) else 0)) ≤ ENNReal.ofReal (Y ^ s / (1 - q ^ (-s))) := by
  first | exact @GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div | exact GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div | (intros; apply GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div <;> assumption)
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.ShellSum

lemma shell_exponent_identity (q A : ℝ) (L m n : ℤ) (hq : 1 < q) :
    A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) * q ^ (L - n)
      = A * q ^ L * q ^ ((m : ℝ) / 4) * q ^ (-(n : ℝ) / 4) := by
  have hq0 : 0 < q := by linarith
  have e1 : q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) * q ^ (((L - n : ℤ)) : ℝ)
      = q ^ (L : ℝ) * q ^ ((m : ℝ) / 4) * q ^ (-(n : ℝ) / 4) := by
    rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
    congr 1
    push_cast
    ring
  rw [Real.rpow_intCast, Real.rpow_intCast] at e1
  linear_combination A * e1

theorem lintegral_le_of_shells :
    ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q A τ : ℝ) (L : ℤ) (c T₁ T₂ : ℝ≥0∞)
      (S : ℤ → ℤ → Set X) (Φ : X → ℝ≥0∞), 1 < q → 0 ≤ A → 0 < τ →
      (∀ m n, MeasurableSet (S m n)) →
      (∀ m n, n ≤ L → μ (S m n) ≤ ENNReal.ofReal (q ^ (L - n)) * c) →
      (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0)) ≤ T₁ →
      (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0)) ≤ T₂ →
      (∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧
        Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2))) →
      ∫⁻ y, Φ y ∂μ ≤ ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by
  intro X _ μ q A τ L c T₁ T₂ S Φ hq hA hτ hS hμ hT1 hT2 hΦ
  have hq0 : 0 < q := by linarith
  let a : ℤ → ℝ≥0∞ := fun m => if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0
  let b : ℤ → ℝ≥0∞ := fun n =>
    if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0
  let w : ℤ × ℤ → ℝ≥0∞ := fun p =>
    if p.1 ≤ L ∧ p.2 ≤ L ∧ τ * q ^ (-p.2) ≤ q ^ L then
      ENNReal.ofReal (A * q ^ (((p.2 : ℝ) - p.1) / 4) * q ^ (((p.1 : ℝ) + p.2) / 2))
    else 0
  have hpt : ∀ y, Φ y ≤ ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y := by
    intro y
    by_cases h0 : Φ y = 0
    · simp [h0]
    obtain ⟨m, n, h1, h2, h3, h4, h5⟩ := hΦ y h0
    refine le_trans ?_ (ENNReal.le_tsum (m, n))
    have hw : w (m, n) = ENNReal.ofReal
        (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) := by
      simp only [w]
      rw [if_pos ⟨h1, h2, h3⟩]
    rw [Set.indicator_of_mem (show y ∈ S (m, n).1 (m, n).2 from h4), hw]
    exact h5
  have hterm : ∀ p : ℤ × ℤ,
      w p * μ (S p.1 p.2) ≤ ENNReal.ofReal (A * q ^ L) * (a p.1 * b p.2 * c) := by
    rintro ⟨m, n⟩
    by_cases hc : m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L
    · obtain ⟨h1, h2, h3⟩ := hc
      have hw : w (m, n) = ENNReal.ofReal
          (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) := by
        simp only [w]
        rw [if_pos ⟨h1, h2, h3⟩]
      have ha : a m = ENNReal.ofReal (q ^ ((m : ℝ) / 4)) := by
        simp only [a]
        rw [if_pos h1]
      have hb : b n = ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) := by
        simp only [b]
        rw [if_pos h3]
      have hnn1 : 0 ≤ A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) := by positivity
      have hnn2 : 0 ≤ A * q ^ L := by positivity
      have hnn3 : 0 ≤ q ^ ((m : ℝ) / 4) := by positivity
      show w (m, n) * μ (S m n) ≤ ENNReal.ofReal (A * q ^ L) * (a m * b n * c)
      rw [hw, ha, hb]
      calc ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) * μ (S m n)
          ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) *
              (ENNReal.ofReal (q ^ (L - n)) * c) := by
            gcongr
            exact hμ m n h2
        _ = ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) * q ^ (L - n))
              * c := by
            rw [ENNReal.ofReal_mul hnn1]
            ring
        _ = ENNReal.ofReal (A * q ^ L * q ^ ((m : ℝ) / 4) * q ^ (-(n : ℝ) / 4)) * c := by
            rw [shell_exponent_identity q A L m n hq]
        _ = ENNReal.ofReal (A * q ^ L) *
              (ENNReal.ofReal (q ^ ((m : ℝ) / 4)) * ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) * c) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hnn2]
            ring
    · have hw : w (m, n) = 0 := by
        simp only [w]
        rw [if_neg hc]
      show w (m, n) * μ (S m n) ≤ _
      rw [hw, zero_mul]
      exact zero_le
  have hfac : ∑' p : ℤ × ℤ, a p.1 * b p.2 * c = (∑' m, a m) * (∑' n, b n) * c := by
    rw [ENNReal.tsum_prod (f := fun m n => a m * b n * c)]
    simp only [mul_assoc]
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  calc ∫⁻ y, Φ y ∂μ
      ≤ ∫⁻ y, ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y ∂μ := lintegral_mono hpt
    _ = ∑' p : ℤ × ℤ, ∫⁻ y, (S p.1 p.2).indicator (fun _ => w p) y ∂μ :=
        lintegral_tsum fun p => (measurable_const.indicator (hS p.1 p.2)).aemeasurable
    _ = ∑' p : ℤ × ℤ, w p * μ (S p.1 p.2) := by
        refine tsum_congr fun p => ?_
        exact lintegral_indicator_const (hS p.1 p.2) (w p)
    _ ≤ ∑' p : ℤ × ℤ, ENNReal.ofReal (A * q ^ L) * (a p.1 * b p.2 * c) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (A * q ^ L) * ((∑' m, a m) * (∑' n, b n) * c) := by
        rw [ENNReal.tsum_mul_left, hfac]
    _ ≤ ENNReal.ofReal (A * q ^ L) * (T₁ * T₂ * c) := by
        gcongr
    _ = ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by ring

end GlobalTheory.CompanionTheory.ShellSum
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_sum_measure_estimate : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q A τ : ℝ) (L : ℤ) (c T₁ T₂ : ℝ≥0∞) (S : ℤ → ℤ → Set X) (Φ : X → ℝ≥0∞), 1 < q → 0 ≤ A → 0 < τ → (∀ m n, MeasurableSet (S m n)) → (∀ m n, n ≤ L → μ (S m n) ≤ ENNReal.ofReal (q ^ (L - n)) * c) → (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0)) ≤ T₁ → (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0)) ≤ T₂ → (∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧ Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2))) → ∫⁻ y, Φ y ∂μ ≤ ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ShellSum.lintegral_le_of_shells
end

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.LFGInt2

theorem modulus_det_iwasawa_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (x : F) (a b : Fˣ) (κ : GL (Fin 2) F), κ ∈ GLnLocal.integralGL F 2 → (modulus ((Matrix.GeneralLinearGroup.det (Ad3.uni2 x * Ad3.dg2 a b * κ)⁻¹ : Fˣ) : F) : ℝ) = ((modulus (a : F) : ℝ) * (modulus (b : F) : ℝ))⁻¹ := by
  intro F _ _ _ _ x a b κ hκ
  have hκ1 : modulus ((Matrix.GeneralLinearGroup.det κ : Fˣ) : F) = 1 := by
    obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hκ
    have key : ∀ g : GL (Fin 2) F, (∀ i j, g i j ∈ 𝒪[F]) →
        modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ≤ 1 := by
      intro g hg
      rw [modulus_le_one_iff, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      exact sub_mem (mul_mem (hg 0 0) (hg 1 1)) (mul_mem (hg 0 1) (hg 1 0))
    have a' := key κ h1
    have b' := key κ⁻¹ h2
    rw [map_inv, Units.val_inv_eq_inv_val, modulus_inv] at b'
    have hpos := modulus_pos (Matrix.GeneralLinearGroup.det κ : Fˣ).ne_zero
    exact le_antisymm a' ((inv_le_one₀ hpos).1 b')
  have hd1 : Matrix.GeneralLinearGroup.det (Ad3.uni2 x) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Ad3.uni2, Matrix.det_fin_two]
  have hd2 : Matrix.GeneralLinearGroup.det (Ad3.dg2 a b) = a * b := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Ad3.dg2, Matrix.det_fin_two]
  rw [map_inv, map_mul, map_mul, hd1, hd2, one_mul, Units.val_inv_eq_inv_val, modulus_inv, Units.val_mul,
    modulus_mul, hκ1, mul_one, Units.val_mul, modulus_mul]
  push_cast
  rfl

open Ad3 Ad3.LFS in

theorem gInt2 : Ad3.LFS.GInt2 := by
  intro F _ _ _ _ _ _ ψ hψ ν hν V' H W' hW' R
  classical
  obtain ⟨C, B, hCB⟩ := H.bound W' hW' (1 / 4) (by norm_num)
  set q : ℝ := (residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast (one_lt_residueCard (K := F))
  have hq0 : 0 < q := by linarith
  obtain ⟨L₀, hL₀⟩ := pow_unbounded_of_one_lt R hq
  set L : ℤ := (L₀ : ℤ) with hLdef
  have hRL : R ≤ q ^ L := by rw [hLdef, zpow_natCast]; exact hL₀.le
  haveI hμ : (hG ψ).IsHaarMeasure := by unfold hG; infer_instance
  haveI hinv : (hG ψ).IsInvInvariant := ⟨Measures.inv_eq_self_GL F 2 (hG ψ)⟩
  set Kμ : ℝ≥0∞ := hG ψ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) with hKμ
  have hKfin : Kμ ≠ ∞ := (GLnLocal.isCompact_integralGL F 2).measure_lt_top.ne
  set C₁ : ℝ := max C 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  have hbound : ∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2,
      ‖W' (dg2 a 1 * κ)‖ ≤ C₁ * (modulus (a : F) : ℝ) ^ (1 / 4 : ℝ) := by
    intro a κ hκ
    have h := (hCB a κ hκ).1
    rw [show (1 / 2 - 1 / 4 : ℝ) = 1 / 4 by norm_num] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hpsi : ∀ x g, W' (uni2 x * g) = (ψ x : ℂ) * W' g := H.psi W' hW'
  have hcen : ∀ (a : Fˣ) g, W' (dg2 a a * g) = W' g := by
    intro a g
    rw [H.cen W' hW']
    simp
  obtain ⟨U, hU⟩ := H.smooth W' hW'
  have hWc : Continuous W' := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨{x | g⁻¹ * x ∈ U}, U.isOpen.preimage (continuous_const.mul continuous_id), by simp [U.one_mem],
      fun x hx => ?_⟩
    have := hU g _ hx
    simpa using this
  have hval : Continuous fun k : GL (Fin 2) F => (k : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have hmod : Continuous fun x : F => (modulus x : ℝ) := NNReal.continuous_coe.comp continuous_modulus
  have hdet : Continuous fun k : GL (Fin 2) F => (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) := by
    have : Continuous fun k : GL (Fin 2) F => ((GeneralLinearGroup.det k : Fˣ) : F) := by
      simpa using hval.matrix_det
    exact hmod.comp this
  have homc : ∀ t : Fˣ, IsClosed (om R t : Set (GL (Fin 2) F)) := by
    intro t
    have e : (om R t : Set (GL (Fin 2) F)) = (⋂ i, ⋂ j, {k : GL (Fin 2) F | (modulus ((k : Matrix (Fin 2) (Fin 2) F) i j) : ℝ) ≤ R}) ∩
        ⋂ j, {k : GL (Fin 2) F | (modulus ((t : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) ≤ R} := by
      ext k
      simp [om]
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (hmod.comp (hval.matrix_elem i j)) continuous_const) (isClosed_iInter fun j =>
      isClosed_le (hmod.comp (continuous_const.mul ((hval.comp continuous_inv).matrix_elem 1 j))) continuous_const)
  set r : ℝ := q ^ (-(1 / 4) : ℝ) with hr
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
  set D : ℝ := 1 - r with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hqL : 0 < q ^ L := zpow_pos hq0 L
  refine ⟨C₁ * q ^ L * ((q ^ L) ^ (1 / 4 : ℝ) / D) ^ 2 * Kμ.toReal, fun t₁ t₂ => ?_⟩
  set τ : ℝ := (modulus (t₂ : F) : ℝ) with hτdef
  have hτ : 0 < τ := by exact_mod_cast modulus_pos t₂.ne_zero
  set σ : ℝ := (modulus (t₁ : F) : ℝ) with hσdef
  have hσ : 0 < σ := by exact_mod_cast modulus_pos t₁.ne_zero
  set f : GL (Fin 2) F → ℝ := (om R t₂).indicator fun k =>
    ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => Set.indicator_nonneg (fun _ _ => by positivity) k
  have hfm : Measurable f := by
    refine Measurable.indicator (Continuous.measurable ?_) (homc t₂).measurableSet
    exact (hWc.comp (continuous_const.mul continuous_inv)).norm.mul
      (hdet.rpow_const fun _ => Or.inr (by norm_num))
  set A : ℝ := C₁ * (σ / τ) ^ (1 / 4 : ℝ) with hA
  have hA0 : 0 ≤ A := by positivity
  set T₁r : ℝ := (q ^ L) ^ (1 / 4 : ℝ) / D with hT₁r
  set T₂r : ℝ := (q ^ L / τ) ^ (1 / 4 : ℝ) / D with hT₂r
  have hT₁ : (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0)) ≤ ENNReal.ofReal T₁r := by
    have h := GlobalTheory.T.geometric_sum_below_threshold q (1 / 4) (q ^ L) hq (by norm_num) hqL
    refine le_of_eq_of_le (tsum_congr fun m => ?_) h
    simp only [zpow_le_zpow_iff_right₀ hq]
    rw [show (m : ℝ) / 4 = 1 / 4 * (m : ℝ) by ring]
  have hT₂ : (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0)) ≤ ENNReal.ofReal T₂r := by
    have h := GlobalTheory.T.geometric_sum_below_threshold q (1 / 4) (q ^ L / τ) hq (by norm_num) (div_pos hqL hτ)
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine le_of_eq_of_le (tsum_congr fun m => ?_) h
    simp only [Equiv.neg_apply, neg_neg, Int.cast_neg]
    have e : τ * q ^ m ≤ q ^ L ↔ q ^ m ≤ q ^ L / τ := by rw [le_div_iff₀ hτ, mul_comm]
    simp only [e]
    rw [show (m : ℝ) / 4 = 1 / 4 * (m : ℝ) by ring]
  set S : ℤ → ℤ → Set (GL (Fin 2) F) := fun m n => {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ q ^ (L - m) ∧
    ∃ κ ∈ GLnLocal.integralGL F 2, g = uni2 x * dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} with hS
  set Φ : GL (Fin 2) F → ℝ≥0∞ := fun g => ENNReal.ofReal (f g⁻¹) with hΦ
  have hcov : ∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧
      Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) := by
    intro g hg
    have hom : g⁻¹ ∈ om R t₂ := by
      by_contra h
      exact hg (by simp [hΦ, hf, h])
    obtain ⟨x, m, n, κ, hκ, rfl⟩ := GlobalTheory.T.iwasawa_decomposition_gl_two_holds F g
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.iwasawa_coordinates_bounded_region F x m n L κ R t₂ hκ hRL hom
    refine ⟨m, n, h1, h2, h4, ⟨x, h3, κ, hκ, rfl⟩, ENNReal.ofReal_le_ofReal ?_⟩
    rw [hf, Set.indicator_of_mem hom, inv_inv]
    have hw := GlobalTheory.T.whittaker_iwasawa_growth_bound F ψ W' C₁ hpsi hcen hbound t₁ t₂ (unifUnit F ^ m) (unifUnit F ^ n) x κ hκ
    have hu : ∀ k : ℤ, (modulus (((unifUnit F ^ k : Fˣ)) : F) : ℝ) = q ^ (-(k : ℝ)) := by
      intro k
      rw [modulus_of_ne_zero (Units.ne_zero _), ord_unifUnit_zpow, NNReal.coe_zpow, NNReal.coe_natCast,
        ← Real.rpow_intCast]
      push_cast
      rfl
    have hM : (modulus ((t₁ * unifUnit F ^ m * (t₂ * unifUnit F ^ n)⁻¹ : Fˣ) : F) : ℝ) =
        (σ / τ) * q ^ ((n : ℝ) - m) := by
      rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mul, modulus_mul, modulus_mul,
        modulus_inv, modulus_mul]
      simp only [NNReal.coe_mul, NNReal.coe_inv]
      rw [hu, hu, ← hσdef, ← hτdef, sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_neg hq0.le (m : ℝ),
        Real.rpow_neg hq0.le (n : ℝ)]
      have := (Real.rpow_pos_of_pos hq0 (m : ℝ)).ne'
      have := (Real.rpow_pos_of_pos hq0 (n : ℝ)).ne'
      field_simp
    have hdetg := modulus_det_iwasawa_inv F x (unifUnit F ^ m) (unifUnit F ^ n) κ hκ
    rw [hM] at hw
    rw [hdetg, hu, hu, mul_inv, ← Real.rpow_neg hq0.le, ← Real.rpow_neg hq0.le, neg_neg, neg_neg,
      ← Real.rpow_add hq0, ← Real.rpow_mul hq0.le]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hq0.le] at hw
    have e1 : ((n : ℝ) - m) * (1 / 4) = ((n : ℝ) - m) / 4 := by ring
    have e2 : ((m : ℝ) + n) * (1 / 2) = ((m : ℝ) + n) / 2 := by ring
    rw [e1] at hw
    rw [e2, hA, mul_assoc C₁]
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  have hmain := GlobalTheory.T.iwasawa_sum_measure_estimate (hG ψ) q A τ L Kμ _ _ S Φ hq hA0 hτ
    (fun m n => (GlobalTheory.T.iwasawa_region_measure_bound F (hG ψ) m n L).1.measurableSet) (fun m n hn => (GlobalTheory.T.iwasawa_region_measure_bound F (hG ψ) m n L).2 hn)
    hT₁ hT₂ hcov
  have hinvl : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ = ∫⁻ g, Φ g ∂hG ψ :=
    ((Measure.measurePreserving_inv (hG ψ)).lintegral_comp hfm.ennreal_ofReal).symm
  set Rr : ℝ := C₁ * q ^ L * ((q ^ L) ^ (1 / 4 : ℝ) / D) ^ 2 * Kμ.toReal * σ ^ (1 / 4 : ℝ) * τ ^ (-(1 / 2) : ℝ) with hRr
  have hRr0 : 0 ≤ Rr := by positivity
  have hfin : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ ≤ ENNReal.ofReal Rr := by
    rw [hinvl]
    refine hmain.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hKfin, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hw0 : 0 < τ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hτ _
    have hw2 : τ ^ (-(1 / 2) : ℝ) = ((τ ^ (1 / 4 : ℝ)) ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le, ← Real.rpow_neg hτ.le]
      norm_num
    rw [hRr, hA, hT₁r, hT₂r, hw2, Real.div_rpow hσ.le hτ.le, Real.div_rpow hqL.le hτ.le]
    field_simp
  refine ⟨⟨hfm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)]
    exact hfin.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hRr0 hfin

end GlobalTheory.CompanionTheory.LFGInt2
end
end
