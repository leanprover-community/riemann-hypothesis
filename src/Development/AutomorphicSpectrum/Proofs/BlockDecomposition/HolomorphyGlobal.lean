import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnZetaGL3GL2Dual
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerInducedOfFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaRegionMeasureBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricSumBelowThreshold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFourierTransformIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerCentral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerIwasawaGrowthBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDoubleIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusReduction
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactWhittakerEqGodementLocal
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerBoundQuadraticExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportQuadraticExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCharacterTwistNontrivialGalois
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisConjugate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNontrivialGaloisIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTranslateEntriesBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenNormImageUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormImageNeighbourhoodEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuityQuadraticExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNonvanishingCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasurability
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerIntegrableQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuousQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportBoundQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasureIndependence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialGaloisPlaceDegreeTwo

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_equation_generic : Ad3.SchwartzSpaceL2.FeGen := by
  first | exact @GlobalTheory.CompanionTheory.WhitFE.feGen | exact GlobalTheory.CompanionTheory.WhitFE.feGen | (intros; apply GlobalTheory.CompanionTheory.WhitFE.feGen <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_induced_of_functional_equation : Ad3.SchwartzSpaceL2.FeGen → ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → WhittakerModelGL2 ψ μ₁ μ₂ (V2 ψ μ₁ μ₂) := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerInducedSpan.whittaker_induced_space | exact GlobalTheory.CompanionTheory.WhittakerInducedSpan.whittaker_induced_space | (intros; apply GlobalTheory.CompanionTheory.WhittakerInducedSpan.whittaker_induced_space <;> assumption)
end

section
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.LFTempered

theorem whittaker_bound_iwasawa (e : ℝ) :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (C : ℝ), (∀ x g, W' (Ad3.uni2 x * g) = (ψ x : ℂ) * W' g) → (∀ (a : Fˣ) g, W' (Ad3.dg2 a a * g) = W' g) → (∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 a 1 * κ)‖ ≤ C * (modulus (a : F) : ℝ) ^ e) → ∀ (t₁ t₂ b₁ b₂ : Fˣ) (x : F), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ))‖ ≤ C * (modulus ((t₁ * b₁ * (t₂ * b₂)⁻¹ : Fˣ) : F) : ℝ) ^ e := by
  intro F _ _ _ _ ψ W' C hu hd hb t₁ t₂ b₁ b₂ x κ hκ
  have e' : Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ) =
      Ad3.uni2 ((t₁ : F) * x * ((t₂⁻¹ : Fˣ) : F)) * (Ad3.dg2 (t₂ * b₂) (t₂ * b₂) *
        (Ad3.dg2 (t₁ * b₁ * (t₂ * b₂)⁻¹) 1 * κ)) := by
    rw [← mul_assoc (Ad3.dg2 (t₂ * b₂) (t₂ * b₂)), ← GlobalTheory.CompanionTheory.WhittakerIwasawa.diagonal_mul_diagonal_alt, ← mul_assoc, ← mul_assoc,
      ← mul_assoc, GlobalTheory.CompanionTheory.WhittakerIwasawa.diagonal_mul_unipotent]
    simp only [mul_assoc]
  rw [e', hu, hd, norm_mul, Circle.norm_coe, one_mul]
  exact hb _ κ hκ

lemma shell_exponent_identity (q A e : ℝ) (L m n : ℤ) (hq : 1 < q) :
    A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2) * q ^ (L - n)
      = A * q ^ L * q ^ ((1 / 2 - e) * (m : ℝ)) * q ^ ((1 / 2 - e) * (-(n : ℝ))) := by
  have hq0 : 0 < q := by linarith
  have e1 : q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2) * q ^ (((L - n : ℤ)) : ℝ)
      = q ^ (L : ℝ) * q ^ ((1 / 2 - e) * (m : ℝ)) * q ^ ((1 / 2 - e) * (-(n : ℝ))) := by
    rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
    congr 1
    push_cast
    ring
  rw [Real.rpow_intCast, Real.rpow_intCast] at e1
  linear_combination A * e1

theorem lintegral_le_of_shells (e : ℝ) :
    ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q A τ : ℝ) (L : ℤ) (c T₁ T₂ : ℝ≥0∞)
      (S : ℤ → ℤ → Set X) (Φ : X → ℝ≥0∞), 1 < q → 0 ≤ A → 0 < τ →
      (∀ m n, MeasurableSet (S m n)) →
      (∀ m n, n ≤ L → μ (S m n) ≤ ENNReal.ofReal (q ^ (L - n)) * c) →
      (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (m : ℝ))) else 0)) ≤ T₁ →
      (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (-(n : ℝ)))) else 0)) ≤ T₂ →
      (∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧
        Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2))) →
      ∫⁻ y, Φ y ∂μ ≤ ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by
  intro X _ μ q A τ L c T₁ T₂ S Φ hq hA hτ hS hμ hT1 hT2 hΦ
  have hq0 : 0 < q := by linarith
  let a : ℤ → ℝ≥0∞ := fun m => if m ≤ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (m : ℝ))) else 0
  let b : ℤ → ℝ≥0∞ := fun n =>
    if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (-(n : ℝ)))) else 0
  let w : ℤ × ℤ → ℝ≥0∞ := fun p =>
    if p.1 ≤ L ∧ p.2 ≤ L ∧ τ * q ^ (-p.2) ≤ q ^ L then
      ENNReal.ofReal (A * q ^ (((p.2 : ℝ) - p.1) * e) * q ^ (((p.1 : ℝ) + p.2) / 2))
    else 0
  have hpt : ∀ y, Φ y ≤ ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y := by
    intro y
    by_cases h0 : Φ y = 0
    · simp [h0]
    obtain ⟨m, n, h1, h2, h3, h4, h5⟩ := hΦ y h0
    refine le_trans ?_ (ENNReal.le_tsum (m, n))
    have hw : w (m, n) = ENNReal.ofReal
        (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2)) := by
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
          (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2)) := by
        simp only [w]
        rw [if_pos ⟨h1, h2, h3⟩]
      have ha : a m = ENNReal.ofReal (q ^ ((1 / 2 - e) * (m : ℝ))) := by
        simp only [a]
        rw [if_pos h1]
      have hb : b n = ENNReal.ofReal (q ^ ((1 / 2 - e) * (-(n : ℝ)))) := by
        simp only [b]
        rw [if_pos h3]
      have hnn1 : 0 ≤ A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2) := by positivity
      have hnn2 : 0 ≤ A * q ^ L := by positivity
      have hnn3 : 0 ≤ q ^ ((1 / 2 - e) * (m : ℝ)) := by positivity
      show w (m, n) * μ (S m n) ≤ ENNReal.ofReal (A * q ^ L) * (a m * b n * c)
      rw [hw, ha, hb]
      calc ENNReal.ofReal (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2)) * μ (S m n)
          ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2)) *
              (ENNReal.ofReal (q ^ (L - n)) * c) := by
            gcongr
            exact hμ m n h2
        _ = ENNReal.ofReal (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2) * q ^ (L - n))
              * c := by
            rw [ENNReal.ofReal_mul hnn1]
            ring
        _ = ENNReal.ofReal (A * q ^ L * q ^ ((1 / 2 - e) * (m : ℝ)) * q ^ ((1 / 2 - e) * (-(n : ℝ)))) * c := by
            rw [shell_exponent_identity q A e L m n hq]
        _ = ENNReal.ofReal (A * q ^ L) *
              (ENNReal.ofReal (q ^ ((1 / 2 - e) * (m : ℝ))) * ENNReal.ofReal (q ^ ((1 / 2 - e) * (-(n : ℝ)))) * c) := by
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

open Ad3 Ad3.LFS in

theorem gInt2 (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2) :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (V' : Submodule ℂ (GL (Fin 2) F → ℂ)), WhittakerModelGL2 ψ ν ν⁻¹ V' → ∀ W' ∈ V',
    ∀ R : ℝ, ∃ C : ℝ, ∀ t₁ t₂ : Fˣ,
      Integrable ((om R t₂).indicator fun k => ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ))
        (hG ψ) ∧
      ∫ k, (om R t₂).indicator (fun k => ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ)) k ∂hG ψ ≤
        C * (modulus (t₁ : F) : ℝ) ^ e * (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ) := by
  intro F _ _ _ _ _ _ ψ ν V' H W' hW' R
  classical
  have hδ : 0 < 1 / 2 - e := by linarith
  obtain ⟨C, B, hCB⟩ := H.bound W' hW' (1 / 2 - e) hδ
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
      ‖W' (dg2 a 1 * κ)‖ ≤ C₁ * (modulus (a : F) : ℝ) ^ e := by
    intro a κ hκ
    have h := (hCB a κ hκ).1
    rw [show (1 / 2 - (1 / 2 - e) : ℝ) = e by ring] at h
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
  set r : ℝ := q ^ (-(1 / 2 - e) : ℝ) with hr
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  set D : ℝ := 1 - r with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hqL : 0 < q ^ L := zpow_pos hq0 L
  refine ⟨C₁ * q ^ L * ((q ^ L) ^ (1 / 2 - e) / D) ^ 2 * Kμ.toReal, fun t₁ t₂ => ?_⟩
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
  set A : ℝ := C₁ * (σ / τ) ^ e with hA
  have hA0 : 0 ≤ A := by positivity
  set T₁r : ℝ := (q ^ L) ^ (1 / 2 - e) / D with hT₁r
  set T₂r : ℝ := (q ^ L / τ) ^ (1 / 2 - e) / D with hT₂r
  have hT₁ : (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (m : ℝ))) else 0)) ≤ ENNReal.ofReal T₁r := by
    have h := GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div q (1 / 2 - e) (q ^ L) hq hδ hqL
    refine le_of_eq_of_le (tsum_congr fun m => ?_) h
    simp only [zpow_le_zpow_iff_right₀ hq]
  have hT₂ : (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (-(n : ℝ)))) else 0)) ≤ ENNReal.ofReal T₂r := by
    have h := GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div q (1 / 2 - e) (q ^ L / τ) hq hδ (div_pos hqL hτ)
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine le_of_eq_of_le (tsum_congr fun m => ?_) h
    simp only [Equiv.neg_apply, neg_neg, Int.cast_neg]
    have e : τ * q ^ m ≤ q ^ L ↔ q ^ m ≤ q ^ L / τ := by rw [le_div_iff₀ hτ, mul_comm]
    simp only [e]
  set S : ℤ → ℤ → Set (GL (Fin 2) F) := fun m n => {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ q ^ (L - m) ∧
    ∃ κ ∈ GLnLocal.integralGL F 2, g = uni2 x * dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} with hS
  set Φ : GL (Fin 2) F → ℝ≥0∞ := fun g => ENNReal.ofReal (f g⁻¹) with hΦ
  have hcov : ∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧
      Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2)) := by
    intro g hg
    have hom : g⁻¹ ∈ om R t₂ := by
      by_contra h
      exact hg (by simp [hΦ, hf, h])
    obtain ⟨x, m, n, κ, hκ, rfl⟩ := GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two F g
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.CompanionTheory.LFCoords.coords F x m n L κ R t₂ hκ hRL hom
    refine ⟨m, n, h1, h2, h4, ⟨x, h3, κ, hκ, rfl⟩, ENNReal.ofReal_le_ofReal ?_⟩
    rw [hf, Set.indicator_of_mem hom, inv_inv]
    have hw := whittaker_bound_iwasawa e F ψ W' C₁ hpsi hcen hbound t₁ t₂ (unifUnit F ^ m) (unifUnit F ^ n) x κ hκ
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
    have hdetg := GlobalTheory.CompanionTheory.LFGInt2.modulus_det_iwasawa_inv F x (unifUnit F ^ m) (unifUnit F ^ n) κ hκ
    rw [hM] at hw
    rw [hdetg, hu, hu, mul_inv, ← Real.rpow_neg hq0.le, ← Real.rpow_neg hq0.le, neg_neg, neg_neg,
      ← Real.rpow_add hq0, ← Real.rpow_mul hq0.le]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hq0.le] at hw
    have e2 : ((m : ℝ) + n) * (1 / 2) = ((m : ℝ) + n) / 2 := by ring
    rw [e2, hA, mul_assoc C₁]
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  have hmain := lintegral_le_of_shells e (hG ψ) q A τ L Kμ _ _ S Φ hq hA0 hτ
    (fun m n => (GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume F (hG ψ) m n L).1.measurableSet)
    (fun m n hn => (GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume F (hG ψ) m n L).2 hn)
    hT₁ hT₂ hcov
  have hinvl : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ = ∫⁻ g, Φ g ∂hG ψ :=
    ((Measure.measurePreserving_inv (hG ψ)).lintegral_comp hfm.ennreal_ofReal).symm
  set Rr : ℝ := C₁ * q ^ L * ((q ^ L) ^ (1 / 2 - e) / D) ^ 2 * Kμ.toReal * σ ^ e * τ ^ (-(1 / 2) : ℝ) with hRr
  have hRr0 : 0 ≤ Rr := by positivity
  have hfin : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ ≤ ENNReal.ofReal Rr := by
    rw [hinvl]
    refine hmain.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hKfin, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hw0 : 0 < τ ^ e := Real.rpow_pos_of_pos hτ _
    have hw1 : 0 < τ ^ (1 / 2 - e) := Real.rpow_pos_of_pos hτ _
    have hw2 : τ ^ (-(1 / 2) : ℝ) = (τ ^ e * τ ^ (1 / 2 - e))⁻¹ := by
      rw [← Real.rpow_add hτ, ← Real.rpow_neg hτ.le]
      congr 1
      ring
    rw [hRr, hA, hT₁r, hT₂r, hw2, Real.div_rpow hσ.le hτ.le, Real.div_rpow hqL.le hτ.le]
    field_simp
  refine ⟨⟨hfm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)]
    exact hfin.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hRr0 hfin

theorem rpow_torus (e : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a * b) ^ (1 / 2 : ℝ) * (a ^ e * b ^ (-(1 / 2) : ℝ)) = a ^ (1 / 2 + e) := by
  rw [Real.mul_rpow ha.le hb.le, Real.rpow_neg hb.le, Real.rpow_add ha]
  have hb' : b ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  field_simp

open Ad3 Ad3.LFS in

theorem gTor (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2) :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∃ C : ℝ, ∀ t₁ t₂ : Fˣ, ‖Wp ψ W' Φ (dg t₁ t₂ 1)‖ ≤ C * (modulus (t₁ : F) : ℝ) ^ (1 / 2 + e) := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hyp
  obtain ⟨hs, hu, ⟨V', hV, hW⟩, hΦ⟩ := id hyp
  obtain ⟨C₁, R, h1⟩ := GlobalTheory.CompanionTheory.LFFour.gFour F ψ hs Φ hΦ
  obtain ⟨C₂, h2⟩ := gInt2 e he0 he1 F ψ ν V' hV W' hW R
  refine ⟨max C₁ 0 * max C₂ 0, fun t₁ t₂ => ?_⟩
  obtain ⟨hint, hle⟩ := h2 t₁ t₂
  have hm1 : 0 < (modulus (t₁ : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos t₁.ne_zero
  have hm2 : 0 < (modulus (t₂ : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos t₂.ne_zero
  have hC₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hC₂ : 0 ≤ max C₂ 0 := le_max_right _ _
  set G : GL (Fin 2) F → ℝ := (om R t₂).indicator fun k =>
    ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ)
    with hGd
  have hG0 : ∀ k, 0 ≤ G k := fun k =>
    Set.indicator_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)) k
  have hpt : ∀ k : GL (Fin 2) F,
      ‖W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
        pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
          (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j)‖ ≤
        max C₁ 0 * G k := by
    intro k
    by_cases hp : pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
        (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) = 0
    · rw [hp, mul_zero, norm_zero]
      exact mul_nonneg hC₁ (hG0 k)
    · obtain ⟨hb, hsup⟩ := h1 (k : Matrix (Fin 2) (Fin 2) F)
        (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j)
      obtain ⟨hk, hξ⟩ := hsup hp
      have hmem : k ∈ om R t₂ := ⟨hk, hξ⟩
      have hGk : G k = ‖W' (dg2 t₁ t₂ * k⁻¹)‖ *
          (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) := by
        rw [hGd, Set.indicator_of_mem hmem]
      rw [norm_mul, norm_mul, GlobalTheory.CompanionTheory.LFTor.norm_mp_half, ← hGk, mul_comm]
      exact mul_le_mul ((hb).trans (le_max_left _ _)) le_rfl
        (by rw [hGk]; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)) hC₁
  have hbound : ‖∫ k, W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
        pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
          (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) ∂hG ψ‖ ≤
      max C₁ 0 * (max C₂ 0 * ((modulus (t₁ : F) : ℝ) ^ e *
        (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ))) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono := integral_mono_of_nonneg (μ := hG ψ)
      (Filter.Eventually.of_forall fun k => norm_nonneg _)
      (hint.const_mul (max C₁ 0)) (Filter.Eventually.of_forall hpt)
    refine hmono.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hC₁
    refine hle.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (Real.rpow_nonneg hm1.le _) (Real.rpow_nonneg hm2.le _))
  rw [GlobalTheory.CompanionTheory.LFGTorus.gtorus F ψ ν W' Φ hyp t₁ t₂, norm_mul, GlobalTheory.CompanionTheory.LFTor.norm_mp_half, Units.val_mul, GroundTheory.LocalField.modulus_mul,
    NNReal.coe_mul]
  calc _ ≤ ((modulus (t₁ : F) : ℝ) * modulus (t₂ : F)) ^ (1 / 2 : ℝ) *
        (max C₁ 0 * (max C₂ 0 * ((modulus (t₁ : F) : ℝ) ^ e *
          (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) _)
    _ = max C₁ 0 * max C₂ 0 * (((modulus (t₁ : F) : ℝ) * modulus (t₂ : F)) ^ (1 / 2 : ℝ) *
          ((modulus (t₁ : F) : ℝ) ^ e * (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ))) := by ring
    _ = _ := by rw [rpow_torus e hm1 hm2]

open Ad3 Ad3.LFS in
open scoped Pointwise in

theorem gK (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2) :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∃ C : ℝ, ∀ t₁ t₂ : Fˣ, ∀ k ∈ GLnLocal.integralGL F 3,
      ‖Wp ψ W' Φ (dg t₁ t₂ 1 * k)‖ ≤ C * (modulus (t₁ : F) : ℝ) ^ (1 / 2 + e) := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hH
  obtain ⟨U, hU⟩ := GlobalTheory.CompanionTheory.LFSmooth.smoothW F ψ ν W' Φ hH
  have hT := GlobalTheory.CompanionTheory.LFTrans.sTrans
  have hcov : ((GLnLocal.integralGL F 3 : Subgroup (GL (Fin 3) F)) : Set (GL (Fin 3) F)) ⊆
      ⋃ k : GL (Fin 3) F, k • (U : Set (GL (Fin 3) F)) := by
    intro k _
    exact Set.mem_iUnion.2 ⟨k, 1, U.one_mem, by simp⟩
  obtain ⟨t, ht⟩ := (GLnLocal.isCompact_integralGL F 3).elim_finite_subcover
    (fun k : GL (Fin 3) F => k • (U : Set (GL (Fin 3) F))) (fun k => U.isOpen.smul k) hcov
  have hC : ∀ k : GL (Fin 3) F, ∃ C : ℝ, ∀ t₁ t₂ : Fˣ,
      ‖Wp ψ W' (rtr k Φ) (dg t₁ t₂ 1)‖ ≤ C * (modulus (t₁ : F) : ℝ) ^ (1 / 2 + e) := fun k =>
    gTor e he0 he1 F ψ ν W' (rtr k Φ) ⟨hH.1, hH.2.1, hH.2.2.1, (hT F ψ W' Φ k hH.2.2.2).1⟩
  choose C hC using hC
  refine ⟨∑ k ∈ t, max (C k) 0, fun a b k hk => ?_⟩
  obtain ⟨ki, hki, hmem⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨u, hu, rfl⟩ := hmem
  have hW : Wp ψ W' Φ (dg a b 1 * (ki • u)) = Wp ψ W' (rtr ki Φ) (dg a b 1) := by
    rw [smul_eq_mul, ← mul_assoc, hU _ u hu]
    exact congrFun (hT F ψ W' Φ ki hH.2.2.2).2 _
  have hnn : 0 ≤ (modulus (a : F) : ℝ) ^ (1 / 2 + e) := by positivity
  have hle : C ki ≤ ∑ k ∈ t, max (C k) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun k => max (C k) 0)
      (fun _ _ => le_max_right _ _) hki)
  rw [hW]
  exact (hC ki a b).trans (mul_le_mul_of_nonneg_right hle hnn)

theorem dg_eq_central {F : Type} [Field F] (t₁ t₂ t₃ : Fˣ) :
    Ad3.dg t₁ t₂ t₃ = Ad3.dg t₃ t₃ t₃ * Ad3.dg (t₁ / t₃) (t₂ / t₃) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp

end GlobalTheory.CompanionTheory.LFTempered

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

namespace GlobalTheory.CompanionTheory.LFTempered

theorem temperedBoundGL3_of_lift : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ), LFS.Hyp ψ ν W' Φ → TemperedBoundGL3 (LFS.Wp ψ W' Φ) := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hH
  obtain ⟨U, hU⟩ := GlobalTheory.CompanionTheory.LFSmooth.smoothW F ψ ν W' Φ hH
  refine ⟨?_, fun ε h0 h1 => ?_⟩
  · refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨{x | g⁻¹ * x ∈ U}, U.isOpen.preimage (continuous_const.mul continuous_id), by simp [U.one_mem],
      fun x hx => ?_⟩
    have := hU g _ hx
    simpa using this
  · obtain ⟨C, hC⟩ := gK (1 / 2 - ε) (by linarith) (by linarith) F ψ ν W' Φ hH
    obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.LFSupp.sSupp F ψ hH.1 (LFS.Wp ψ W' Φ)
      (GlobalTheory.CompanionTheory.LFPsi.sPsiW F ψ ν W' Φ hH) ⟨U, hU⟩
    refine ⟨C, B, fun t₁ t₂ t₃ k hk => ?_⟩
    have hcen : LFS.Wp ψ W' Φ (dg t₁ t₂ t₃ * k) = LFS.Wp ψ W' Φ (dg (t₁ / t₃) (t₂ / t₃) 1 * k) := by
      rw [dg_eq_central t₁ t₂ t₃, mul_assoc]
      exact GlobalTheory.CompanionTheory.LFCen.scenW F ψ ν W' Φ hH t₃ _
    rw [hcen]
    refine ⟨?_, fun hne => ?_⟩
    · have h := hC (t₁ / t₃) (t₂ / t₃) k hk
      rwa [show (1 / 2 + (1 / 2 - ε) : ℝ) = 1 - ε by ring] at h
    · have e1 : t₁ / t₂ * (t₂ / t₃) = t₁ / t₃ := div_mul_div_cancel _ _ _
      have := hB (t₁ / t₂) (t₂ / t₃) k hk (by rwa [e1])
      exact this

end GlobalTheory.CompanionTheory.LFTempered
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.temperedBoundGL3_lifted_whittaker : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ), LFS.Hyp ψ ν W' Φ → TemperedBoundGL3 (LFS.Wp ψ W' Φ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFTempered.temperedBoundGL3_of_lift
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

noncomputable section

namespace GlobalTheory.CompanionTheory.DualHol

theorem diag_eq_central_mul {F : Type} [Field F] (x y : Fˣ) : dg2 x y = dg2 y y * dg2 (x / y) 1 := by
  have hy : (y : F) ≠ 0 := y.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem temperedBoundGL2_of_whittaker : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (V : Submodule ℂ (GL (Fin 2) F → ℂ)), IsUnit1 μ₁ → IsUnit1 μ₂ → WhittakerModelGL2 ψ μ₁ μ₂ V → ∀ W ∈ V, TemperedBoundGL2 W := by
  intro F _ _ _ _ _ _ ψ μ₁ μ₂ V h₁ h₂ H W hW
  obtain ⟨U, hU⟩ := H.smooth W hW
  have hWc : Continuous W := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨{x | g⁻¹ * x ∈ U}, U.isOpen.preimage (continuous_const.mul continuous_id), by simp [U.one_mem],
      fun x hx => ?_⟩
    have := hU g _ hx
    simpa using this
  refine ⟨hWc.measurable, fun ε h0 _ => ?_⟩
  obtain ⟨C, B, hb⟩ := H.bound W hW ε h0
  refine ⟨C, B, fun x y k hk => ?_⟩
  have e : W (dg2 x y * k) = ((μ₁ y * μ₂ y : ℂˣ) : ℂ) * W (dg2 (x / y) 1 * k) := by
    rw [diag_eq_central_mul, mul_assoc, H.cen W hW]
  have hn : ‖((μ₁ y * μ₂ y : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_mul, norm_mul, h₁.2, h₂.2, one_mul]
  have hne : ((μ₁ y * μ₂ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  refine ⟨?_, fun hz => ?_⟩
  · rw [e, norm_mul, hn, one_mul]
    exact (hb (x / y) k hk).1
  · refine (hb (x / y) k hk).2 fun h0' => hz ?_
    rw [e, h0', mul_zero]

end GlobalTheory.CompanionTheory.DualHol
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.temperedBoundGL2_of_induced : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (V : Submodule ℂ (GL (Fin 2) F → ℂ)), IsUnit1 μ₁ → IsUnit1 μ₂ → WhittakerModelGL2 ψ μ₁ μ₂ V → ∀ W ∈ V, TemperedBoundGL2 W := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DualHol.temperedBoundGL2_of_whittaker
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_whittaker_eq_godement_local : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ → ∀ Φ : F × F → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → ∃ φ ∈ GodementSectionLocal.schwartzBruhat2 F, GL2LocalData.WcS χ c₁ c₂ Φ = W2 χ c₂ c₁ φ := by
  first | exact @GlobalTheory.CompanionTheory.WcSplit.compact_whittaker_eq_godement | exact GlobalTheory.CompanionTheory.WcSplit.compact_whittaker_eq_godement | (intros; apply GlobalTheory.CompanionTheory.WcSplit.compact_whittaker_eq_godement <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.WcB

theorem Wc_continuousOn_of_wS : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ), Φ ∈ GL2LocalData.SBc F E c → ∀ A : Set (GL (Fin 2) F), ContinuousOn (fun p : GL (Fin 2) F × Eˣ => wS χ σ μ lam c Φ p.1 p.2) {p | p.1 ∈ A} → ContinuousOn (GL2LocalData.Wc χ σ μ lam c Φ) (A ∩ {g | ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det}) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ σ μ lam c Φ hΦ A hc g₀ hg₀
  obtain ⟨hgA, t₀, ht₀⟩ := hg₀
  have key : ∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det →
      GL2LocalData.Wc χ σ μ lam c Φ g = wS χ σ μ lam c Φ g t := by
    intro g t ht
    have h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det := ⟨t, ht⟩
    rw [Wc_eq_wS χ σ μ lam c Φ g h]
    exact GlobalTheory.T.weil_whittaker_measure_independence F E χ σ μ lam c Φ hΦ g _ t (h.choose_spec.trans ht.symm)
  rw [ContinuousWithinAt, key g₀ t₀ ht₀]
  intro V hV
  have h2 := (hc (g₀, t₀) hgA) hV
  obtain ⟨u, hu, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 h2
  rw [nhds_prod_eq] at hu
  obtain ⟨U, hU, T, hT, hprod⟩ := Filter.mem_prod_iff.1 hu
  have hev := GlobalTheory.T.norm_image_neighbourhood_eventually F E t₀ T hT
  rw [ht₀] at hev
  have hdet : Continuous (fun g : GL (Fin 2) F => (g.val).det) :=
    Continuous.matrix_det Units.continuous_val
  have hev' : ∀ᶠ g in 𝓝 g₀, ∃ t ∈ T, Algebra.norm F (t : E) = (g.val).det :=
    hdet.continuousAt.eventually hev
  refine Filter.mem_map.2 ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, mem_nhdsWithin_of_mem_nhds hev',
    self_mem_nhdsWithin] with g hgU hgt hgS
  obtain ⟨t, htT, ht⟩ := hgt
  show GL2LocalData.Wc χ σ μ lam c Φ g ∈ V
  rw [key g t ht]
  have hp : ((g, t) : GL (Fin 2) F × Eˣ) ∈ u ∩ {p | p.1 ∈ A} :=
    ⟨hprod (Set.mk_mem_prod hgU htT), hgS.1⟩
  exact hsub hp

end GlobalTheory.CompanionTheory.WcB
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_central_twist : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ), Φ ∈ GL2LocalData.SBc F E c → ∀ A : Set (GL (Fin 2) F), ContinuousOn (fun p : GL (Fin 2) F × Eˣ => wS χ σ μ lam c Φ p.1 p.2) {p | p.1 ∈ A} → ContinuousOn (GL2LocalData.Wc χ σ μ lam c Φ) (A ∩ {g | ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det}) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WcB.Wc_continuousOn_of_wS
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.WhitOffBorel

theorem real_bound {X Y δ p q M I C₀ L : ℝ} (hX : 0 < X) (hY : 0 < Y) (hδ : 0 < δ) (hp : 0 < p)
    (hM : 0 < M) (hI : 0 ≤ I) (hL : 0 ≤ L)
    (h1 : I * max 1 (q / p) ≤ C₀) (h2 : δ ≤ M * max p q) :
    L * (X * Y * δ) ^ (1 / 2 : ℝ) * (Y * p)⁻¹ * I ≤
      (L * (Real.sqrt δ)⁻¹ * |C₀| * M) * (X / Y) ^ (1 / 2 : ℝ) := by
  have hXY : 0 < X / Y := div_pos hX hY
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (X / Y) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = Real.sqrt δ := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 hXY
  have hd0 : 0 < d := hd ▸ Real.sqrt_pos.2 hδ
  have hss : s * s = X / Y := by rw [hs]; exact Real.mul_self_sqrt hXY.le
  have hdd : d * d = δ := by rw [hd]; exact Real.mul_self_sqrt hδ.le
  have e : (X * Y * δ) ^ (1 / 2 : ℝ) = s * d * Y := by
    rw [← Real.sqrt_eq_rpow]
    have : X * Y * δ = (s * d * Y) ^ 2 := by
      have : (s * d * Y) ^ 2 = (s * s) * (d * d) * Y ^ 2 := by ring
      rw [this, hss, hdd]; field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  rw [e, ← Real.sqrt_eq_rpow (X / Y), ← hs, ← hd]
  have hmax : p * max 1 (q / p) = max p q := by
    rw [mul_max_of_nonneg _ _ hp.le, mul_one, mul_div_cancel₀ _ hp.ne']
  have key : I * max p q ≤ |C₀| * p := by
    rw [← hmax]
    calc I * (p * max 1 (q / p)) = (I * max 1 (q / p)) * p := by ring
      _ ≤ |C₀| * p := mul_le_mul_of_nonneg_right (h1.trans (le_abs_self _)) hp.le
  have key2 : d * d * I ≤ |C₀| * M * p := by
    rw [hdd]
    calc δ * I ≤ (M * max p q) * I := mul_le_mul_of_nonneg_right h2 hI
      _ = M * (I * max p q) := by ring
      _ ≤ M * (|C₀| * p) := mul_le_mul_of_nonneg_left key hM.le
      _ = |C₀| * M * p := by ring
  have key3 : d * I / p ≤ |C₀| * M / d := by
    rw [div_le_div_iff₀ hp hd0]
    calc d * I * d = d * d * I := by ring
      _ ≤ |C₀| * M * p := key2
  calc L * (s * d * Y) * (Y * p)⁻¹ * I = (L * s) * (d * I / p) := by
        field_simp
    _ ≤ (L * s) * (|C₀| * M / d) := mul_le_mul_of_nonneg_left key3 (by positivity)
    _ = L * d⁻¹ * |C₀| * M * s := by field_simp

theorem real_supp {X Y δ p q M R : ℝ} (hX : 0 < X) (hY : 0 < Y) (hδ : 0 < δ) (hp : 0 < p)
    (hq : 0 ≤ q) (hpM : p ≤ M) (hqM : q ≤ M)
    (h : (X * Y * δ / (Y * p)) ^ 2 * (X * Y * δ)⁻¹ ≤ R * max 1 ((q / p) ^ 2)) :
    X / Y ≤ max 1 (|R| * M ^ 2 / δ) := by
  have e : (X * Y * δ / (Y * p)) ^ 2 * (X * Y * δ)⁻¹ = (X / Y) * δ / p ^ 2 := by
    field_simp
  rw [e] at h
  have hM : 0 < M := hp.trans_le hpM
  have hm : max 1 ((q / p) ^ 2) ≤ M ^ 2 / p ^ 2 := by
    refine max_le ?_ ?_
    · rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hp.le hpM 2
    · rw [div_pow]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hq hqM 2) (by positivity)
  have h3 : (X / Y) * δ / p ^ 2 ≤ |R| * (M ^ 2 / p ^ 2) :=
    h.trans ((mul_le_mul_of_nonneg_right (le_abs_self R) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hm (abs_nonneg R)))
  have h4 : (X / Y) * δ ≤ |R| * M ^ 2 := by
    have hp2 : 0 < p ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right h3 hp2.le
    have e1 : (X / Y) * δ / p ^ 2 * p ^ 2 = (X / Y) * δ := by field_simp
    have e2 : |R| * (M ^ 2 / p ^ 2) * p ^ 2 = |R| * M ^ 2 := by field_simp
    rwa [e1, e2] at this
  exact le_max_of_le_right ((le_div_iff₀ hδ).2 h4)

theorem whittaker_off_borel : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ : E → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → ∀ h₀ : GL (Fin 2) F, ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ (x y : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, (k * h₀).val 1 0 ≠ 0 → ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖ ≤ C * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) ∧ (GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) ≠ 0 → (modulus ((x / y : Fˣ) : F) : ℝ) ≤ B) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχc hχ1 σ hσ μ _ lam c hc Φ hΦl hΦc h₀
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.weil_whittaker_nonvanishing_character F E χ hχc hχ1 σ hσ μ Φ hΦl hΦc
  obtain ⟨R, hR⟩ := GlobalTheory.T.weil_whittaker_measurability F E χ hχc hχ1 σ hσ μ Φ hΦl hΦc
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.compact_translate_entries_bounded F h₀
  have hδ₀ : (0 : ℝ) < (modulus (h₀.val).det : ℝ) := by
    have hne : (h₀.val).det ≠ 0 := by
      have := (Matrix.isUnits_det_units h₀)
      exact this.ne_zero
    exact_mod_cast modulus_pos hne
  refine ⟨‖lam‖ * (Real.sqrt (modulus (h₀.val).det : ℝ))⁻¹ * |C₀| * M,
    max 1 (|R| * M ^ 2 / (modulus (h₀.val).det : ℝ)), by positivity,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro x y k hk hne
  obtain ⟨hent, hdet⟩ := hM k hk
  rw [mul_assoc (dg2 x y) k h₀]
  obtain ⟨m, hm⟩ : ∃ m, m = k * h₀ := ⟨_, rfl⟩
  rw [← hm] at hne hent hdet ⊢
  obtain ⟨g, hg⟩ : ∃ g, g = dg2 x y * m := ⟨_, rfl⟩
  rw [← hg]
  have g10 : g.val 1 0 = y * m.val 1 0 := by
    simp [hg, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have g11 : g.val 1 1 = y * m.val 1 1 := by
    simp [hg, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have gdet : (g.val).det = x * y * (m.val).det := by
    rw [hg, Units.val_mul, Matrix.det_mul]
    simp [dg2, Matrix.det_fin_two_of]
  have hXp : (0 : ℝ) < (modulus (x : F) : ℝ) := by exact_mod_cast modulus_pos x.ne_zero
  have hYp : (0 : ℝ) < (modulus (y : F) : ℝ) := by exact_mod_cast modulus_pos y.ne_zero
  have hpp : (0 : ℝ) < (modulus (m.val 1 0) : ℝ) := by exact_mod_cast modulus_pos hne
  have hxy : (modulus ((x / y : Fˣ) : F) : ℝ) = (modulus (x : F) : ℝ) / (modulus (y : F) : ℝ) := by
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, modulus_mul, modulus_inv]
    push_cast
    rw [div_eq_mul_inv]
  have mg10 : (modulus (g.val 1 0) : ℝ) = (modulus (y : F) : ℝ) * (modulus (m.val 1 0) : ℝ) := by
    rw [g10, modulus_mul]; push_cast; rfl
  have mgdet : (modulus (g.val).det : ℝ) =
      (modulus (x : F) : ℝ) * (modulus (y : F) : ℝ) * (modulus (h₀.val).det : ℝ) := by
    rw [gdet, modulus_mul, modulus_mul, hdet]; push_cast; rfl
  have hg10 : g.val 1 0 ≠ 0 := by
    rw [g10]; exact mul_ne_zero y.ne_zero hne
  have mκ : (modulus (g.val 1 1 / g.val 1 0) : ℝ) =
      (modulus (m.val 1 1) : ℝ) / (modulus (m.val 1 0) : ℝ) := by
    rw [g10, g11, div_eq_mul_inv, modulus_mul, modulus_inv, modulus_mul, modulus_mul]
    push_cast
    field_simp
  by_cases hW : GL2LocalData.Wc χ σ μ lam c Φ g = 0
  · rw [hW, norm_zero]
    refine ⟨by positivity, fun h => absurd rfl h⟩
  obtain ⟨t, htN, hval⟩ := GlobalTheory.T.weil_whittaker_galois_invariance F E χ σ hσ μ lam c hc Φ g hg10 hW
  have hI0 : gaussI χ μ Φ (g.val 1 1 / g.val 1 0)
      (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hval
    exact hW (norm_eq_zero.1 hval)
  refine ⟨?_, fun _ => ?_⟩
  · rw [hval, mgdet, mg10, hxy]
    refine GlobalTheory.CompanionTheory.WhitOffBorel.real_bound (q := (modulus (m.val 1 1) : ℝ)) hXp hYp hδ₀ hpp hM0 (norm_nonneg _) (norm_nonneg _) ?_ ?_
    · have := hC₀ (g.val 1 1 / g.val 1 0) (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹)
      rwa [mκ] at this
    · have hpm : (modulus (m.val 1 0) : ℝ) ≤ max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ) :=
        le_max_left _ _
      have hqm : (modulus (m.val 1 1) : ℝ) ≤ max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ) :=
        le_max_right _ _
      have hn1 : (modulus (-1 : F) : ℝ) ≤ 1 := by
        exact_mod_cast (modulus_le_one_iff (K := F)).2 (neg_mem (one_mem _))
      have t1 : (modulus (m.val 0 0 * m.val 1 1) : ℝ) ≤
          M * max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ) := by
        rw [modulus_mul]; push_cast
        exact mul_le_mul (hent 0 0) hqm (NNReal.coe_nonneg _) hM0.le
      have t2 : (modulus (-(m.val 0 1 * m.val 1 0)) : ℝ) ≤
          M * max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ) := by
        have e : -(m.val 0 1 * m.val 1 0) = (-1) * (m.val 0 1 * m.val 1 0) := by ring
        rw [e, modulus_mul, modulus_mul]; push_cast
        calc (modulus (-1 : F) : ℝ) * ((modulus (m.val 0 1) : ℝ) * (modulus (m.val 1 0) : ℝ))
            ≤ 1 * ((modulus (m.val 0 1) : ℝ) * (modulus (m.val 1 0) : ℝ)) :=
              mul_le_mul_of_nonneg_right hn1 (by positivity)
          _ = (modulus (m.val 0 1) : ℝ) * (modulus (m.val 1 0) : ℝ) := one_mul _
          _ ≤ _ := mul_le_mul (hent 0 1) hpm (NNReal.coe_nonneg _) hM0.le
      have hd : (m.val).det = m.val 0 0 * m.val 1 1 + -(m.val 0 1 * m.val 1 0) := by
        rw [Matrix.det_fin_two]; ring
      have hdd : (modulus (h₀.val).det : ℝ) = (modulus (m.val).det : ℝ) := by rw [hdet]
      rw [hdd, hd]
      exact (GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max _ _).trans (max_le t1 t2)
  · rw [hxy]
    have hs := hR _ _ hI0
    have mξ : (modulus (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹) : ℝ) =
        ((modulus (x : F) : ℝ) * (modulus (y : F) : ℝ) * (modulus (h₀.val).det : ℝ) /
          ((modulus (y : F) : ℝ) * (modulus (m.val 1 0) : ℝ))) ^ 2 *
        ((modulus (x : F) : ℝ) * (modulus (y : F) : ℝ) * (modulus (h₀.val).det : ℝ))⁻¹ := by
      rw [modulus_mul, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap (K := F), modulus_inv,
        ← GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) (t : E), htN, div_eq_mul_inv,
        modulus_mul, modulus_inv]
      push_cast
      rw [mgdet, mg10, div_eq_mul_inv]
    rw [mξ, mκ] at hs
    exact GlobalTheory.CompanionTheory.WhitOffBorel.real_supp hXp hYp hδ₀ hpp (NNReal.coe_nonneg _) (hent 1 0) (hent 1 1) hs

end GlobalTheory.CompanionTheory.WhitOffBorel
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_nontrivial_character_extension : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ : E → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → ∀ h₀ : GL (Fin 2) F, ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ (x y : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, (k * h₀).val 1 0 ≠ 0 → ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖ ≤ C * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) ∧ (GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) ≠ 0 → (modulus ((x / y : Fˣ) : F) : ℝ) ≤ B) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WhitOffBorel.whittaker_off_borel
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.WcB

section Meas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)]

theorem measurable_indicator_of_continuousOn {f : GL (Fin 2) F → ℂ} {s : Set (GL (Fin 2) F)}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) : Measurable (s.indicator f) := by
  classical
  have h := ContinuousOn.measurable_piecewise (f := f) (g := fun _ => (0 : ℂ)) hf
    continuousOn_const hs
  have e : s.piecewise f (fun _ => (0 : ℂ)) = s.indicator f := by
    ext g
    by_cases hg : g ∈ s <;> simp [Set.piecewise, Set.indicator, hg]
  rwa [e] at h

theorem measurable_Wc (χ : AddChar F Circle) (hχ : Continuous χ) (hal : Continuous (algebraMap F E))
    (σ : E ≃ₐ[F] E) (hσ : σ ≠ AlgEquiv.refl) (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ)
    (c : Eˣ →* ℂˣ) (hc : IsUnit1 c) (Φ : E → ℂ) (hΦ : Φ ∈ GL2LocalData.SBc F E c) :
    Measurable (GL2LocalData.Wc χ σ μ lam c Φ) := by
  set Gp : Set (GL (Fin 2) F) := {g | ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det} with hGp
  have hdet : Continuous fun g : GL (Fin 2) F => (g.val).det :=
    Continuous.matrix_det Units.continuous_val
  have hent : Continuous fun g : GL (Fin 2) F => g.val 1 0 :=
    (continuous_id.matrix_elem 1 0).comp Units.continuous_val
  have hGo : IsOpen Gp := (GlobalTheory.T.isOpen_norm_image_units F E).1.preimage hdet
  have hA0 : IsClosed {g : GL (Fin 2) F | g.val 1 0 = 0} := isClosed_eq hent continuous_const
  have hA1 : IsOpen {g : GL (Fin 2) F | g.val 1 0 ≠ 0} := isOpen_ne_fun hent continuous_const
  have c1 : ContinuousOn (GL2LocalData.Wc χ σ μ lam c Φ) ({g : GL (Fin 2) F | g.val 1 0 ≠ 0} ∩ Gp) :=
    GlobalTheory.T.weil_whittaker_central_twist F E χ σ μ lam c Φ hΦ _
      (GlobalTheory.T.weil_whittaker_continuous_quadratic F E χ hχ hal σ hσ μ lam c hc Φ hΦ.1 hΦ.2.1)
  have c0 : ContinuousOn (GL2LocalData.Wc χ σ μ lam c Φ) ({g : GL (Fin 2) F | g.val 1 0 = 0} ∩ Gp) :=
    GlobalTheory.T.weil_whittaker_central_twist F E χ σ μ lam c Φ hΦ _
      (GlobalTheory.T.weil_whittaker_support_bound_quadratic F E χ σ μ lam c Φ hχ hal hc hΦ.1)
  have m1 := measurable_indicator_of_continuousOn c1 (hA1.measurableSet.inter hGo.measurableSet)
  have m0 := measurable_indicator_of_continuousOn c0 (hA0.measurableSet.inter hGo.measurableSet)
  have e : GL2LocalData.Wc χ σ μ lam c Φ =
      ({g : GL (Fin 2) F | g.val 1 0 ≠ 0} ∩ Gp).indicator (GL2LocalData.Wc χ σ μ lam c Φ) +
      ({g : GL (Fin 2) F | g.val 1 0 = 0} ∩ Gp).indicator (GL2LocalData.Wc χ σ μ lam c Φ) := by
    ext g
    by_cases hg : g ∈ Gp
    · by_cases h0 : g.val 1 0 = 0
      · simp [Set.indicator, hg, h0]
      · simp [Set.indicator, hg, h0]
    · have : GL2LocalData.Wc χ σ μ lam c Φ g = 0 := Wc_eq_zero χ σ μ lam c Φ g hg
      simp [Set.indicator, hg, this]
  rw [e]
  exact m1.add m0

end Meas

theorem temperedBoundGL2_compact_whittaker : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ h₀ : GL (Fin 2) F, TemperedBoundGL2 (fun g => GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c Φ (g * h₀)) := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ h2 hal σ hσ lam c hc Φ hΦ h₀
  haveI : ValuativeExtension F E := GlobalTheory.LBC.Inh.valuativeExtension hal
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  set μ := selfDualMeasure (GL2LocalData.chE E χ) with hμ
  have hmeas := measurable_Wc χ hχ hal σ hσ μ lam c hc Φ hΦ
  refine ⟨hmeas.comp (continuous_mul_right h₀).measurable, fun ε h0 h1 => ?_⟩
  obtain ⟨C0, B0, hC0, hB0, H0⟩ := GlobalTheory.T.weil_whittaker_diag_norm_le_sqrt_modulus_and_support F E χ σ μ lam c Φ hc hΦ.1 hΦ.2.1 h₀
  obtain ⟨C1, B1, hC1, hB1, H1⟩ := GlobalTheory.T.weil_whittaker_nontrivial_character_extension F E χ hχ hχ1 σ hσ μ lam c hc Φ hΦ.1 hΦ.2.1 h₀
  have hB : 0 < max B0 B1 := lt_max_of_lt_left hB0
  have hC : 0 ≤ max C0 C1 := le_max_of_le_left hC0
  refine ⟨max C0 C1 * (max B0 B1) ^ ε, max B0 B1, fun x y k hk => ?_⟩
  show ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖ ≤ _ ∧ (GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) ≠ 0 → _)
  have hr : 0 < (modulus ((x / y : Fˣ) : F) : ℝ) := by
    exact_mod_cast modulus_pos (Units.ne_zero _)
  have key : ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖ ≤
        max C0 C1 * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) ∧
      (GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) ≠ 0 → (modulus ((x / y : Fˣ) : F) : ℝ) ≤ max B0 B1) := by
    by_cases hz : (k * h₀).val 1 0 = 0
    · obtain ⟨a, b⟩ := H0 x y k hk hz
      exact ⟨a.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _)),
        fun h => (b h).trans (le_max_left _ _)⟩
    · obtain ⟨a, b⟩ := H1 x y k hk hz
      exact ⟨a.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _)),
        fun h => (b h).trans (le_max_right _ _)⟩
  refine ⟨?_, key.2⟩
  by_cases hW : GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) = 0
  · rw [hW, norm_zero]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hB.le _)) (Real.rpow_nonneg hr.le _)
  · have hle := key.2 hW
    have e : (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) =
        (modulus ((x / y : Fˣ) : F) : ℝ) ^ ε * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    have hpow : (modulus ((x / y : Fˣ) : F) : ℝ) ^ ε ≤ (max B0 B1) ^ ε :=
      Real.rpow_le_rpow hr.le hle h0.le
    calc ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖
        ≤ max C0 C1 * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) := key.1
      _ = max C0 C1 * ((modulus ((x / y : Fˣ) : F) : ℝ) ^ ε * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε)) := by
          rw [e]
      _ ≤ max C0 C1 * ((max B0 B1) ^ ε * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hr.le _)) hC
      _ = max C0 C1 * (max B0 B1) ^ ε * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε) := by ring

end GlobalTheory.CompanionTheory.WcB
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.temperedBoundGL2_quadratic_whittaker : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ h₀ : GL (Fin 2) F, TemperedBoundGL2 (fun g => GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c Φ (g * h₀)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WcB.temperedBoundGL2_compact_whittaker
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_galois_place_degree_two : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (v : Pl) (w : PlK K) (_ : w.asIdeal.LiesOver v.asIdeal) (σ : Kv K w ≃ₐ[Qv v] Kv K w), σ ≠ AlgEquiv.refl → Module.finrank (Qv v) (Kv K w) = 2 := by
  first | exact @GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl | exact GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl | (intros; apply GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

namespace GlobalTheory.CompanionTheory.DualHolMain

theorem isStd_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ψ : AddChar F Circle), IsStd ψ → IsStd ψ⁻¹ := by
  intro F _ _ _ _ ψ ⟨h1, h2, h3⟩
  have hinv : ∀ x, ψ⁻¹ x = (ψ x)⁻¹ := fun x => AddChar.inv_apply' ψ x
  refine ⟨?_, ?_, ?_⟩
  · have : (ψ⁻¹ : AddChar F Circle) = fun x => (ψ x)⁻¹ := by funext x; exact hinv x
    show Continuous (ψ⁻¹ : AddChar F Circle)
    rw [this]; exact h1.inv
  · exact inv_ne_one.2 h2
  · have : {n : ℤ | IsTrivialOn ψ⁻¹ n} = {n : ℤ | IsTrivialOn ψ n} := by
      ext n
      simp only [Set.mem_setOf_eq, IsTrivialOn, hinv, inv_eq_one]
    rw [← h3, addCharConductor, addCharConductor, this]

theorem isUnit1_cAt {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] : IsUnit1 (cAt c v w) := by
  refine ⟨?_, fun x => ?_⟩
  · exact (GroundTheory.Automorphic.GodementSection.continuous_localChar c w).comp
      (Continuous.units_map _ (continuous_adicCompletionMap v w))
  · simp only [cAt, MonoidHom.comp_apply]
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _

theorem main : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.HOLV K := by
  intro K _ _ hK D c v W hW Wt e hT
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
  have hν := D.unit v
  have hνi : IsUnit1 (D.ν v)⁻¹ := ⟨hν.1.inv, fun x => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hν.2, inv_one]⟩
  have hV := GlobalTheory.T.whittaker_induced_of_functional_equation GlobalTheory.T.functional_equation_generic (Qv v) (GP.psiF v) hψ (D.ν v) (D.ν v)⁻¹ hν hνi
  have h3 : TemperedBoundGL3 W := by
    refine TemperedBoundGL3.span ?_ hW
    rintro _ ⟨W', hW', Φ, hΦ, rfl⟩
    exact GlobalTheory.T.temperedBoundGL3_lifted_whittaker _ _ (D.ν v) _ _ ⟨hψ, hν, ⟨_, hV, hW'⟩, hΦ⟩
  have h2 : TemperedBoundGL2 Wt := by
    rcases hT with ⟨w₁, w₂, i₁, i₂, -, hm, -⟩ | ⟨w, i, -, σ, η, hσ, -, hm, -⟩
    · have hχ := isStd_inv _ _ hψ
      have u₁ := isUnit1_cAt c v w₁
      have u₂ := isUnit1_cAt c v w₂
      have hV' := GlobalTheory.T.whittaker_induced_of_functional_equation GlobalTheory.T.functional_equation_generic (Qv v) (GP.psiF v)⁻¹ hχ _ _ u₂ u₁
      refine TemperedBoundGL2.span ?_ hm
      rintro _ ⟨Φ, h1, h2, h₀, rfl⟩
      obtain ⟨φ, hφ, e⟩ := GlobalTheory.T.compact_whittaker_eq_godement_local _ _ hχ _ _ u₁ u₂ Φ h1 h2
      rw [e]
      exact GlobalTheory.T.temperedBoundGL2_of_induced _ _ _ _ _ u₂ u₁ hV' _ (hV'.stable _ (Submodule.subset_span ⟨φ, hφ, rfl⟩) h₀)
    · refine TemperedBoundGL2.span ?_ hm
      rintro _ ⟨Φ, hΦ, h₀, rfl⟩
      have hc : IsUnit1 (localChar c w) := ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => by
        rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _⟩
      have hχ := isStd_inv _ _ hψ
      exact GlobalTheory.T.temperedBoundGL2_quadratic_whittaker _ _ hχ.1 hχ.2.1 _ (GlobalTheory.T.nontrivial_galois_place_degree_two K hK v w i σ hσ)
        (continuous_adicCompletionMap v w) σ hσ _ _ hc Φ hΦ h₀
  exact GlobalTheory.T.differentiableOn_zetaGL3GL2_dual _ _ _ _ h3 h2

end GlobalTheory.CompanionTheory.DualHolMain
end
