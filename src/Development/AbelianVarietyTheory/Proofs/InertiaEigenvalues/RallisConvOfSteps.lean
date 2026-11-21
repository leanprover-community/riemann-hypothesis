import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermStronglyMeasurableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangiansStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisNonGraphLagrangianSumEqZeroCuspidal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

def lagFrame (W : HSp D) (Y : Lag W) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  let b := Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1
  (Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a,
    Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a)

theorem lagFrame_isLagFrame (W : HSp D) (Y : Lag W) : IsLagFrame W Y (lagFrame W Y) := by
  unfold IsLagFrame lagFrame
  have h : (Set.range fun j =>
      ((fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a) a j),
        (fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a) a j))) =
      (Y.1.subtype) '' Set.range (Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.RawLift

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem rallis_kernel_step : ∀ D : D7, KerAbs D → SWPair D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧ IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧ ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV = ((νV 𝓗).toReal : ℂ) * ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  intro D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  obtain ⟨lcV, scV, t2V⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  obtain ⟨lcW, scW, t2W⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (GA D W) := ⟨rfl⟩
  haveI := hS.haarV
  haveI := hS.haarW
  obtain ⟨hfin, hK⟩ := hKer ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ
  obtain ⟨B₁, hB₁⟩ := hK f₁ hf₁ φ₁ hφ₁ hc₁
  obtain ⟨B₂, hB₂⟩ := hK f₂ hf₂ φ₂ hφ₂ hc₂
  haveI : IsFiniteMeasure (νV.restrict 𝓗) := isFiniteMeasure_restrict.2 hfin
  have hk : ∀ f, IsThetaFunO ψ V W f → Continuous fun p : GA D V × GA D W => thetaKO om p.1 p.2 f :=
    fun f hf => hS.weil.om_cont f hf 0
  set μG := νW.restrict 𝓖 with hμG
  set μH := νV.restrict 𝓗 with hμH
  set F : GA D V → GA D W × GA D W → ℂ := fun h p =>
    thetaKO om h p.1 f₁ * star (φ₁ p.1) * (star (thetaKO om h p.2 f₂) * φ₂ p.2) with hF
  have hFc : Continuous (Function.uncurry F) := by
    have a1 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.1 f₁ :=
      (hk f₁ hf₁).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have a2 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.2 f₂ :=
      (hk f₂ hf₂).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
    have b1 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₁ q.2.1 :=
      hφ₁.cont.comp (continuous_fst.comp continuous_snd)
    have b2 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₂ q.2.2 :=
      hφ₂.cont.comp (continuous_snd.comp continuous_snd)
    exact (a1.mul b1.star).mul (a2.star.mul b2)
  have hFm : AEStronglyMeasurable (Function.uncurry F) (μH.prod (μG.prod μG)) := hFc.aestronglyMeasurable
  have hI1 : ∀ h, Integrable (fun g => thetaKO om h g f₁ * star (φ₁ g)) μG := by
    intro h
    refine ((hB₁ h).1.norm).mono' (((hk f₁ hf₁).comp (continuous_const.prodMk continuous_id)).mul
      hφ₁.cont.star).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simp [norm_mul]
  have hI2 : ∀ h, Integrable (fun g => star (thetaKO om h g f₂) * φ₂ g) μG := fun h => (hB₂ h).1
  have hFh : ∀ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h = ∫ p, F h p ∂(μG.prod μG) := by
    intro h
    rw [integral_prod_mul (fun g => thetaKO om h g f₁ * star (φ₁ g)) (fun g => star (thetaKO om h g f₂) * φ₂ g)]
    unfold upLift
    congr 1
    rw [← hμG]
    show (starRingEnd ℂ) _ = _
    rw [← integral_conj]
    congr 1
    funext g
    simp [Complex.star_def]
  have hB₁0 : 0 ≤ B₁ := le_trans (integral_nonneg fun g => by positivity) ((hB₁ 1).2)
  have hB₂0 : 0 ≤ B₂ := le_trans (integral_nonneg fun g => by positivity) ((hB₂ 1).2)
  have hnorm : ∀ h, ∫ p, ‖F h p‖ ∂(μG.prod μG) =
      (∫ g, ‖thetaKO om h g f₁‖ * ‖φ₁ g‖ ∂μG) * ∫ g, ‖thetaKO om h g f₂‖ * ‖φ₂ g‖ ∂μG := by
    intro h
    rw [← integral_prod_mul (fun g => ‖thetaKO om h g f₁‖ * ‖φ₁ g‖) (fun g => ‖thetaKO om h g f₂‖ * ‖φ₂ g‖)]
    congr 1
    funext p
    simp [hF, norm_mul]
  have hInt : Integrable (Function.uncurry F) (μH.prod (μG.prod μG)) := by
    rw [integrable_prod_iff hFm]
    refine ⟨ae_of_all _ fun h => (hI1 h).mul_prod (hI2 h), ?_⟩
    refine (integrable_const (B₁ * B₂)).mono' hFm.norm.integral_prod_right' (ae_of_all _ fun h => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hnorm h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (hB₁ h).2 (hB₂ h).2 (integral_nonneg fun g => by positivity) hB₁0
  have hsplit : ∀ (h : GA D V) (g : GA D W) (f : WO V W → ℂ), thetaKO om h g f = thetaKO om h 1 (om (1, g) f) := by
    intro h g f
    unfold thetaKO
    rw [show ((h, g) : GA D V × GA D W) = (h, 1) * (1, g) by simp, map_mul, Module.End.mul_apply]
  have hup : (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) =
      fun h => ∫ p, F h p ∂(μG.prod μG) := funext hFh
  refine ⟨fun h => (hB₁ h).1, ?_, ?_⟩
  · show Integrable _ μH
    rw [hup]
    exact hInt.integral_prod_left
  · have hpt : ∀ p : GA D W × GA D W, ∫ h, F h p ∂μH = ((νV 𝓗).toReal : ℂ) * (star (φ₁ p.1) * φ₂ p.2 *
        ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
      intro p
      have hsw := hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, p.1) f₁) (om (1, p.2) f₂)
        (hS.weil.om_pres _ _ hf₁) (hS.weil.om_pres _ _ hf₂)
      have he := hsw.tsum_eq
      rw [← hμH, tsum_mul_left] at he
      have hfun : (fun h => F h p) = fun h => (star (φ₁ p.1) * φ₂ p.2) *
          (thetaKO om h 1 (om (1, p.1) f₁) * star (thetaKO om h 1 (om (1, p.2) f₂))) := by
        funext h
        simp only [hF]
        rw [hsplit h p.1 f₁, hsplit h p.2 f₂]
        ring
      rw [hfun, integral_const_mul, ← he]
      ring
    show ∫ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂μH = _
    rw [hup, integral_integral_swap hInt, ← Measure.prod_restrict, ← hμG, ← integral_const_mul]
    congr 1
    funext p
    rw [hpt p]

end GlobalTheory.RawLift

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallis_inner_product_kernel_identity : ∀ D : D7, KerAbs D → SWPair D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧ IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧ ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV = ((νV 𝓗).toReal : ℂ) * ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  atlas_forward_decl GlobalTheory.RawLift.rallis_kernel_step
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RallisExch

theorem exch_general {X ι : Type*} [MeasurableSpace X] [Countable ι] (ν : Measure X) [SFinite ν] (𝓖 : Set X)
    (T : ι → X × X → ℂ) (a b : X → ℂ)
    (hT : ∀ Y, AEStronglyMeasurable (T Y) ((ν.prod ν).restrict (𝓖 ×ˢ 𝓖)))
    (ha : AEStronglyMeasurable a (ν.restrict 𝓖)) (hb : AEStronglyMeasurable b (ν.restrict 𝓖))
    (hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' Y, ‖T Y (g₁, g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤) :
    (∀ Y, IntegrableOn (fun p : X × X => star (a p.1) * b p.2 * T Y p) (𝓖 ×ˢ 𝓖) (ν.prod ν)) ∧
    Summable (fun Y => ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * T Y p ∂(ν.prod ν)) ∧
    ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * ∑' Y, T Y p ∂(ν.prod ν) =
      ∑' Y, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * T Y p ∂(ν.prod ν) := by
  have hρ : (ν.prod ν).restrict (𝓖 ×ˢ 𝓖) = (ν.restrict 𝓖).prod (ν.restrict 𝓖) :=
    (Measure.prod_restrict 𝓖 𝓖).symm
  set ρ := (ν.prod ν).restrict (𝓖 ×ˢ 𝓖) with hρdef
  set F : ι → X × X → ℂ := fun Y p => star (a p.1) * b p.2 * T Y p with hFdef
  have ha' : AEStronglyMeasurable (fun p : X × X => star (a p.1)) ρ := by
    rw [hρ]; exact ha.star.comp_fst
  have hb' : AEStronglyMeasurable (fun p : X × X => b p.2) ρ := by
    rw [hρ]; exact hb.comp_snd
  have hF : ∀ Y, AEStronglyMeasurable (F Y) ρ := fun Y => (ha'.mul hb').mul (hT Y)
  have hnorm : ∀ Y p, ‖F Y p‖ₑ = ‖T Y p‖ₑ * ‖a p.1‖ₑ * ‖b p.2‖ₑ := by
    intro Y p
    have hs : ‖star (a p.1)‖ₑ = ‖a p.1‖ₑ := by rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_star]
    simp only [F, enorm_mul, hs]; ring
  have hsum : ∑' Y, ∫⁻ p, ‖F Y p‖ₑ ∂ρ ≠ ⊤ := by
    rw [← lintegral_tsum (fun Y => (hF Y).enorm)]
    simp_rw [hnorm]
    rw [hρ, lintegral_prod _ ?_]
    · exact hfin
    · rw [← hρ]
      exact AEMeasurable.ennreal_tsum fun Y => by
        simpa [hnorm] using (hF Y).enorm
  have hint : ∀ Y, Integrable (F Y) ρ := fun Y =>
    ⟨hF Y, lt_of_le_of_lt (ENNReal.le_tsum Y) (lt_top_iff_ne_top.2 hsum)⟩
  refine ⟨hint, ?_, ?_⟩
  · refine Summable.of_norm_bounded (ENNReal.summable_toReal hsum) fun Y => ?_
    have h1 := enorm_integral_le_lintegral_enorm (μ := ρ) (F Y)
    rw [← ofReal_norm_eq_enorm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top hsum (ENNReal.le_tsum Y))).1 h1
  · have : (fun p : X × X => star (a p.1) * b p.2 * ∑' Y, T Y p) = fun p => ∑' Y, F Y p := by
      funext p; exact tsum_mul_left.symm
    rw [this]
    exact integral_tsum hF hsum

end GlobalTheory.RallisExch

namespace GlobalTheory.RallisExch

open scoped GlobalTheory.GaugeEx

theorem eisAbs_exchange : ∀ D : D7, EisAbs D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ Y : Lag W, IntegrableOn (fun p : GA D W × GA D W => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) (𝓖 ×ˢ 𝓖) (νW.prod νW)) ∧ Summable (fun Y : Lag W => ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW)) ∧ ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∑' Y : Lag W, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  intro D hE ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ h1 h2 hA1 hC1 hA2 hC2
  haveI : Countable (Lag W) := GlobalTheory.T.countable_doubled_hermitian_lagrangians D W
  haveI : SigmaFinite νW := by haveI := hS.haarW; infer_instance
  have hT : ∀ Y : Lag W, AEStronglyMeasurable
      (fun p : GA D W × GA D W => lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂))
      ((νW.prod νW).restrict (𝓖 ×ˢ 𝓖)) := fun Y =>
    (GlobalTheory.T.siegelWeil_lagrangian_term_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hS.weil hS.covol f₁ f₂ h1 h2 (fr Y)).aestronglyMeasurable
  exact exch_general νW 𝓖 (fun Y p => lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) φ₁ φ₂ hT
    hA1.cont.aestronglyMeasurable hA2.cont.aestronglyMeasurable
    (hE ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2 φ₁ φ₂ hA1 hC1 hA2 hC2)

end GlobalTheory.RallisExch
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilSum_doubleIntegral_exchange_cuspForms : ∀ D : D7, EisAbs D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ Y : Lag W, IntegrableOn (fun p : GA D W × GA D W => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) (𝓖 ×ˢ 𝓖) (νW.prod νW)) ∧ Summable (fun Y : Lag W => ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW)) ∧ ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∑' Y : Lag W, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  atlas_forward_decl GlobalTheory.RallisExch.eisAbs_exchange
end

section
section
open MeasureTheory

namespace GlobalTheory

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {ν : Measure G} [ν.IsHaarMeasure]
    {Γ : Subgroup G} [Countable Γ] {𝓖 : Set G}

theorem fundamentalDomain_lintegral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G) :
    ∫⁻ y in 𝓖, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂ν
      = ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν := by
  rw [lintegral_tsum (fun γ => by fun_prop)]
  set F : G → ENNReal := fun g => ‖P (x⁻¹ * g)‖ₑ * ‖a x‖ₑ * ‖b g‖ₑ with hF
  have key : ∀ γ : Γ, ∀ y, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = ‖P (x⁻¹ * ((γ : G)⁻¹ * y))‖ₑ * ‖a x‖ₑ * ‖b ((γ : G)⁻¹ * y)‖ₑ
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.lintegral_eq_tsum' F, ← lintegral_mul_left_eq_self _ x]
  simp [hF]

theorem fundamentalDomain_integral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G)
    (hfin : ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ≠ ⊤) :
    ∑' γ : Γ, ∫ y in 𝓖, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) ∂ν
      = ∫ g, star (a x) * b (x * g) * P g ∂ν := by
  set F : G → ℂ := fun g => star (a x) * b g * P (x⁻¹ * g) with hF
  have hFi : Integrable F ν := by
    refine ⟨by fun_prop, ?_⟩
    unfold HasFiniteIntegral
    rw [← lintegral_mul_left_eq_self _ x]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top
    refine lintegral_congr (fun g => ?_)
    have hs : ‖star (a x)‖ₑ = ‖a x‖ₑ := by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
    simp only [hF, enorm_mul, hs, inv_mul_cancel_left]
    ring
  have key : ∀ γ : Γ, ∀ y, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = star (a x) * b ((γ : G)⁻¹ * y) * P (x⁻¹ * ((γ : G)⁻¹ * y))
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.integral_eq_tsum' F hFi, ← integral_mul_left_eq_self F x]
  simp [hF]

theorem unfold_tsum_fundamentalDomain (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (a b P : G → ℂ)
    (ha : Continuous a) (hbc : Continuous b) (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g)
    (hP : StronglyMeasurable P)
    (hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤) :
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  have ham : Measurable a := ha.measurable
  have hbm : Measurable b := hbc.measurable
  have hPm : Measurable P := hP.measurable
  have hs : ∀ z : ℂ, ‖star z‖ₑ = ‖z‖ₑ := fun z => by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
  set μ := ν.restrict 𝓖 with hμ

  have hT : ∫⁻ x, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ∂μ ≠ ⊤ := by
    rw [← lintegral_congr (fun x => fundamentalDomain_lintegral_unfold_left h𝓖 hb hbm hPm (a := a) x)]
    exact hfin
  set k : G → G → ℂ := fun x g => star (a x) * b (x * g) * P g with hk
  have hkm : Measurable (Function.uncurry k) := by
    simp only [hk, Function.uncurry_def]; fun_prop
  have hki : Integrable (Function.uncurry k) (μ.prod ν) := by
    refine ⟨hkm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ (by fun_prop)]
    refine lt_of_le_of_lt (le_of_eq ?_) hT.lt_top
    refine lintegral_congr (fun x => lintegral_congr (fun g => ?_))
    simp only [hk, Function.uncurry_apply_pair, enorm_mul, hs]
    ring
  refine ⟨?_, ?_⟩
  · have h1 := hki.swap.integral_prod_left
    refine h1.congr (Filter.Eventually.of_forall (fun g => ?_))
    simp only [hk, Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]
    rw [integral_mul_const, mul_comm]

  · set f : Γ → G × G → ℂ := fun γ z => star (a z.1) * b z.2 * P (z.1⁻¹ * (γ : G)⁻¹ * z.2) with hf
    have hfm : ∀ γ, Measurable (f γ) := fun γ => by simp only [hf]; fun_prop
    have hfe : ∀ γ x y, ‖f γ (x, y)‖ₑ = ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ := by
      intro γ x y; simp only [hf, enorm_mul, hs]; ring
    have hsum : ∑' γ : Γ, ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ ≠ ⊤ := by
      rw [← lintegral_tsum (fun γ => ((hfm γ).enorm.lintegral_prod_right').aemeasurable)]
      have hx : ∀ x, ∑' γ : Γ, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ
          = ∫⁻ y, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂μ := fun x => by
        rw [← lintegral_tsum (f := fun γ y => ‖f γ (x, y)‖ₑ)
          (fun γ => ((hfm γ).comp measurable_prodMk_left).enorm.aemeasurable)]
        simp only [hfe]
      rw [lintegral_congr hx]
      exact hfin
    have hfi : ∀ γ, Integrable (f γ) (μ.prod μ) := fun γ =>
      ⟨(hfm γ).aestronglyMeasurable, by
        unfold HasFiniteIntegral
        rw [lintegral_prod _ (hfm γ).enorm.aemeasurable]
        exact lt_of_le_of_lt (ENNReal.le_tsum (f := fun γ : Γ => ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ) γ)
          hsum.lt_top⟩
    have lhs : ∀ γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν)
        = ∫ x, ∫ y, f γ (x, y) ∂μ ∂μ := by
      intro γ; rw [← Measure.prod_restrict, ← integral_prod _ (hfi γ)]
    rw [tsum_congr lhs, ← integral_tsum (fun γ => (hfi γ).integral_prod_left.aestronglyMeasurable)
      (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun γ =>
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _))]
    have hae : ∀ᵐ x ∂μ, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν < ⊤ :=
      ae_lt_top (show Measurable (fun z : G × G => ‖P z.2‖ₑ * ‖a z.1‖ₑ * ‖b (z.1 * z.2)‖ₑ) by
        fun_prop).lintegral_prod_right' hT
    have step : (∫ x, ∑' γ : Γ, ∫ y, f γ (x, y) ∂μ ∂μ) = ∫ x, ∫ g, k x g ∂ν ∂μ :=
      integral_congr_ae (hae.mono fun x hx => fundamentalDomain_integral_unfold_left h𝓖 hb hbm hPm x hx.ne)
    rw [step, integral_integral_swap hki]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hk]
    rw [integral_mul_const, mul_comm]
end
end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_tsum_integral_fundamentalDomain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → ∀ (a b P : G → ℂ), Continuous a → Continuous b →
    (∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) → StronglyMeasurable P →
    ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤ →
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  atlas_forward_decl GlobalTheory.unfold_tsum_fundamentalDomain
end

section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.Doubling

variable {E : Type} [Field E] {r : ℕ}

def conjSub (c : E ≃+* E) (S : Submodule E (Fin r → E)) : Submodule E (Fin r → E) where
  carrier := {w | (fun i => c (w i)) ∈ S}
  add_mem' := by
    intro a b ha hb
    have := S.add_mem ha hb
    simpa [Set.mem_setOf_eq, Pi.add_def] using this
  zero_mem' := by
    have h0 : (fun i => c ((0 : Fin r → E) i)) = 0 := by funext i; simp
    change (fun i => c ((0 : Fin r → E) i)) ∈ S
    rw [h0]
    exact S.zero_mem
  smul_mem' := by
    intro t a ha
    have := S.smul_mem (c t) ha
    simpa [Set.mem_setOf_eq, Pi.smul_def] using this

theorem mem_conjSub (c : E ≃+* E) (S : Submodule E (Fin r → E)) (w : Fin r → E) :
    w ∈ conjSub c S ↔ (fun i => c (w i)) ∈ S := ⟨fun h => h, fun h => h⟩

private theorem conj_mem_lemma (c : E ≃+* E) (hc : ∀ x, c (c x) = x)
    (S : Submodule E (Fin r → E)) (w : Fin r → E) :
    (fun i => c (w i)) ∈ conjSub c S ↔ w ∈ S := by
  rw [mem_conjSub]
  simp only [hc]

theorem finrank_conjSub (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (S : Submodule E (Fin r → E)) :
    Module.finrank E (conjSub c S) = Module.finrank E S := by
  let j : S ≃+ conjSub c S :=
    { toFun := fun x => ⟨fun i => c (x.1 i), (conj_mem_lemma c hc S x.1).2 x.2⟩
      invFun := fun y => ⟨fun i => c (y.1 i), (mem_conjSub c S y.1).1 y.2⟩
      left_inv := fun x => Subtype.ext (funext fun i => hc (x.1 i))
      right_inv := fun y => Subtype.ext (funext fun i => hc (y.1 i))
      map_add' := fun x y => Subtype.ext (funext fun i => map_add c (x.1 i) (y.1 i)) }
  have hr : Module.rank E S = Module.rank E (conjSub c S) :=
    rank_eq_of_equiv_equiv (c : E → E) j c.bijective
      (fun t x => Subtype.ext (funext fun i => map_mul c t (x.1 i)))
  exact (congrArg Cardinal.toNat hr).symm

theorem row_apply (c : E ≃+* E) (J : Matrix (Fin r) (Fin r) E) (x v : Fin r → E) :
    (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) v () =
      (fun i => c (x i)) ⬝ᵥ J.mulVec v := by
  rw [Matrix.toLin'_apply, Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.of_apply]

theorem mem_orth (c : E ≃+* E) (J : Matrix (Fin r) (Fin r) E) (S : Submodule E (Fin r → E))
    (v : Fin r → E) :
    v ∈ (⨅ x ∈ S, LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)))
      ↔ ∀ x ∈ S, (fun i => c (x i)) ⬝ᵥ J.mulVec v = 0 := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun x => forall_congr' fun _ => ?_
  rw [← row_apply c J x v]
  exact ⟨fun h => congrFun h (), fun h => funext fun u => by cases u; exact h⟩

theorem finrank_orth (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (J : Matrix (Fin r) (Fin r) E)
    (hJ : J.det ≠ 0) (S : Submodule E (Fin r → E)) :
    Module.finrank E
      (⨅ x ∈ S, LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) :
        Submodule E (Fin r → E)) + Module.finrank E S = r := by
  classical
  set T := conjSub c S
  have hTS : Module.finrank E T = Module.finrank E S := finrank_conjSub c hc S
  have hunit : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 (isUnit_iff_ne_zero.2 hJ)
  set Ψ : (Fin r → E) →ₗ[E] Module.Dual E (Fin r → E) :=
    (dotProductEquiv E (Fin r)).toLinearMap ∘ₗ J.vecMulLinear
  have hΨ : Function.Injective Ψ :=
    (dotProductEquiv E (Fin r)).injective.comp (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  have hΨv : ∀ w v, Ψ w v = w ⬝ᵥ J.mulVec v := fun w v => by
    simp [Ψ, Matrix.dotProduct_mulVec]
  have hO : (⨅ x ∈ S, LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) :
      Submodule E (Fin r → E)) = (T.map Ψ).dualCoannihilator := by
    ext v
    rw [mem_orth, Submodule.mem_dualCoannihilator]
    constructor
    · rintro h φ ⟨w, hw, rfl⟩
      rw [hΨv]
      have hw' := (mem_conjSub c S w).1 hw
      have := h _ hw'
      simpa only [hc] using this
    · intro h x hx
      have hx' : (fun i => c (x i)) ∈ T := by
        rw [mem_conjSub]; simpa only [hc] using hx
      have := h _ ⟨_, hx', rfl⟩
      rwa [hΨv] at this
  have hW : Module.finrank E (T.map Ψ) = Module.finrank E T :=
    (Submodule.equivMapOfInjective Ψ hΨ T).finrank_eq.symm
  have key := Subspace.finrank_add_finrank_dualCoannihilator_eq (T.map Ψ)
  rw [Module.finrank_fin_fun, hW, hTS] at key
  rw [hO]
  omega

theorem finrank_map_fst (Y : Submodule E ((Fin r → E) × (Fin r → E))) :
    Module.finrank E (Y.map (LinearMap.fst E _ _)) +
      Module.finrank E (Y.comap (LinearMap.inr E (Fin r → E) (Fin r → E))) = Module.finrank E Y := by
  set f := (LinearMap.fst E (Fin r → E) (Fin r → E)).domRestrict Y with hf
  set g : Y.comap (LinearMap.inr E (Fin r → E) (Fin r → E)) →ₗ[E] Y :=
    LinearMap.codRestrict Y ((LinearMap.inr E (Fin r → E) (Fin r → E)).comp (Submodule.subtype _))
      (fun w => w.2) with hg
  have hinj : Function.Injective g := by
    intro u w huw
    have h := congrArg (fun y : Y => (y : (Fin r → E) × (Fin r → E)).2) huw
    exact Subtype.ext h
  have hrange : LinearMap.range g = LinearMap.ker f := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      rfl
    · intro hy
      have h1 : (y : (Fin r → E) × (Fin r → E)).1 = 0 := hy
      have hy' : (LinearMap.inr E (Fin r → E) (Fin r → E)) (y : (Fin r → E) × (Fin r → E)).2 =
          (y : (Fin r → E) × (Fin r → E)) := by
        exact Prod.ext h1.symm rfl
      refine ⟨⟨(y : (Fin r → E) × (Fin r → E)).2, ?_⟩, ?_⟩
      · rw [Submodule.mem_comap, hy']
        exact y.2
      · exact Subtype.ext hy'
  have key := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_domRestrict, ← hrange, LinearMap.finrank_range_of_inj hinj] at key
  exact key

theorem finrank_map_snd (Y : Submodule E ((Fin r → E) × (Fin r → E))) :
    Module.finrank E (Y.map (LinearMap.snd E _ _)) +
      Module.finrank E (Y.comap (LinearMap.inl E (Fin r → E) (Fin r → E))) = Module.finrank E Y := by
  set f := (LinearMap.snd E (Fin r → E) (Fin r → E)).domRestrict Y with hf
  set g : Y.comap (LinearMap.inl E (Fin r → E) (Fin r → E)) →ₗ[E] Y :=
    LinearMap.codRestrict Y ((LinearMap.inl E (Fin r → E) (Fin r → E)).comp (Submodule.subtype _))
      (fun w => w.2) with hg
  have hinj : Function.Injective g := by
    intro u w huw
    have h := congrArg (fun y : Y => (y : (Fin r → E) × (Fin r → E)).1) huw
    exact Subtype.ext h
  have hrange : LinearMap.range g = LinearMap.ker f := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      rfl
    · intro hy
      have h1 : (y : (Fin r → E) × (Fin r → E)).2 = 0 := hy
      have hy' : (LinearMap.inl E (Fin r → E) (Fin r → E)) (y : (Fin r → E) × (Fin r → E)).1 =
          (y : (Fin r → E) × (Fin r → E)) := by
        exact Prod.ext rfl h1.symm
      refine ⟨⟨(y : (Fin r → E) × (Fin r → E)).1, ?_⟩, ?_⟩
      · rw [Submodule.mem_comap, hy']
        exact y.2
      · exact Subtype.ext hy'
  have key := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_domRestrict, ← hrange, LinearMap.finrank_range_of_inj hinj] at key
  exact key

private theorem conj_single_lemma (c : E ≃+* E) (i : Fin r) :
    (fun k => c ((Pi.single i (1 : E) : Fin r → E) k)) = (Pi.single i (1 : E) : Fin r → E) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem isometry_matrix (c : E ≃+* E) (J g : Matrix (Fin r) (Fin r) E)
    (h : ∀ x x' : Fin r → E, (fun i => c (x i)) ⬝ᵥ J.mulVec x' =
      (fun i => c ((g.mulVec x) i)) ⬝ᵥ J.mulVec (g.mulVec x')) :
    (g.map c).transpose * J * g = J := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [conj_single_lemma c i] at h1
  simp only [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at h1
  rw [h1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct,
    Matrix.mulVec, Matrix.col_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)

theorem maximal_isotropic_doubled (E : Type) [Field E] (c : E ≃+* E) (r : ℕ)
    (J : Matrix (Fin r) (Fin r) E) (hc : ∀ x, c (c x) = x) (hJ : J.det ≠ 0)
    (_hJh : J.transpose.map c = J) (Y : Submodule E ((Fin r → E) × (Fin r → E)))
    (hY : Module.finrank E Y = r)
    (hiso : ∀ y ∈ Y, ∀ y' ∈ Y, (fun i => c (y.1 i)) ⬝ᵥ J.mulVec y'.1 =
      (fun i => c (y.2 i)) ⬝ᵥ J.mulVec y'.2) :
    (Module.finrank E (Y.comap (LinearMap.inl E _ _)) =
        Module.finrank E (Y.comap (LinearMap.inr E _ _))) ∧
      Y.map (LinearMap.fst E _ _) = ⨅ x ∈ Y.comap (LinearMap.inl E _ _),
        LinearMap.ker ((Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j))) ∧
      (Y.comap (LinearMap.inl E _ _) = ⊥ ↔ ∃ g : GL (Fin r) E,
        ((g : Matrix (Fin r) (Fin r) E).map c).transpose * J * (g : Matrix (Fin r) (Fin r) E) = J ∧
          ∀ y, y ∈ Y ↔ y.2 = (g : Matrix (Fin r) (Fin r) E).mulVec y.1) := by
  classical
  set A := Y.comap (LinearMap.inl E (Fin r → E) (Fin r → E)) with hA
  set B := Y.comap (LinearMap.inr E (Fin r → E) (Fin r → E)) with hB
  have memA : ∀ a, a ∈ A ↔ ((a, 0) : (Fin r → E) × (Fin r → E)) ∈ Y := fun a => by
    rw [hA, Submodule.mem_comap, LinearMap.inl_apply]
  have memB : ∀ b, b ∈ B ↔ (((0 : Fin r → E), b) : (Fin r → E) × (Fin r → E)) ∈ Y := fun b => by
    rw [hB, Submodule.mem_comap, LinearMap.inr_apply]
  have hfst := finrank_map_fst Y
  have hsnd := finrank_map_snd Y
  rw [← hB, hY] at hfst
  rw [← hA, hY] at hsnd
  have hoA := finrank_orth c hc J hJ A
  have hoB := finrank_orth c hc J hJ B
  have le1 : Y.map (LinearMap.fst E (Fin r → E) (Fin r → E)) ≤ ⨅ x ∈ A,
      LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) := by
    rintro v ⟨y, hy, rfl⟩
    rw [mem_orth]
    intro a ha
    have := hiso _ ((memA a).1 ha) y hy
    simpa using this
  have le2 : Y.map (LinearMap.snd E (Fin r → E) (Fin r → E)) ≤ ⨅ x ∈ B,
      LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) := by
    rintro v ⟨y, hy, rfl⟩
    rw [mem_orth]
    intro b hb
    have := hiso _ ((memB b).1 hb) y hy
    simpa using this.symm
  have d1 := Submodule.finrank_mono le1
  have d2 := Submodule.finrank_mono le2
  have hAB : Module.finrank E A = Module.finrank E B := by omega
  refine ⟨hAB, Submodule.eq_of_le_of_finrank_eq le1 (by omega), ?_⟩
  constructor
  · intro hA0
    have hA0' : Module.finrank E A = 0 := by rw [hA0]; exact finrank_bot E (Fin r → E)
    have hB0 : B = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hP1 : Y.map (LinearMap.fst E (Fin r → E) (Fin r → E)) = ⊤ :=
      Submodule.eq_of_le_of_finrank_eq le_top (by rw [finrank_top, Module.finrank_fin_fun]; omega)
    let f : Y →ₗ[E] (Fin r → E) := (LinearMap.fst E (Fin r → E) (Fin r → E)).comp Y.subtype
    have hf : ∀ y : Y, f y = (y : (Fin r → E) × (Fin r → E)).1 := fun y => rfl
    have finj : Function.Injective f := by
      intro y y' hyy
      rw [hf, hf] at hyy
      have hd : (y : (Fin r → E) × (Fin r → E)) - y' ∈ Y := Y.sub_mem y.2 y'.2
      have h2 : ((y : (Fin r → E) × (Fin r → E)) - y').2 ∈ B := by
        rw [memB]
        convert hd using 1
        exact Prod.ext (by simp [hyy]) rfl
      rw [hB0, Submodule.mem_bot, Prod.snd_sub, sub_eq_zero] at h2
      exact Subtype.ext (Prod.ext hyy h2)
    have fsurj : Function.Surjective f := by
      intro v
      have hv : v ∈ Y.map (LinearMap.fst E (Fin r → E) (Fin r → E)) := hP1 ▸ Submodule.mem_top
      obtain ⟨y, hy, rfl⟩ := hv
      exact ⟨⟨y, hy⟩, rfl⟩
    let e := LinearEquiv.ofBijective f ⟨finj, fsurj⟩
    let T : (Fin r → E) →ₗ[E] (Fin r → E) :=
      (LinearMap.snd E (Fin r → E) (Fin r → E)).comp (Y.subtype.comp e.symm.toLinearMap)
    have hT : ∀ v, T v = ((e.symm v : Y) : (Fin r → E) × (Fin r → E)).2 := fun v => rfl
    have he1 : ∀ v, ((e.symm v : Y) : (Fin r → E) × (Fin r → E)).1 = v := fun v => by
      rw [← hf]
      exact e.apply_symm_apply v
    have hgraph : ∀ y : (Fin r → E) × (Fin r → E), y ∈ Y ↔ y.2 = T y.1 := by
      intro y
      constructor
      · intro hy
        have hyy : (⟨y, hy⟩ : Y) = e.symm y.1 := finj (by rw [hf, hf, he1])
        rw [hT, ← hyy]
      · intro h
        have hy : y = ((e.symm y.1 : Y) : (Fin r → E) × (Fin r → E)) :=
          Prod.ext (he1 _).symm (h.trans (hT _))
        rw [hy]
        exact (e.symm y.1).2
    set M := LinearMap.toMatrix' T with hMdef
    have hM : ∀ v, M.mulVec v = T v := fun v => LinearMap.toMatrix'_mulVec T v
    have hdet : M.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv
      have hv0 : (v, (0 : Fin r → E)) ∈ Y := by
        rw [hgraph, ← hM, hMv]
      have hvA : v ∈ A := (memA v).2 hv0
      rw [hA0, Submodule.mem_bot] at hvA
      exact hvA
    refine ⟨Matrix.nonsingInvUnit M (isUnit_iff_ne_zero.mpr hdet), ?_, ?_⟩
    · show (M.map c).transpose * J * M = J
      apply isometry_matrix
      intro x x'
      have hx := (hgraph (x, T x)).2 rfl
      have hx' := (hgraph (x', T x')).2 rfl
      have := hiso _ hx _ hx'
      rw [hM, hM]
      exact this
    · intro y
      show y ∈ Y ↔ y.2 = M.mulVec y.1
      rw [hM]
      exact hgraph y
  · rintro ⟨g, -, hg⟩
    rw [eq_bot_iff]
    intro a ha
    rw [memA, hg] at ha
    have hinv : ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec
        ((g : Matrix (Fin r) (Fin r) E).mulVec a) = a := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← ha, Matrix.mulVec_zero] at hinv
    rw [Submodule.mem_bot, ← hinv]

end GlobalTheory.Doubling
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Graphs

variable {D : D7}

def graphSub (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Submodule D.host.E ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :=
  LinearMap.range (LinearMap.prod LinearMap.id (Matrix.mulVecLin c))

theorem mem_graphSub {W : HSp D} {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    {y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)} : y ∈ graphSub W c ↔ y.2 = c *ᵥ y.1 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro h
    exact ⟨y.1, Prod.ext rfl (by simp [h])⟩

theorem cT_eq (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) c = cᴴ := by
  funext i j
  rfl

theorem star_dot (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (x x' : Fin W.rank → D.host.E) :
    star (c *ᵥ x) ⬝ᵥ W.gram *ᵥ (c *ᵥ x') = star x ⬝ᵥ (cᴴ * W.gram * c) *ᵥ x' := by
  rw [Matrix.star_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

def graphLag (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) : Lag W :=
  ⟨graphSub W g, by
    rw [graphSub, LinearMap.finrank_range_of_inj (fun x y h => congrArg Prod.fst h)]
    simp, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
        W.gram * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
    rw [cT_eq] at h
    show star x ⬝ᵥ W.gram *ᵥ y = star ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ x) ⬝ᵥ
      W.gram *ᵥ ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ y)
    rw [star_dot, h]⟩

theorem graphLag_bot (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    (graphLag W g hg).1.comap (LinearMap.inl D.host.E _ _) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h : (0 : Fin W.rank → D.host.E) = (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ x :=
    mem_graphSub.1 (Submodule.mem_comap.1 hx)
  have h2 := congrArg (((g⁻¹ : GL (Fin W.rank) D.host.E) : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ ·) h
  simpa [Matrix.mulVec_mulVec] using h2.symm

theorem herm' (W : HSp D) : W.gramᵀ.map (starRingAut : D.host.E ≃+* D.host.E) = W.gram := by
  have h := GlobalTheory.AutFunCounterexample.gram_herm W
  funext i j
  exact congrFun (congrFun h i) j

theorem incA_injective (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem exists_rat (W : HSp D) (γ : GQ W) : ∃ g : GL (Fin W.rank) D.host.E,
    g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram ∧ Formalism.UG.bc (incA D) g = matHom W (γ : GA D W) := by
  have h : matHom W (γ : GA D W) ∈ HFin (AF D.host.F) D.sp.cm.sig W.gram := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 h
  exact ⟨g, hg, e⟩

def ratG (W : HSp D) (γ : GQ W) : GL (Fin W.rank) D.host.E := (exists_rat W γ).choose

theorem ratG_mem (W : HSp D) (γ : GQ W) :
    ratG W γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := (exists_rat W γ).choose_spec.1

theorem mt_ratG (W : HSp D) (γ : GQ W) :
    Formalism.L2.Theta.mt W (γ : GA D W) = (ratG W γ : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) := by
  rw [Formalism.L2.Theta.mt, ← (exists_rat W γ).choose_spec.2]
  rfl

theorem bc_injective (W : HSp D) {g g' : GL (Fin W.rank) D.host.E}
    (h : (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) =
      (g' : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) : g = g' := by
  exact Units.ext (Matrix.ext fun i j => incA_injective D (congrFun (congrFun h i) j))

theorem graphSub_injective (W : HSp D) {c c' : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (h : graphSub W c = graphSub W c') : c = c' := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hx : (x, c *ᵥ x) ∈ graphSub W c' := h ▸ mem_graphSub.2 rfl
  exact mem_graphSub.1 hx

theorem isLagFrame_graph (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    IsLagFrame W (graphLag W g hg) (1, (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E)) := by
  have h := congrArg (Submodule.map (LinearMap.prod (LinearMap.id : (Fin W.rank → D.host.E) →ₗ[D.host.E] _)
    (Matrix.mulVecLin (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E))))
    (Pi.basisFun D.host.E (Fin W.rank)).span_eq
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at h
  refine Eq.trans ?_ h
  congr 2
  funext j
  ext a <;> simp [Matrix.one_apply, Pi.single_apply]

theorem hr_mem (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
      W.gram * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
  show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig)
      ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) *
      W.gram.map (inclR (F := D.host.F) (AF D.host.F)) *
      (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) =
      W.gram.map (inclR (F := D.host.F) (AF D.host.F))
  rw [GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, h]

def ofRat (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) : GQ W :=
  ⟨(⟨Formalism.UG.bc (incA D) g, hr_mem W g hg⟩ : HR (AF D.host.F) D.sp.cm.sig W.gram),
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)⟩

end GlobalTheory.RawLift.Graphs

namespace GlobalTheory.RawLift.Graphs

open GlobalTheory.RawLift.Graphs

theorem graphs : ∀ (D : D7) (W : HSp D), ∃ e : GQ W ≃ {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥},
    ∀ γ : GQ W, ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, mt W (γ : GA D W) = c.map (incA D) ∧ IsLagFrame W (e γ).1 (1, c) := by
  intro D W
  let f : GQ W → {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥} :=
    fun γ => ⟨graphLag W (ratG W γ) (ratG_mem W γ), graphLag_bot W _ _⟩
  have hinj : Function.Injective f := by
    intro γ γ' h
    have h1 : graphSub W (ratG W γ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = graphSub W (ratG W γ') :=
      congrArg (fun Y => Y.1.1) h
    have h2 := graphSub_injective W h1
    have h3 : Formalism.L2.Theta.mt W (γ : GA D W) = Formalism.L2.Theta.mt W (γ' : GA D W) := by
      rw [mt_ratG, mt_ratG, h2]
    exact Subtype.ext (GlobalTheory.AutFunCounterexample.GA_ext W h3)
  have hsurj : Function.Surjective f := by
    rintro ⟨Y, hY⟩
    obtain ⟨g, hgU, hgY⟩ := ((GlobalTheory.Doubling.maximal_isotropic_doubled D.host.E starRingAut W.rank W.gram
      (fun x => star_star x) (GlobalTheory.AutFunCounterexample.gram_det_ne W) (herm' W) Y.1 Y.2.1 Y.2.2).2.2).1 hY
    have hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := hgU
    refine ⟨ofRat W g hg, Subtype.ext (Subtype.ext ?_)⟩
    have e1 : ratG W (ofRat W g hg) = g := bc_injective W ((mt_ratG W _).symm.trans rfl)
    show graphSub W (ratG W (ofRat W g hg)) = Y.1
    rw [e1]
    ext y
    rw [mem_graphSub]
    exact (hgY y).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun γ => ⟨_, mt_ratG W γ, isLagFrame_graph W _ (ratG_mem W γ)⟩⟩

end GlobalTheory.RawLift.Graphs
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangians_transverse_eq_graphs_rational_unitary : ∀ (D : D7) (W : HSp D), ∃ e : GQ W ≃ {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥},
    ∀ γ : GQ W, ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, mt W (γ : GA D W) = c.map (incA D) ∧ IsLagFrame W (e γ).1 (1, c) := by
  atlas_forward_decl GlobalTheory.RawLift.Graphs.graphs
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pairing_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (p : GA D V × GA D W) (a b : WO V W → ℂ), IsThetaFunO ψ V W a → IsThetaFunO ψ V W b → thetaIP μ 𝓕 (om p a) (om p b) = thetaIP μ 𝓕 a b := by
  first | exact @GlobalTheory.WeilPairing.thetaInner_weilRep | exact GlobalTheory.WeilPairing.thetaInner_weilRep | (intros; apply GlobalTheory.WeilPairing.thetaInner_weilRep <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem graph_term_of_termMove {D : D7} (hTM : TermMove D) {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)}
    {𝓗 : Set (GA D V)} {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) {γ : GA D W} (hγ : γ ∈ GQ W) {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hc : mt W γ = c.map (incA D)) {Y : Lag W} (hY : IsLagFrame W Y (1, c)) (g₁ g₂ : GA D W) :
    lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂) = thetaIP μ 𝓕 (om (1, g₁⁻¹ * γ⁻¹ * g₂) f₂) f₁ := by
  have hmul : ∀ p q (f : WO V W → ℂ), om p (om q f) = om (p * q) f := fun p q f => by rw [map_mul]; rfl
  have p₁ := hS.weil.om_pres (1, g₁) f₁ h₁
  have p₂ := hS.weil.om_pres (1, g₂) f₂ h₂
  obtain ⟨hfr, hg⟩ := hTM ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ _ p₁ p₂
  have e1 : om (1, g₁⁻¹) (om (1, γ⁻¹) (om (1, g₂) f₂)) = om (1, g₁⁻¹ * γ⁻¹ * g₂) f₂ := by
    rw [hmul, hmul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, one_mul, mul_assoc]
  have e2 : om (1, g₁⁻¹) (om (1, g₁) f₁) = f₁ := by
    rw [hmul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  rw [← hfr Y (1, c) hY, (hg γ hγ c hc).2,
    ← GlobalTheory.T.theta_pairing_invariant D ψ V W χV χW om μ 𝓕 hS.weil hS.covol (1, g₁⁻¹) _ _ (hS.weil.om_pres (1, γ⁻¹) _ p₂) p₁, e1, e2]

open scoped GlobalTheory.GaugeEx in

theorem rallis_graphs : ∀ D : D7, EisAbs D → TermMove D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧ ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW := by
  intro D hEA hTM ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ ha₁ hc₁ ha₂ hc₂
  haveI := hS.haarW
  obtain ⟨e, he⟩ := GlobalTheory.T.lagrangians_transverse_eq_graphs_rational_unitary D W
  haveI : Countable (Lag W) := GlobalTheory.T.countable_doubled_hermitian_lagrangians D W
  haveI : Countable (GQ W) := e.injective.countable
  choose c hc hcf using he
  let P : GA D W → ℂ := fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁
  have hT : ∀ (γ : GQ W) (p : GA D W × GA D W),
      lagTerm μ 𝓕 (fr (e γ).1) (om (1, p.1) f₁) (om (1, p.2) f₂) = P (p.1⁻¹ * (γ : GA D W)⁻¹ * p.2) :=
    fun γ p => graph_term_of_termMove hTM hS hf₁ hf₂ γ.2 (hc γ) (hcf γ) p.1 p.2
  have hPm : StronglyMeasurable P := by
    have h := GlobalTheory.T.siegelWeil_lagrangian_term_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hS.weil hS.covol f₁ f₂ hf₁ hf₂ (1, 1)
    have hcont : Continuous fun g : GA D W => ((1 : GA D W), g) := continuous_const.prodMk continuous_id
    convert h.comp_measurable hcont.measurable using 1
    funext g
    simp only [Function.comp_apply, P]
    rw [lagTerm_one_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : GQ W, ‖P (g₁⁻¹ * (γ : GA D W)⁻¹ * g₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ ∂νW ∂νW ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hEA ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ hf₁ hf₂ φ₁ φ₂ ha₁ hc₁ ha₂ hc₂) ?_
    refine lintegral_mono fun g₁ => lintegral_mono fun g₂ => ?_
    have hinj : Function.Injective fun γ : GQ W => (e γ).1 := Subtype.val_injective.comp e.injective
    refine le_trans (le_of_eq ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun Y => ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ))
    refine tsum_congr fun γ => ?_
    rw [← hT γ (g₁, g₂)]
  obtain ⟨hI, hE⟩ := GlobalTheory.T.unfold_tsum_integral_fundamentalDomain νW (GQ W) 𝓖 hS.fdW φ₁ φ₂ P ha₁.cont ha₂.cont ha₂.left hPm hfin
  refine ⟨hI, ?_⟩
  refine ((e.tsum_eq (fun Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥} =>
    ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW))).symm.trans ?_).trans hE
  refine tsum_congr fun γ => ?_
  congr 1
  funext p
  rw [hT γ p]

end GlobalTheory.RawLift
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangianGraphs_sum_eq_matrixCoeff_integral : ∀ D : D7, EisAbs D → TermMove D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧ ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW := by
  atlas_forward_decl GlobalTheory.RawLift.rallis_graphs
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open Filter
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.TermCont

open GlobalTheory.RawLift

theorem continuous_lagTerm : ∀ D : D7, ∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr,
    SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
      ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ →
        Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂ Y _
  have hw := hS.weil
  have hψ := hw.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ h₂
  have hJ := GlobalTheory.ThetaJointCont.continuous_om_oriented hw h₁
  have hrm : ∀ (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E), Continuous fun u : WO V W => ratMul C u := fun C => by
    unfold ratMul
    exact continuous_const.matrix_mul continuous_id
  have hμ1 : μ 𝓕 = 1 := hS.covol.2.2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [hμ1]; exact ENNReal.one_ne_top)
  have : SecondCountableTopology (GA D W) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).2.1
  refine continuous_iff_continuousAt.2 fun g₀ => ?_

  have hc0 : Continuous fun w : WO V W => om ((1 : GA D V), g₀) f₁ w :=
    hJ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨κ, hκ⟩ := hK.exists_bound_of_continuousOn hc0.continuousOn
  have hev : ∀ᶠ g in 𝓝 g₀, ∀ w ∈ K, ‖om ((1 : GA D V), g) f₁ w‖ ≤ κ + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun w hw' => ?_
    have hc : Continuous fun y : GA D W × WO V W => ‖om ((1 : GA D V), y.1) f₁ y.2‖ :=
      (hJ.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).norm
    exact (hc.continuousAt.eventually_lt continuousAt_const ((hκ w hw').trans_lt (lt_add_one κ))).mono
      fun y hy => hy.le
  have hall : ∀ᶠ g in 𝓝 g₀, ∀ w, ‖om ((1 : GA D V), g) f₁ w‖ ≤ κ + 1 := hev.mono fun g hg w => by
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.OrientedHeis.theta_norm_periodic hψ (hw.om_pres _ f₁ h₁) γ hγ w]
    exact hg _ h
  unfold lagTerm
  refine continuousAt_of_dominated (bound := fun _ => (κ + 1) * C₂) ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun g => ?_
    exact ((((hw.om_pres _ f₁ h₁).cont.comp (hrm _)).mul
      (continuous_star.comp (h₂.cont.comp (hrm _))))).aestronglyMeasurable
  · refine hall.mono fun g hg => Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hg _) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hg 0))
  · refine Eventually.of_forall fun u => ?_
    exact ((hw.om_cont f₁ h₁ _).comp (continuous_const.prodMk continuous_id)).continuousAt.mul continuousAt_const

end GlobalTheory.RawLift.TermCont

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem rallisConv_of_steps : ∀ D : D7, SWPair D → EisAbs D → KerAbs D → TermMove D → TermInv D → CuspKill D → RallisConv D := by
  intro D hSW hEis hKer hMove hInv hKill θ ψ V W χV χW om hθ hω hsig hpos hbig νV 𝓗 νW 𝓖 μ 𝓕 hνV h𝓗 hνW h𝓖
    hμ h𝓕 h1 f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  have hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 (lagFrame W) :=
    { weil := hω, sigOK := hsig, pos := hpos, big := hbig, haarV := hνV, fdV := h𝓗, haarW := hνW, fdW := h𝓖,
      covol := ⟨hμ, h𝓕, h1⟩, frame := lagFrame_isLagFrame W }
  obtain ⟨K1, K2, K3⟩ := GlobalTheory.T.rallis_inner_product_kernel_identity D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁
    hφ₂ hc₂
  obtain ⟨-, E2, E3⟩ := GlobalTheory.T.siegelWeilSum_doubleIntegral_exchange_cuspForms D hEis ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  obtain ⟨G1, G2⟩ := GlobalTheory.T.lagrangianGraphs_sum_eq_matrixCoeff_integral D hEis hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁
    hφ₂ hc₂
  have N := GlobalTheory.T.rallis_nonGraphLagrangian_sum_eq_zero_cuspidal D hEis hMove hInv hKill (GlobalTheory.RawLift.TermCont.continuous_lagTerm D) ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂
    hφ₁ hc₁ hφ₂ hc₂
  refine ⟨K1, K2, G1, ?_⟩
  rw [K3, E3, ← E2.tsum_subtype_add_tsum_subtype_compl {Y : Lag W | Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}]
  erw [N, add_zero]
  rw [← G2]
  rfl

end GlobalTheory.RawLift

end
end
