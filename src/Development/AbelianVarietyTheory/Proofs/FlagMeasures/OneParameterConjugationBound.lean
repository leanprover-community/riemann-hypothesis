import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarBallGrowthUnitaryJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableExpNegMulOfSublevelGrowth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalVolumeGrowth
import BuildAid.ForwardExisting

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_subgroup_bi_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∀ m ∈ NW ε W, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  first | exact @GlobalTheory.UnipUnimod.unimodular_NW | exact GlobalTheory.UnipUnimod.unimodular_NW | (intros; apply GlobalTheory.UnipUnimod.unimodular_NW <;> assumption)
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_volume_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r))) ∧ ∀ b : ℝ, 4 * n * rkR ε < b → Integrable (fun m : UJ ε => Real.exp (-(b * dOp (umat m)))) ν := by
  first | exact @GlobalTheory.RadVol.radical_volume_growth | exact GlobalTheory.RadVol.radical_volume_growth | (intros; apply GlobalTheory.RadVol.radical_volume_growth <;> assumption)
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

private theorem lintegral_eq_lintegral_weight_mul_lintegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hone : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (φ : G → ENNReal) (hφ : Measurable φ) :
    ∫⁻ y, φ y ∂μ = ∫⁻ y, β y * ∫⁻ m, φ (m * y) ∂ν ∂μ := by
  calc ∫⁻ y, φ y ∂μ = ∫⁻ y, (∫⁻ m, β (m⁻¹ * y) ∂ν) * φ y ∂μ := by
          simp only [hone, one_mul]
    _ = ∫⁻ y, ∫⁻ m, β (m⁻¹ * y) * φ y ∂ν ∂μ := by
          refine lintegral_congr (fun y => ?_)
          have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
          exact (lintegral_mul_const _ hb).symm
    _ = ∫⁻ m, ∫⁻ y, β (m⁻¹ * y) * φ y ∂μ ∂ν := by
          have hm : Measurable (fun p : G × G => β (p.2⁻¹ * p.1) * φ p.1) :=
            (hβ.comp (measurable_snd.inv.mul measurable_fst)).mul (hφ.comp measurable_fst)
          exact lintegral_lintegral_swap (f := fun y m => β (m⁻¹ * y) * φ y) hm.aemeasurable
    _ = ∫⁻ m, ∫⁻ y, β y * φ (m * y) ∂μ ∂ν := by
          refine lintegral_congr (fun m => ?_)
          have h := lintegral_mul_left_eq_self (μ := μ) (fun y => β (m⁻¹ * y) * φ y) m
          simp only [inv_mul_cancel_left] at h
          exact h.symm
    _ = ∫⁻ y, ∫⁻ m, β y * φ (m * y) ∂ν ∂μ := by
          have hm : Measurable (fun p : G × G => β p.2 * φ (p.1 * p.2)) :=
            (hβ.comp measurable_snd).mul (hφ.comp (measurable_fst.mul measurable_snd))
          exact lintegral_lintegral_swap (f := fun m y => β y * φ (m * y)) hm.aemeasurable
    _ = ∫⁻ y, β y * ∫⁻ m, φ (m * y) ∂ν ∂μ := by
          refine lintegral_congr (fun y => ?_)
          have hb : Measurable (fun m => φ (m * y)) := hφ.comp (measurable_mul_const y)
          exact lintegral_const_mul _ hb

private theorem integrable_and_integral_eq_of_lintegral_weight_one {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hfin : ∀ y, β y ≠ ⊤) (hone : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (g : G → ℂ) (hg : Measurable g) (hgi : Integrable g μ) :
    Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν) μ ∧
      ∫ y, g y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν ∂μ := by
  have hkey := lintegral_eq_lintegral_weight_mul_lintegral μ ν β hβ hone
  have hgl : ∫⁻ y, ‖g y‖ₑ ∂μ < ⊤ := hgi.hasFiniteIntegral
  have hnorm : ∀ y (z : ℂ), ‖((β y).toReal : ℂ) * z‖ₑ = β y * ‖z‖ₑ := by
    intro y z
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin y)]
  have hHm : Measurable (fun p : G × G => ((β p.2).toReal : ℂ) * g (p.1 * p.2)) :=
    (Complex.measurable_ofReal.comp (hβ.comp measurable_snd).ennreal_toReal).mul
      (hg.comp (measurable_fst.mul measurable_snd))
  have hHi : Integrable (fun p : G × G => ((β p.2).toReal : ℂ) * g (p.1 * p.2)) (ν.prod μ) := by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖((β p.2).toReal : ℂ) * g (p.1 * p.2)‖ₑ ∂(ν.prod μ) < ⊤
    rw [lintegral_prod_symm _ hHm.enorm.aemeasurable]
    simp only [hnorm]
    have h2 : ∀ y, ∫⁻ m, β y * ‖g (m * y)‖ₑ ∂ν = β y * ∫⁻ m, ‖g (m * y)‖ₑ ∂ν := fun y =>
      lintegral_const_mul _ (hg.enorm.comp (measurable_mul_const y))
    simp only [h2]
    rw [← hkey _ hg.enorm]
    exact hgl
  have heq : ∀ y, ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν = ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν :=
    fun y => integral_const_mul _ _
  have hint0 : Integrable (fun y => ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν) μ :=
    hHi.integral_prod_right
  have hint : Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν) μ :=
    hint0.congr (ae_of_all _ heq)
  refine ⟨hint, ?_⟩
  have hKm : Measurable (fun p : G × G => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2) :=
    (Complex.measurable_ofReal.comp
      (hβ.comp (measurable_fst.inv.mul measurable_snd)).ennreal_toReal).mul (hg.comp measurable_snd)
  have hKi : Integrable (fun p : G × G => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2) (ν.prod μ) := by
    refine ⟨hKm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2‖ₑ ∂(ν.prod μ) < ⊤
    rw [lintegral_prod_symm _ hKm.enorm.aemeasurable]
    simp only [hnorm]
    have h3 : ∀ y, ∫⁻ m, β (m⁻¹ * y) * ‖g y‖ₑ ∂ν = ‖g y‖ₑ := by
      intro y
      have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
      rw [lintegral_mul_const _ hb, hone, one_mul]
    simp only [h3]
    exact hgl
  have hβone : ∀ y, ∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν = 1 := by
    intro y
    have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
    rw [integral_complex_ofReal, integral_toReal hb.aemeasurable (ae_of_all _ fun m => (hfin _).lt_top),
      hone, ENNReal.toReal_one, Complex.ofReal_one]
  calc ∫ y, g y ∂μ = ∫ y, (∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν) * g y ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show g y = (∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν) * g y
        rw [hβone y, one_mul]
    _ = ∫ y, ∫ m, ((β (m⁻¹ * y)).toReal : ℂ) * g y ∂ν ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ m, ∫ y, ((β (m⁻¹ * y)).toReal : ℂ) * g y ∂μ ∂ν :=
        (integral_prod_symm _ hKi).symm.trans (integral_prod _ hKi)
    _ = ∫ m, ∫ y, ((β y).toReal : ℂ) * g (m * y) ∂μ ∂ν := by
        refine integral_congr_ae (ae_of_all _ fun m => ?_)
        have h := integral_mul_left_eq_self (μ := μ) (fun y => ((β (m⁻¹ * y)).toReal : ℂ) * g y) m
        simp only [inv_mul_cancel_left] at h
        exact h.symm
    _ = ∫ y, ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν ∂μ :=
        (integral_prod _ hHi).symm.trans (integral_prod_symm _ hHi)
    _ = ∫ y, ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν ∂μ :=
        integral_congr_ae (ae_of_all _ heq)

theorem weil_formula_cutoff : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (ν : Measure G), IsClosed (N : Set G) → IsHaarSub (N : Set G) ν → ∀ β : G → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → (∀ f : G → ENNReal, Measurable f → ∫⁻ y, f y ∂μ = ∫⁻ y, β y * ∫⁻ m, f (m * y) ∂ν ∂μ) ∧ ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) μ ∧ ∫ y, f y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ N ν _hN hH β hβ hfin hone
  have hH' := hH
  unfold IsHaarSub at hH'
  haveI : IsFiniteMeasureOnCompacts ν := hH'.2.1
  haveI : SigmaFinite ν := inferInstance
  have hkey := lintegral_eq_lintegral_weight_mul_lintegral μ ν β hβ hone
  refine ⟨hkey, fun f hf => ?_⟩
  have hgm : Measurable (hf.aestronglyMeasurable.mk f) :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[μ] hf.aestronglyMeasurable.mk f := hf.aestronglyMeasurable.ae_eq_mk
  obtain ⟨hgi, hgeq⟩ := integrable_and_integral_eq_of_lintegral_weight_one μ ν β hβ hfin hone _ hgm (hf.congr hfg)
  have hEm : MeasurableSet (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}) :=
    measurableSet_toMeasurable _ _
  have hE0 : μ (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}) = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hfg
  have hsub : {y | f y ≠ hf.aestronglyMeasurable.mk f y} ⊆
      toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y} := subset_toMeasurable _ _
  have hind : Measurable ((toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
      (1 : G → ENNReal)) := measurable_one.indicator hEm
  have h0 := hkey _ hind
  rw [lintegral_indicator_one hEm, hE0] at h0
  have hIm : Measurable (fun y => β y * ∫⁻ m, (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
      (1 : G → ENNReal) (m * y) ∂ν) :=
    hβ.mul (hind.comp measurable_mul).lintegral_prod_left'
  have hae := (lintegral_eq_zero_iff' hIm.aemeasurable).mp h0.symm
  have hcong : (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) =ᵐ[μ]
      (fun y => ((β y).toReal : ℂ) * ∫ m, hf.aestronglyMeasurable.mk f (m * y) ∂ν) := by
    filter_upwards [hae] with y hy
    have hy' : β y * ∫⁻ m, (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
        (1 : G → ENNReal) (m * y) ∂ν = 0 := hy
    rcases mul_eq_zero.mp hy' with hb | hI
    · simp [hb]
    · congr 1
      have hmy : Measurable (fun m => (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
          (1 : G → ENNReal) (m * y)) := hind.comp (measurable_mul_const y)
      have hae2 := (lintegral_eq_zero_iff hmy).mp hI
      refine integral_congr_ae ?_
      filter_upwards [hae2] with m hm
      by_contra hne
      have hmE := hsub hne
      simp [Set.indicator_of_mem hmE] at hm
  refine ⟨hgi.congr hcong.symm, ?_⟩
  rw [integral_congr_ae hfg, hgeq, integral_congr_ae hcong]

end GlobalTheory
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_with_cutoff_subgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (ν : Measure G), IsClosed (N : Set G) → IsHaarSub (N : Set G) ν → ∀ β : G → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → (∀ f : G → ENNReal, Measurable f → ∫⁻ y, f y ∂μ = ∫⁻ y, β y * ∫⁻ m, f (m * y) ∂ν ∂μ) ∧ ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) μ ∧ ∫ y, f y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν ∂μ := by
  atlas_forward_decl GlobalTheory.weil_formula_cutoff
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.ConstTermNorm

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem continuous_integral_translate (ν : Measure G) (D : G → ℝ) (hDc : Continuous D)
    (hDi : ∀ g, D g⁻¹ = D g) (hDm : ∀ g h, D (g * h) ≤ D g + D h) (c C : ℝ) (hc : 0 ≤ c)
    (hν : Integrable (fun m => Real.exp (-(c * D m))) ν) (a : G → ℂ) (ha : Continuous a)
    (hb : ∀ g, ‖a g‖ ≤ C * Real.exp (-(c * D g))) :
    Continuous (fun g => ∫ m, a (m * g) ∂ν) := by
  have hC : 0 ≤ C := by
    have h1 := hb 1
    have h2 := Real.exp_pos (-(c * D 1))
    nlinarith [norm_nonneg (a 1)]
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hev : ∀ᶠ g in nhds g₀, D g < D g₀ + 1 :=
    hDc.continuousAt.eventually (gt_mem_nhds (lt_add_one (D g₀)))
  refine continuousAt_of_dominated
    (bound := fun m => C * Real.exp (c * (D g₀ + 1)) * Real.exp (-(c * D m))) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun g =>
      (ha.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  · filter_upwards [hev] with g hg
    refine Filter.Eventually.of_forall fun m => ?_
    have hm : D m ≤ D (m * g) + D g := by
      have h3 := hDm (m * g) g⁻¹
      rwa [mul_inv_cancel_right, hDi] at h3
    have k1 := mul_le_mul_of_nonneg_left hm hc
    have k2 := mul_le_mul_of_nonneg_left hg.le hc
    calc ‖a (m * g)‖ ≤ C * Real.exp (-(c * D (m * g))) := hb _
      _ ≤ C * Real.exp (c * (D g₀ + 1)) * Real.exp (-(c * D m)) := by
        rw [mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
        nlinarith
  · exact hν.const_mul _
  · exact Filter.Eventually.of_forall fun m =>
      (ha.comp (continuous_const.mul continuous_id)).continuousAt

theorem integrable_translate_mul (ν μ : Measure G) [SFinite ν] [SFinite μ] (D : G → ℝ) (hD0 : ∀ g, 0 ≤ D g)
    (hDi : ∀ g, D g⁻¹ = D g) (hDm : ∀ g h, D (g * h) ≤ D g + D h) (c C C' : ℝ) (hc : 0 ≤ c)
    (hν : Integrable (fun m => Real.exp (-(c / 2 * D m))) ν)
    (hμ : Integrable (fun m => Real.exp (-(c / 2 * D m))) μ) (a b : G → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ g, ‖a g‖ ≤ C * Real.exp (-(c * D g))) (hbb : ∀ g, ‖b g‖ ≤ C' * Real.exp (-(c * D g))) :
    Integrable (fun p : G × G => a (p.1 * p.2) * b p.2) (ν.prod μ) := by
  have hC : 0 ≤ C := by
    have h1 := hab 1
    have h2 := Real.exp_pos (-(c * D 1))
    nlinarith [norm_nonneg (a 1)]
  have hC' : 0 ≤ C' := by
    have h1 := hbb 1
    have h2 := Real.exp_pos (-(c * D 1))
    nlinarith [norm_nonneg (b 1)]
  have hmeas : AEStronglyMeasurable (fun p : G × G => a (p.1 * p.2) * b p.2) (ν.prod μ) :=
    ((ha.comp continuous_mul).mul (hb.comp continuous_snd)).aestronglyMeasurable
  refine Integrable.mono' ((hν.mul_prod hμ).const_mul (C * C')) hmeas
    (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨m, y⟩ := p
  have hm : D m ≤ D (m * y) + D y := by
    have h3 := hDm (m * y) y⁻¹
    rwa [mul_inv_cancel_right, hDi] at h3
  have k0 := mul_nonneg hc (hD0 (m * y))
  have k1 := mul_le_mul_of_nonneg_left hm hc
  show ‖a (m * y) * b y‖ ≤ C * C' * (Real.exp (-(c / 2 * D m)) * Real.exp (-(c / 2 * D y)))
  rw [norm_mul]
  calc ‖a (m * y)‖ * ‖b y‖ ≤ (C * Real.exp (-(c * D (m * y)))) * (C' * Real.exp (-(c * D y))) :=
        mul_le_mul (hab _) (hbb _) (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    _ = C * C' * Real.exp (-(c * D (m * y)) + -(c * D y)) := by rw [Real.exp_add]; ring
    _ ≤ C * C' * (Real.exp (-(c / 2 * D m)) * Real.exp (-(c / 2 * D y))) := by
        rw [← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (mul_nonneg hC hC')
        nlinarith

private theorem inner_mul_eq_inner_inv_of_isURepOn {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
    (m y : UJ ε) (w u : H) :
    ⟪w, σ (umat (m * y)) u⟫_ℂ = ⟪σ (umat m⁻¹) w, σ (umat y) u⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have e2 : umat m * umat m⁻¹ = 1 := congrArg (fun z : UJ ε => umat z) (mul_inv_cancel m)
  have hv : σ (umat m) (σ (umat m⁻¹) w) = w := by
    have h3 := hmul (umat m) m.2 (umat m⁻¹) m⁻¹.2
    rw [e2, h1] at h3
    have h4 := congrArg (fun T : H →L[ℂ] H => T w) h3
    simpa using h4.symm
  have hmy : σ (umat (m * y)) u = σ (umat m) (σ (umat y) u) := by
    have h3 := hmul (umat m) m.2 (umat y) y.2
    exact congrArg (fun T : H →L[ℂ] H => T u) h3
  let T : H →ₗᵢ[ℂ] H := ⟨(σ (umat m) : H →ₗ[ℂ] H), fun x => hiso (umat m) m.2 x⟩
  rw [hmy]
  conv_lhs => rw [← hv]
  exact T.inner_map_map (σ (umat m⁻¹) w) (σ (umat y) u)

private theorem dOp_nonneg_inv_subadditive_continuous (n : ℕ) (ε : Fin n → Bool) :
    (∀ g : UJ ε, 0 ≤ dOp (umat g)) ∧ (∀ g : UJ ε, dOp (umat g⁻¹) = dOp (umat g)) ∧
      (∀ g h : UJ ε, dOp (umat (g * h)) ≤ dOp (umat g) + dOp (umat h)) ∧
      Continuous (fun g : UJ ε => dOp (umat g)) := by
  obtain ⟨-, -, -, -, h5⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ g : UJ ε, dOp (umat g) = 0 := fun g => by
      rw [GlobalTheory.Count.Cartan.dOp_eq, Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) ℂ) (umat g) 0]
      letI : NormedRing (Matrix (Fin 0) (Fin 0) ℂ) := Matrix.instL2OpNormedRing
      exact Real.log_eq_zero.2 (Or.inl norm_zero)
    refine ⟨fun g => (h0 g).ge, fun g => by rw [h0, h0], fun g h => by rw [h0, h0, h0, add_zero], h5⟩
  · obtain ⟨-, h2, -⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
    exact ⟨fun g => (h2 g 1 hn).1, fun g => (h2 g 1 hn).2.1, fun g h => (h2 g h hn).2.2.1, h5⟩

private theorem nw_one_mem_mul_mem_inv_mem_isClosed {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) :
    (1 : UJ ε) ∈ NW ε W ∧ (∀ a ∈ NW ε W, ∀ b ∈ NW ε W, a * b ∈ NW ε W) ∧
      (∀ a ∈ NW ε W, a⁻¹ ∈ NW ε W) ∧ IsClosed (NW ε W) := by
  have hadd : ∀ x p q : Fin n → ℂ, herm (Jm ε) x (p + q) = herm (Jm ε) x p + herm (Jm ε) x q := by
    intro x p q
    simp only [herm, star_add, add_dotProduct]
  have hneg : ∀ x p : Fin n → ℂ, herm (Jm ε) x (-p) = -herm (Jm ε) x p := by
    intro x p
    simp only [herm, star_neg, neg_dotProduct]
  have hzero : ∀ x : Fin n → ℂ, herm (Jm ε) x 0 = 0 := by
    intro x
    simp only [herm, star_zero, zero_dotProduct]
  have hmulv : ∀ g h : UJ ε,
      umat (g * h) - 1 = (umat g - 1) * (umat h - 1) + (umat g - 1) + (umat h - 1) := by
    intro g h
    have e : umat (g * h) = umat g * umat h := rfl
    rw [e]
    noncomm_ring
  have hinv : ∀ g : UJ ε, umat g⁻¹ - 1 = -(umat g - 1) - (umat g⁻¹ - 1) * (umat g - 1) ∧
      umat g⁻¹ - 1 = -(umat g - 1) - (umat g - 1) * (umat g⁻¹ - 1) := by
    intro g
    have h1 : umat g⁻¹ * umat g = 1 := congrArg (fun z : UJ ε => umat z) (inv_mul_cancel g)
    have h2 : umat g * umat g⁻¹ = 1 := congrArg (fun z : UJ ε => umat z) (mul_inv_cancel g)
    constructor
    · rw [sub_mul, mul_sub, mul_sub, h1, mul_one, one_mul, one_mul]
      abel
    · rw [mul_sub, sub_mul, sub_mul, h2, mul_one, one_mul, one_mul]
      abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e0 : umat (1 : UJ ε) - 1 = 0 := sub_self (1 : Matrix (Fin n) (Fin n) ℂ)
    simp only [NW, Set.mem_setOf_eq, e0, zero_mulVec, hzero]
    exact ⟨fun _ _ => trivial, fun _ _ => W.zero_mem, fun _ _ _ => trivial⟩
  · intro a ha b hb
    simp only [NW, Set.mem_setOf_eq] at ha hb ⊢
    obtain ⟨a1, a2, a3⟩ := ha
    obtain ⟨b1, b2, b3⟩ := hb
    refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩ <;>
      rw [hmulv, add_mulVec, add_mulVec, ← mulVec_mulVec]
    · rw [b1 x hx, a1 x hx, mulVec_zero, add_zero, add_zero]
    · rw [a1 _ (b2 y hy), zero_add]
      exact W.add_mem (a2 y hy) (b2 y hy)
    · rw [hadd, hadd, a3 _ x hx, a3 y x hx, b3 y x hx, add_zero, add_zero]
  · intro g hg
    simp only [NW, Set.mem_setOf_eq] at hg ⊢
    obtain ⟨a1, a2, a3⟩ := hg
    have c1 : ∀ x ∈ W, (umat g⁻¹ - 1) *ᵥ x = 0 := by
      intro x hx
      rw [(hinv g).1, sub_mulVec, neg_mulVec, ← mulVec_mulVec, a1 x hx, mulVec_zero, neg_zero, sub_zero]
    refine ⟨c1, fun y hy => ?_, fun y x hx => ?_⟩
    · rw [(hinv g).1, sub_mulVec, neg_mulVec, ← mulVec_mulVec, c1 _ (a2 y hy), sub_zero]
      exact W.neg_mem (a2 y hy)
    · rw [(hinv g).2, sub_mulVec, neg_mulVec, ← mulVec_mulVec, sub_eq_add_neg, hadd, hneg, hneg,
        a3 y x hx, a3 _ x hx, neg_zero, add_zero]
  · have hcu : Continuous (fun g : UJ ε => umat g - 1) :=
      (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
    have hcv : ∀ y, Continuous (fun g : UJ ε => (umat g - 1) *ᵥ y) := fun y =>
      hcu.matrix_mulVec continuous_const
    simp only [NW, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq (hcv x) continuous_const) (IsClosed.inter (isClosed_iInter fun y =>
      isClosed_iInter fun _ => (W.closed_of_finiteDimensional).preimage (hcv y))
      (isClosed_iInter fun y => isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq ?_ continuous_const))
    simp only [herm]
    unfold dotProduct
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (hcv y).star).mul continuous_const

end General

theorem constTerm_inner : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ β : UJ ε → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (u v v' : H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 8 * n * rkR ε < c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v', σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v'⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → Continuous (fun g : UJ ε => (∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν)) ∧ Integrable (fun g : UJ ε => ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) * star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν))) (muG ε) ∧ ∫ g : UJ ε, ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) * star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν)) ∂(muG ε) = (∫ m, ⟪v, σ (umat m) v'⟫_ℂ ∂ν) * ((‖u‖ ^ 2 / d : ℝ) : ℂ) := by
  intro n ε W ν hW hν β hβ hβt hβ1 H _ _ _ σ d c u v v' hσ hd hc hf hf' hvv
  obtain ⟨hD0, hDi, hDm, hDc⟩ := dOp_nonneg_inv_subadditive_continuous n ε
  obtain ⟨n1, nmul, ninv, ncl⟩ := nw_one_mem_mul_mem_inv_mem_isClosed ε W
  have hr := GlobalTheory.T.haar_subgroup_bi_invariant n ε W ν hW hν
  obtain ⟨-, hνi⟩ := GlobalTheory.T.unipotentRadical_volume_growth n ε W ν hW hν
  haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
  have hnr : (0 : ℝ) ≤ (n : ℝ) * (rkR ε : ℝ) := by positivity
  have hc0 : 0 ≤ c := by nlinarith
  have hνc : Integrable (fun m : UJ ε => Real.exp (-(c * dOp (umat m)))) ν := hνi c (by nlinarith)
  have hνc2 : Integrable (fun m : UJ ε => Real.exp (-(c / 2 * dOp (umat m)))) ν :=
    hνi (c / 2) (by nlinarith)
  have hμc2 : Integrable (fun m : UJ ε => Real.exp (-(c / 2 * dOp (umat m)))) (muG ε) := by
    obtain ⟨C0, -, hC0⟩ := GlobalTheory.BallVol.ballVol n ε
    exact GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth (UJ ε) (muG ε) (fun g => dOp (umat g)) _ (c / 2) C0
      hDc.measurable hD0 hC0 (by nlinarith)
  obtain ⟨C1, hC1⟩ := hf
  obtain ⟨C2, hC2⟩ := hf'
  have hcu : Continuous (fun g : UJ ε => umat g) := Units.continuous_val.comp continuous_subtype_val
  have hsc : ∀ x : H, Continuous (fun g : UJ ε => σ (umat g) x) := fun x =>
    (hσ.2.2 x).comp_continuous hcu (fun g => g.2)
  have cf : Continuous (fun g : UJ ε => ⟪v, σ (umat g) u⟫_ℂ) := continuous_const.inner (hsc u)
  have cf' : Continuous (fun g : UJ ε => ⟪v', σ (umat g) u⟫_ℂ) := continuous_const.inner (hsc u)
  have hconj : ∀ F : UJ ε → ℂ, ∫ x, star (F x) ∂ν = star (∫ x, F x ∂ν) := fun F => by
    simpa using integral_conj (μ := ν) (f := F)
  have hP := integrable_translate_mul ν (muG ε) (fun g => dOp (umat g)) hD0 hDi hDm c C2 C1 hc0 hνc2 hμc2
    (fun g => star ⟪v', σ (umat g) u⟫_ℂ) (fun g => ⟪v, σ (umat g) u⟫_ℂ) cf'.star cf
    (fun g => (norm_star _).trans_le (hC2 g)) hC1
  have hνN : ∀ᵐ m ∂ν, m ∈ NW ε W := ae_iff.2 hν.2.2.1
  have hF' : ∀ y : UJ ε, ∀ m₀ ∈ NW ε W, (∫ m, ⟪v', σ (umat (m * (m₀ * y))) u⟫_ℂ ∂ν) =
      ∫ m, ⟪v', σ (umat (m * y)) u⟫_ℂ ∂ν := by
    intro y m₀ hm₀
    have e' : Measure.map (MeasurableEquiv.mulRight m₀) ν = ν := hr.1 m₀ hm₀
    conv_rhs => rw [← e']
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact congrArg (fun z : UJ ε => ⟪v', σ (umat z) u⟫_ℂ) (mul_assoc x m₀ y).symm
  have hin : ∀ y : UJ ε, (∫ m, ⟪v, σ (umat (m * y)) u⟫_ℂ *
      star (∫ k, ⟪v', σ (umat (k * (m * y))) u⟫_ℂ ∂ν) ∂ν) =
      (∫ m, ⟪v, σ (umat (m * y)) u⟫_ℂ ∂ν) * star (∫ k, ⟪v', σ (umat (k * y)) u⟫_ℂ ∂ν) := by
    intro y
    rw [← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [hνN] with m hm
    rw [hF' y m hm]
  have hpt : ∀ y : UJ ε, (∫ m, star ⟪v', σ (umat (m * y)) u⟫_ℂ * ⟪v, σ (umat y) u⟫_ℂ ∂ν) =
      ⟪v, σ (umat y) u⟫_ℂ * star (∫ m, ⟪v', σ (umat (m * y)) u⟫_ℂ ∂ν) := by
    intro y
    rw [integral_mul_const, hconj, mul_comm]
  have hhint : Integrable (fun y : UJ ε => ⟪v, σ (umat y) u⟫_ℂ *
      star (∫ m, ⟪v', σ (umat (m * y)) u⟫_ℂ ∂ν)) (muG ε) :=
    hP.integral_prod_right.congr (Filter.Eventually.of_forall fun y => hpt y)
  let N : Subgroup (UJ ε) :=
    { carrier := NW ε W, mul_mem' := fun {a b} ha hb => nmul a ha b hb, one_mem' := n1,
      inv_mem' := fun {a} ha => ninv a ha }
  obtain ⟨-, hU⟩ := GlobalTheory.T.weil_formula_with_cutoff_subgroup (UJ ε) (muG ε) N ν ncl hν β hβ hβt hβ1
  obtain ⟨hUi, hUe⟩ := hU _ hhint
  have key : ∀ m : UJ ε, ∫ y, star ⟪v', σ (umat (m * y)) u⟫_ℂ * ⟪v, σ (umat y) u⟫_ℂ ∂(muG ε) =
      ⟪u, u⟫_ℂ * ⟪v, σ (umat m⁻¹) v'⟫_ℂ / (d : ℂ) := by
    intro m
    rw [← (hd.2 u v u (σ (umat m⁻¹) v')).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show star ⟪v', σ (umat (m * y)) u⟫_ℂ * ⟪v, σ (umat y) u⟫_ℂ = _
    rw [inner_mul_eq_inner_inv_of_isURepOn σ hσ m y v' u]
    exact mul_comm _ _
  have hinvI : ∫ m, ⟪v, σ (umat m⁻¹) v'⟫_ℂ ∂ν = ∫ m, ⟪v, σ (umat m) v'⟫_ℂ ∂ν := by
    have e' : Measure.map (MeasurableEquiv.inv (UJ ε)) ν = ν := hr.2
    conv_rhs => rw [← e']
    rw [integral_map_equiv]
    rfl
  refine ⟨continuous_integral_translate ν (fun g => dOp (umat g)) hDc hDi hDm c C1 hc0 hνc
    (fun g => ⟪v, σ (umat g) u⟫_ℂ) cf hC1, ?_, ?_⟩
  · refine hUi.congr (Filter.Eventually.of_forall fun g => ?_)
    dsimp only
    rw [hin g]
  · have s1 : (∫ g : UJ ε, ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) *
        star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν)) ∂(muG ε)) =
        ∫ y, ⟪v, σ (umat y) u⟫_ℂ * star (∫ m, ⟪v', σ (umat (m * y)) u⟫_ℂ ∂ν) ∂(muG ε) := by
      rw [hUe]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      dsimp only
      rw [hin g]
    have s2 : (∫ y, ⟪v, σ (umat y) u⟫_ℂ * star (∫ m, ⟪v', σ (umat (m * y)) u⟫_ℂ ∂ν) ∂(muG ε)) =
        ∫ y, ∫ m, star ⟪v', σ (umat (m * y)) u⟫_ℂ * ⟪v, σ (umat y) u⟫_ℂ ∂ν ∂(muG ε) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => (hpt y).symm)
    have s3 := integral_integral_swap (μ := ν) (ν := muG ε)
      (f := fun m y => star ⟪v', σ (umat (m * y)) u⟫_ℂ * ⟪v, σ (umat y) u⟫_ℂ) hP
    rw [s1, s2, ← s3]
    simp_rw [key]
    have hu : ⟪u, u⟫_ℂ = ((‖u‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K u
    rw [integral_div, integral_const_mul, hinvI, hu]
    push_cast
    ring

end GlobalTheory.Dec.ConstTermNorm
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_rep_matrix_coefficient_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ β : UJ ε → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (u v v' : H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 8 * n * rkR ε < c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v', σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v'⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → Continuous (fun g : UJ ε => (∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν)) ∧ Integrable (fun g : UJ ε => ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) * star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν))) (muG ε) ∧ ∫ g : UJ ε, ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) * star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν)) ∂(muG ε) = (∫ m, ⟪v, σ (umat m) v'⟫_ℂ ∂ν) * ((‖u‖ ^ 2 / d : ℝ) : ℂ) := by
  atlas_forward_decl GlobalTheory.Dec.ConstTermNorm.constTerm_inner
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.TorusLip

lemma sq_integral_le {r : ℝ → ℝ} (hr : Continuous r) :
    (∫ t in (0:ℝ)..1, r t) ^ 2 ≤ ∫ t in (0:ℝ)..1, r t ^ 2 := by
  set a := ∫ t in (0:ℝ)..1, r t with ha
  have h1 : IntervalIntegrable r MeasureTheory.volume 0 1 := hr.intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun t => r t ^ 2) MeasureTheory.volume 0 1 :=
    (hr.pow 2).intervalIntegrable 0 1
  have hnn : 0 ≤ ∫ t in (0:ℝ)..1, (r t - a) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
  have e : ∀ t, (r t - a) ^ 2 = r t ^ 2 - (2 * a * r t - a ^ 2) := fun t => by ring
  simp_rw [e] at hnn
  rw [intervalIntegral.integral_sub h2 ((h1.const_mul (2 * a)).sub intervalIntegrable_const),
    intervalIntegral.integral_sub (h1.const_mul (2 * a)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hnn
  simp only [sub_zero, one_smul, smul_eq_mul, one_mul] at hnn
  nlinarith

lemma torus_lipschitz_l2_bound {G ι : Type} [Fintype ι] [TopologicalSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [SFinite μ] (β : G → ℝ) (hβ : Measurable β) (hβ0 : ∀ g, 0 ≤ β g)
    (Φ : ι → ℝ → G → ℂ) (hΦ : ∀ i, Continuous fun p : ℝ × G => Φ i p.1 p.2) (D : G → ℂ) (M s : ℝ) (hM : 0 ≤ M)
    (hs : |s| ≤ 1) (B : ι → ℝ)
    (hD : ∀ g, ∃ y : ι → ℝ, ∑ i, y i ^ 2 ≤ M ∧ D g = ∫ t in (0:ℝ)..s, ∑ i, (y i : ℂ) * Φ i t g)
    (hB : ∀ i t, |t| ≤ 1 → Integrable (fun g => β g * ‖Φ i t g‖ ^ 2) μ ∧ ∫ g, β g * ‖Φ i t g‖ ^ 2 ∂μ ≤ B i) :
    ∫ g, β g * ‖D g‖ ^ 2 ∂μ ≤ M * s ^ 2 * ∑ i, B i := by
  set q : ι → G → ℝ := fun i g => ∫ u in (0:ℝ)..1, β g * ‖Φ i (s * u) g‖ ^ 2 with hqdef
  have hΦc : ∀ i g, Continuous fun u : ℝ => Φ i (s * u) g := fun i g =>
    (hΦ i).comp ((continuous_const.mul continuous_id).prodMk continuous_const)
  have hpt : ∀ g, β g * ‖D g‖ ^ 2 ≤ M * s ^ 2 * ∑ i, q i g := by
    intro g
    obtain ⟨y, hy, hDg⟩ := hD g
    set F : ℝ → ℂ := fun t => ∑ i, (y i : ℂ) * Φ i t g with hF
    have hFc : Continuous F := continuous_finset_sum _ (fun i _ =>
      continuous_const.mul ((hΦ i).comp (continuous_id.prodMk continuous_const)))
    have hFs : Continuous fun u : ℝ => F (s * u) := hFc.comp (continuous_const.mul continuous_id)
    have hD' : D g = s • ∫ u in (0:ℝ)..1, F (s * u) := by
      rw [hDg, intervalIntegral.smul_integral_comp_mul_left, mul_zero, mul_one]
    have h1 : ‖D g‖ ^ 2 ≤ s ^ 2 * ∫ u in (0:ℝ)..1, ‖F (s * u)‖ ^ 2 := by
      have hn : ‖∫ u in (0:ℝ)..1, F (s * u)‖ ≤ ∫ u in (0:ℝ)..1, ‖F (s * u)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
      have hcs := sq_integral_le (r := fun u => ‖F (s * u)‖) hFs.norm
      rw [hD', norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg s)
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
    have h2 : ∀ u, ‖F (s * u)‖ ^ 2 ≤ M * ∑ i, ‖Φ i (s * u) g‖ ^ 2 := by
      intro u
      have a1 : ‖F (s * u)‖ ≤ ∑ i, |y i| * ‖Φ i (s * u) g‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_)))
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have a2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |y i|) (fun i => ‖Φ i (s * u) g‖)
      simp only [sq_abs] at a2
      have a3 : 0 ≤ ∑ i, ‖Φ i (s * u) g‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      calc ‖F (s * u)‖ ^ 2 ≤ (∑ i, |y i| * ‖Φ i (s * u) g‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a1 2
        _ ≤ (∑ i, y i ^ 2) * ∑ i, ‖Φ i (s * u) g‖ ^ 2 := a2
        _ ≤ M * ∑ i, ‖Φ i (s * u) g‖ ^ 2 := mul_le_mul_of_nonneg_right hy a3
    have h3 : ∫ u in (0:ℝ)..1, ‖F (s * u)‖ ^ 2 ≤ ∫ u in (0:ℝ)..1, M * ∑ i, ‖Φ i (s * u) g‖ ^ 2 :=
      intervalIntegral.integral_mono_on zero_le_one ((hFs.norm.pow 2).intervalIntegrable 0 1)
        ((continuous_const.mul (continuous_finset_sum _ (fun i _ => ((hΦc i g).norm.pow 2)))).intervalIntegrable 0 1)
        (fun u _ => h2 u)
    have h4 : ∫ u in (0:ℝ)..1, M * ∑ i, ‖Φ i (s * u) g‖ ^ 2 =
        M * ∑ i, ∫ u in (0:ℝ)..1, ‖Φ i (s * u) g‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finset_sum (f := fun i u => ‖Φ i (s * u) g‖ ^ 2)
          (fun i _ => ((hΦc i g).norm.pow 2).intervalIntegrable 0 1)]
    have h5 : ∑ i, q i g = β g * ∑ i, ∫ u in (0:ℝ)..1, ‖Φ i (s * u) g‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => intervalIntegral.integral_const_mul _ _)
    rw [h5]
    have h6 : ‖D g‖ ^ 2 ≤ s ^ 2 * (M * ∑ i, ∫ u in (0:ℝ)..1, ‖Φ i (s * u) g‖ ^ 2) := by
      rw [← h4]; exact h1.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg s))
    calc β g * ‖D g‖ ^ 2 ≤ β g * (s ^ 2 * (M * ∑ i, ∫ u in (0:ℝ)..1, ‖Φ i (s * u) g‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h6 (hβ0 g)
      _ = M * s ^ 2 * (β g * ∑ i, ∫ u in (0:ℝ)..1, ‖Φ i (s * u) g‖ ^ 2) := by ring
  have hsu : ∀ u ∈ Set.Icc (0:ℝ) 1, |s * u| ≤ 1 := by
    intro u hu
    rw [abs_mul, abs_of_nonneg hu.1]
    nlinarith [abs_nonneg s, hu.2, hu.1]
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hmem : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)), u ∈ Set.Icc (0:ℝ) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    rw [Set.uIoc_of_le zero_le_one] at hu
    exact ⟨hu.1.le, hu.2⟩
  have hq : ∀ i, Integrable (q i) μ ∧ ∫ g, q i g ∂μ ≤ B i := by
    intro i
    set f : ℝ → G → ℝ := fun u g => β g * ‖Φ i (s * u) g‖ ^ 2 with hf
    have hmeas : Measurable (Function.uncurry f) := by
      have hc : Continuous fun p : ℝ × G => Φ i (s * p.1) p.2 :=
        (hΦ i).comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
      exact (hβ.comp measurable_snd).mul (hc.measurable.norm.pow_const 2)
    have hint : Integrable (Function.uncurry f)
        ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)).prod μ) := by
      rw [integrable_prod_iff hmeas.aestronglyMeasurable]
      refine ⟨?_, ?_⟩
      · filter_upwards [hmem] with u hu
        exact (hB i (s * u) (hsu u hu)).1
      · refine (integrable_const (B i)).mono' hmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
        filter_upwards [hmem] with u hu
        have e : ∫ g, ‖Function.uncurry f (u, g)‖ ∂μ = ∫ g, β g * ‖Φ i (s * u) g‖ ^ 2 ∂μ := by
          congr 1; funext g
          show ‖β g * ‖Φ i (s * u) g‖ ^ 2‖ = β g * ‖Φ i (s * u) g‖ ^ 2
          rw [Real.norm_eq_abs]
          exact abs_of_nonneg (mul_nonneg (hβ0 g) (sq_nonneg _))
        rw [e, Real.norm_eq_abs,
          abs_of_nonneg (integral_nonneg (fun g => mul_nonneg (hβ0 g) (sq_nonneg _)))]
        exact (hB i (s * u) (hsu u hu)).2
    refine ⟨?_, ?_⟩
    · have e : q i = fun g => ∫ u, f u g ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) := by
        funext g
        show ∫ u in (0:ℝ)..1, β g * ‖Φ i (s * u) g‖ ^ 2 =
          ∫ u, β g * ‖Φ i (s * u) g‖ ^ 2 ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1))
        rw [intervalIntegral.integral_of_le zero_le_one, Set.uIoc_of_le zero_le_one]
      rw [e]; exact hint.integral_prod_right
    · have sw := MeasureTheory.intervalIntegral_integral_swap hint
      calc ∫ g, q i g ∂μ = ∫ u in (0:ℝ)..1, ∫ g, f u g ∂μ := sw.symm
        _ ≤ ∫ u in (0:ℝ)..1, B i := by
          apply intervalIntegral.integral_mono_on zero_le_one
          · exact intervalIntegrable_iff.2 hint.integral_prod_left
          · exact intervalIntegrable_const
          · intro u hu; exact (hB i (s * u) (hsu u hu)).2
        _ = B i := by simp
  have hg_int : Integrable (fun g => M * s ^ 2 * ∑ i, q i g) μ :=
    (integrable_finset_sum _ (fun i _ => (hq i).1)).const_mul _
  calc ∫ g, β g * ‖D g‖ ^ 2 ∂μ ≤ ∫ g, M * s ^ 2 * ∑ i, q i g ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun g => mul_nonneg (hβ0 g) (sq_nonneg _)))
          hg_int (Filter.Eventually.of_forall hpt)
    _ = M * s ^ 2 * ∑ i, ∫ g, q i g ∂μ := by
        rw [integral_const_mul, integral_finset_sum _ (fun i _ => (hq i).1)]
    _ ≤ M * s ^ 2 * ∑ i, B i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hq i).2)) (mul_nonneg hM (sq_nonneg s))

section Abstract

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

lemma decay_shift {δ : G → ℝ} (hinv : ∀ g, δ g⁻¹ = δ g) (hsub : ∀ g g', δ (g * g') ≤ δ g + δ g') {c C : ℝ}
    (hc : 0 ≤ c) {f : G → ℂ} (hf : ∀ g, ‖f g‖ ≤ C * Real.exp (-(c * δ g))) (x y g : G) :
    ‖f (x * g * y)‖ ≤ C * Real.exp (c * (δ x + δ y)) * Real.exp (-(c * δ g)) := by
  have hC : 0 ≤ C := by
    by_contra h
    have h' : C * Real.exp (-(c * δ 1)) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) (Real.exp_pos _)
    linarith [norm_nonneg (f 1), hf 1]
  have hd : δ g ≤ δ x + δ (x * g * y) + δ y := by
    have e : g = x⁻¹ * (x * g * y) * y⁻¹ := by group
    have h1 := hsub (x⁻¹ * (x * g * y)) y⁻¹
    have h2 := hsub x⁻¹ (x * g * y)
    rw [← e, hinv] at h1
    rw [hinv] at h2
    linarith
  have hm := mul_le_mul_of_nonneg_left hd hc
  calc ‖f (x * g * y)‖ ≤ C * Real.exp (-(c * δ (x * g * y))) := hf _
    _ ≤ C * Real.exp (c * (δ x + δ y) + -(c * δ g)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        nlinarith
    _ = C * Real.exp (c * (δ x + δ y)) * Real.exp (-(c * δ g)) := by rw [Real.exp_add]; ring

omit [IsTopologicalGroup G] in
lemma inner_move {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) (x g : G) (v u : H) :
    ⟪ρ x⁻¹ v, ρ g u⟫_ℂ = ⟪v, ρ (x * g) u⟫_ℂ := by
  have hiso : ∀ h : G, ∀ a b : H, ⟪ρ h a, ρ h b⟫_ℂ = ⟪a, b⟫_ℂ := by
    intro h a b
    let L : H →ₗᵢ[ℂ] H := { toLinearMap := (ρ h : H →ₗ[ℂ] H), norm_map' := hρ.2.2.1 h }
    exact L.inner_map_map a b
  have h1 : ρ x (ρ x⁻¹ v) = v := by
    have := congrArg (fun T : H →L[ℂ] H => T v) (hρ.2.1 x x⁻¹)
    simp only [mul_inv_cancel, hρ.1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  have h2 : ρ x (ρ g u) = ρ (x * g) u := by
    rw [hρ.2.1]; rfl
  rw [← hiso x (ρ x⁻¹ v) (ρ g u), h1, h2]

omit [IsTopologicalGroup G] in
lemma hasDerivAt_coef {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) {b : ℝ → G} (hb : ∀ s t, b (s + t) = b s * b t)
    {w u : H} (hd : HasDerivAt (fun s => ρ (b s) w) u 0) (v : H) (x : G) (t : ℝ) :
    HasDerivAt (fun s => ⟪v, ρ (x * b s) w⟫_ℂ) ⟪v, ρ (x * b t) u⟫_ℂ t := by
  set L : H →L[ℝ] ℂ := ((innerSL ℂ v).comp (ρ (x * b t))).restrictScalars ℝ with hL
  have e : ∀ s, ⟪v, ρ (x * b s) w⟫_ℂ = L (ρ (b (s - t)) w) := by
    intro s
    have hs : x * b s = (x * b t) * b (s - t) := by
      rw [mul_assoc, ← hb]; congr 2; ring
    rw [hs, hρ.2.1, hL]
    simp
  have hd' : HasDerivAt (fun s => ρ (b (s - t)) w) u t :=
    HasDerivAt.comp_sub_const t t (by rwa [sub_self])
  have key := HasFDerivAt.comp_hasDerivAt t L.hasFDerivAt hd'
  have hf : (fun s => ⟪v, ρ (x * b s) w⟫_ℂ) = L ∘ (fun s => ρ (b (s - t)) w) := by
    funext s; exact e s
  rw [hf]
  refine key.congr_deriv ?_
  rw [hL]
  simp

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

lemma integrable_coef {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) {δ : G → ℝ} (hinv : ∀ g, δ g⁻¹ = δ g)
    (hsub : ∀ g g', δ (g * g') ≤ δ g + δ g') {c : ℝ} (hc : 0 ≤ c) {ν : Measure G}
    (hν : Integrable (fun m => Real.exp (-(c * δ m))) ν) {v u : H}
    (hu : ∃ C : ℝ, ∀ g, ‖⟪v, ρ g u⟫_ℂ‖ ≤ C * Real.exp (-(c * δ g))) (g : G) :
    Integrable (fun m => ⟪v, ρ (m * g) u⟫_ℂ) ν := by
  obtain ⟨C, hC⟩ := hu
  have hCn : 0 ≤ C := by
    by_contra h
    have h1 := hC 1
    have h2 : C * Real.exp (-(c * δ 1)) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) (Real.exp_pos _)
    linarith [norm_nonneg (⟪v, ρ 1 u⟫_ℂ)]
  have hcont : Continuous fun m : G => ⟪v, ρ (m * g) u⟫_ℂ :=
    continuous_const.inner ((hρ.2.2.2 u).comp (continuous_id.mul continuous_const))
  refine Integrable.mono' (hν.const_mul (C * Real.exp (c * δ g))) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun m => ?_)
  have h2 : δ m ≤ δ (m * g) + δ g := by
    have := hsub (m * g) g⁻¹
    rwa [mul_inv_cancel_right, hinv] at this
  have hm := mul_le_mul_of_nonneg_left h2 hc
  calc ‖⟪v, ρ (m * g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * δ (m * g))) := hC _
    _ ≤ C * Real.exp (c * δ g + -(c * δ m)) := by
      apply mul_le_mul_of_nonneg_left _ hCn
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = C * Real.exp (c * δ g) * Real.exp (-(c * δ m)) := by rw [Real.exp_add]; ring

lemma ftc {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) {δ : G → ℝ} (hδ : Continuous δ) (hinv : ∀ g, δ g⁻¹ = δ g)
    (hsub : ∀ g g', δ (g * g') ≤ δ g + δ g') {c : ℝ} (hc : 0 ≤ c) {ν : Measure G} [SFinite ν]
    (hν : Integrable (fun m => Real.exp (-(c * δ m))) ν) {b : ℝ → G} (hbc : Continuous b) (hb0 : b 0 = 1)
    (hb : ∀ s t, b (s + t) = b s * b t) {v w u : H} (hd : HasDerivAt (fun s => ρ (b s) w) u 0)
    (hw : ∃ C : ℝ, ∀ g, ‖⟪v, ρ g w⟫_ℂ‖ ≤ C * Real.exp (-(c * δ g)))
    (hu : ∃ C : ℝ, ∀ g, ‖⟪v, ρ g u⟫_ℂ‖ ≤ C * Real.exp (-(c * δ g))) (g : G) (s : ℝ) :
    (∫ m, ⟪v, ρ (m * (g * b s)) w⟫_ℂ ∂ν) - ∫ m, ⟪v, ρ (m * g) w⟫_ℂ ∂ν =
      ∫ t in (0:ℝ)..s, ∫ m, ⟪v, ρ (m * (g * b t)) u⟫_ℂ ∂ν := by
  have hcontF' : Continuous fun p : G × ℝ => ⟪v, ρ (p.1 * (g * b p.2)) u⟫_ℂ :=
    continuous_const.inner ((hρ.2.2.2 u).comp
      (continuous_fst.mul (continuous_const.mul (hbc.comp continuous_snd))))
  have hpt : ∀ m : G, ⟪v, ρ (m * (g * b s)) w⟫_ℂ - ⟪v, ρ (m * g) w⟫_ℂ =
      ∫ t in (0:ℝ)..s, ⟪v, ρ (m * (g * b t)) u⟫_ℂ := by
    intro m
    have hder : ∀ t ∈ Set.uIcc (0:ℝ) s, HasDerivAt (fun r => ⟪v, ρ (m * (g * b r)) w⟫_ℂ)
        ⟪v, ρ (m * (g * b t)) u⟫_ℂ t := by
      intro t _
      have := hasDerivAt_coef hρ hb hd v (m * g) t
      simpa only [mul_assoc] using this
    have hint : IntervalIntegrable (fun t => ⟪v, ρ (m * (g * b t)) u⟫_ℂ) MeasureTheory.volume 0 s :=
      (hcontF'.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable 0 s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint, hb0, mul_one]
  obtain ⟨K, hK⟩ := (isCompact_uIcc (a := (0:ℝ)) (b := s)).exists_bound_of_continuousOn
    ((hδ.comp hbc).continuousOn)
  obtain ⟨C, hC⟩ := hu
  have hCn : 0 ≤ C := by
    by_contra h
    have h1 := hC 1
    have h2 : C * Real.exp (-(c * δ 1)) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) (Real.exp_pos _)
    linarith [norm_nonneg (⟪v, ρ 1 u⟫_ℂ)]
  have hbd : ∀ t ∈ Set.uIcc (0:ℝ) s, ∀ m, ‖⟪v, ρ (m * (g * b t)) u⟫_ℂ‖ ≤
      C * Real.exp (c * (δ g + K)) * Real.exp (-(c * δ m)) := by
    intro t ht m
    have h1 : δ m ≤ δ (m * (g * b t)) + δ g + δ (b t) := by
      have a1 := hsub (m * (g * b t)) (g * b t)⁻¹
      have a2 := hsub g (b t)
      rw [mul_inv_cancel_right, hinv] at a1
      linarith
    have h2 : δ (b t) ≤ K := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hK t ht)
    have h3 := mul_le_mul_of_nonneg_left h1 hc
    have h4 := mul_le_mul_of_nonneg_left h2 hc
    calc ‖⟪v, ρ (m * (g * b t)) u⟫_ℂ‖ ≤ C * Real.exp (-(c * δ (m * (g * b t)))) := hC _
      _ ≤ C * Real.exp (c * (δ g + K) + -(c * δ m)) := by
        apply mul_le_mul_of_nonneg_left _ hCn
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = C * Real.exp (c * (δ g + K)) * Real.exp (-(c * δ m)) := by rw [Real.exp_add]; ring
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hprod : Integrable (Function.uncurry fun t m => ⟪v, ρ (m * (g * b t)) u⟫_ℂ)
      ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) s)).prod ν) := by
    have hmaj : Integrable (fun p : ℝ × G => (1:ℝ) * (C * Real.exp (c * (δ g + K)) * Real.exp (-(c * δ p.2))))
        ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) s)).prod ν) :=
      (integrable_const (1:ℝ)).mul_prod (hν.const_mul _)
    refine hmaj.mono' (hcontF'.comp continuous_swap).aestronglyMeasurable ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_uIoc)] with p hp
    have := hbd p.1 (Set.uIoc_subset_uIcc hp) p.2
    rw [one_mul]; exact this
  have hi1 : Integrable (fun m => ⟪v, ρ (m * (g * b s)) w⟫_ℂ) ν :=
    integrable_coef hρ hinv hsub hc hν hw (g * b s)
  have hi0 : Integrable (fun m => ⟪v, ρ (m * g) w⟫_ℂ) ν := integrable_coef hρ hinv hsub hc hν hw g
  rw [← integral_sub hi1 hi0]
  simp_rw [hpt]
  exact (MeasureTheory.intervalIntegral_integral_swap hprod).symm

lemma integral_conj {ν : Measure G} {x : G} {r : ℝ} (hr : 0 ≤ r)
    (h : ν.map (fun m => x * m * x⁻¹) = ENNReal.ofReal r • ν) (f : G → ℂ) :
    ∫ m, f (x * m * x⁻¹) ∂ν = (r : ℂ) * ∫ m, f m ∂ν := by
  let e : G ≃ₜ G := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)
  have he : (e.toMeasurableEquiv : G → G) = fun m => x * m * x⁻¹ := rfl
  have key := integral_map_equiv e.toMeasurableEquiv f (μ := ν)
  simp only [he] at key
  rw [h, integral_smul_measure, ENNReal.toReal_ofReal hr] at key
  rw [← key, Complex.real_smul]

lemma integral_right {ν : Measure G} {x : G} (h : ν.map (fun m => m * x) = ν) (f : G → ℂ) :
    ∫ m, f (m * x) ∂ν = ∫ m, f m ∂ν := by
  have he : ((Homeomorph.mulRight x).toMeasurableEquiv : G → G) = fun m => m * x := rfl
  have key := integral_map_equiv (Homeomorph.mulRight x).toMeasurableEquiv f (μ := ν)
  simp only [he] at key
  rw [h] at key
  exact key.symm

end Abstract

variable {n : ℕ} {ε : Fin n → Bool}

lemma isURep_umat {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) :
    IsURep fun g : UJ ε => σ (umat g) := by
  have hm : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  refine ⟨hσ.1.1, fun a b => hσ.1.2 _ (hm a) _ (hm b), fun g v => hσ.2.1 _ (hm g) v, fun v => ?_⟩
  exact (hσ.2.2 v).comp_continuous (Units.continuous_val.comp continuous_subtype_val) hm

lemma onePar {a : ℝ → UJ ε} {X : Matrix (Fin n) (Fin n) ℂ}
    (ha : ∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • X)) :
    Continuous a ∧ a 0 = 1 ∧ (∀ s t, a (s + t) = a s * a t) ∧ ∀ s, (a s)⁻¹ = a (-s) := by
  have hexp : ∀ s t : ℝ, NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
    intro s t
    rw [Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have hadd : ∀ s t, a (s + t) = a s * a t := fun s t => Subtype.ext (Units.ext (by
    change umat (a (s + t)) = umat (a s) * umat (a t)
    rw [ha, ha, ha, hexp]))
  have h0 : a 0 = 1 := Subtype.ext (Units.ext (by
    change umat (a 0) = 1
    rw [ha]; simp))
  have hinv : ∀ s, (a s)⁻¹ = a (-s) := fun s =>
    inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  have hsm : Continuous fun s : ℝ => (s : ℂ) • X := Complex.continuous_ofReal.smul continuous_const
  have hc : Continuous fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
    exact NormedSpace.exp_continuous.comp hsm
  refine ⟨?_, h0, hadd, hinv⟩
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact hc.congr (fun s => (ha s).symm)
  · refine (hc.comp continuous_neg).congr (fun s => ?_)
    show NormedSpace.exp (((-s : ℝ) : ℂ) • X) = umat (a s)⁻¹
    rw [hinv, ha]

lemma conj_facts {k : UJ ε} (hk : umat k ∈ Kset ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    inG ε (umat k⁻¹ * X * umat k) ∧
      ((umat k⁻¹ * X * umat k) * (umat k⁻¹ * X * umat k)ᴴ).trace = (X * Xᴴ).trace ∧
      ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • (umat k⁻¹ * X * umat k)) =
        umat k⁻¹ * NormedSpace.exp ((s : ℂ) • X) * umat k := by
  obtain ⟨hku, hkJ⟩ := hk
  have hinvk : umat k⁻¹ = star (umat k) := by
    have h1 : umat k⁻¹ * umat k = 1 := by
      change (((k⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    have h2 : star (umat k) * umat k = 1 := Matrix.mem_unitaryGroup_iff'.1 hku
    calc umat k⁻¹ = umat k⁻¹ * (umat k * star (umat k)) := by
            rw [Matrix.mem_unitaryGroup_iff.1 hku, mul_one]
      _ = star (umat k) := by rw [← mul_assoc, h1, one_mul]
  have hJk : Jm ε * star (umat k) = star (umat k) * Jm ε := by
    have := congrArg star hkJ
    simp only [star_mul, Matrix.star_eq_conjTranspose, Jm_conjTranspose] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have hJ : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  set K := umat k
  rw [hinvk]
  refine ⟨?_, ?_, ?_⟩
  · unfold inG at hX ⊢
    simp only [Matrix.star_eq_conjTranspose] at hJk ⊢
    calc (Kᴴ * X * K)ᴴ * Jm ε + Jm ε * (Kᴴ * X * K)
        = Kᴴ * (Xᴴ * Jm ε + Jm ε * X) * K := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
            Matrix.add_mul, Matrix.mul_assoc]
          rw [hkJ, ← Matrix.mul_assoc (Jm ε) Kᴴ, hJk, Matrix.mul_assoc]
      _ = 0 := by rw [hX]; simp
  · simp only [Matrix.star_eq_conjTranspose]
    have hu : K * Kᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 hku
    have : Kᴴ * X * K * (Kᴴ * X * K)ᴴ = Kᴴ * (X * Xᴴ) * K := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc K Kᴴ, hu, Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · intro s
    have hu : K * star K = 1 := Matrix.mem_unitaryGroup_iff.1 hku
    have hu' : star K * K = 1 := Matrix.mem_unitaryGroup_iff'.1 hku
    let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨star K, K, hu', hu⟩
    have key := Matrix.exp_units_conj U ((s : ℂ) • X)
    have e1 : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = K := rfl
    rw [e1] at key
    change NormedSpace.exp (star K * ((s : ℂ) • X) * K) = star K * NormedSpace.exp ((s : ℂ) • X) * K at key
    rw [← key, Matrix.mul_smul, Matrix.smul_mul]

lemma norm_shift (hn : 1 ≤ n) {W : Submodule ℂ (Fin n → ℂ)} {ν : Measure (UJ ε)} (hW : IsIsoC ε W)
    (hν : IsHaarSub (NW ε W) ν) {β : UJ ε → ENNReal} (hβ : Measurable β) (hβt : ∀ y, β y ≠ ⊤)
    (hβ1 : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) {x : UJ ε} {r : ℝ}
    (h1 : ν.map (fun m => x * m * x⁻¹) = ENNReal.ofReal (Real.exp r) • ν)
    (h2 : ν.map (fun m => x⁻¹ * m * x⁻¹⁻¹) = ENNReal.ofReal (Real.exp (-r)) • ν)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d c : ℝ} (hσ : IsURepOn (UJset ε) σ)
    (hd : IsFdeg (muG ε) σ d) (hc : 8 * n * rkR ε < c) {v u : H}
    (hu : ∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))))
    (hv : ∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) :
    Integrable (fun g : UJ ε => (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (x * g))) u⟫_ℂ ∂ν‖ ^ 2) (muG ε) ∧
      ∫ g : UJ ε, (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (x * g))) u⟫_ℂ ∂ν‖ ^ 2 ∂(muG ε) =
        Real.exp (-r) * ((∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * (‖u‖ ^ 2 / d)) := by
  have hρ : IsURep (fun g : UJ ε => σ (umat g)) := isURep_umat hσ
  have im : ∀ (a g' : UJ ε) (p q : H), ⟪σ (umat a⁻¹) p, σ (umat g') q⟫_ℂ = ⟪p, σ (umat (a * g')) q⟫_ℂ :=
    fun a g' p q => inner_move hρ a g' p q
  have hmul : ∀ a b : UJ ε, σ (umat (a * b)) = (σ (umat a)).comp (σ (umat b)) := fun a b => hρ.2.1 a b
  have cd := GlobalTheory.Count.Cartan.cartan_distances n ε
  have hinv : ∀ g : UJ ε, dOp (umat g⁻¹) = dOp (umat g) := fun g => (cd.2.1 g g hn).2.1
  have hsub : ∀ g g' : UJ ε, dOp (umat (g * g')) ≤ dOp (umat g) + dOp (umat g') :=
    fun g g' => (cd.2.1 g g' hn).2.2.1
  have hc0 : 0 ≤ c := le_trans (by positivity) hc.le
  set v₁ := σ (umat x⁻¹) v with hv₁
  have hA : ∀ g, ∫ m, ⟪v, σ (umat (m * (x * g))) u⟫_ℂ ∂ν =
      (Real.exp (-r) : ℂ) * ∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν := by
    intro g
    have key := integral_conj (Real.exp_pos r).le h1 (fun m => ⟪v, σ (umat (m * (x * g))) u⟫_ℂ)
    have e : ∀ m, ⟪v, σ (umat (x * m * x⁻¹ * (x * g))) u⟫_ℂ = ⟪v₁, σ (umat (m * g)) u⟫_ℂ := by
      intro m
      have : x * m * x⁻¹ * (x * g) = x * (m * g) := by group
      rw [this, hv₁, im]
    simp only [e] at key
    rw [key, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      Complex.ofReal_one, one_mul]
  obtain ⟨Cu, hCu⟩ := hu
  obtain ⟨Cv, hCv⟩ := hv
  have hd1 : ∃ C : ℝ, ∀ g : UJ ε, ‖⟪v₁, σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))) := by
    refine ⟨Cu * Real.exp (c * (dOp (umat x) + dOp (umat (1 : UJ ε)))), fun g => ?_⟩
    have := decay_shift (δ := fun g : UJ ε => dOp (umat g)) hinv hsub hc0
      (f := fun g : UJ ε => ⟪v, σ (umat g) u⟫_ℂ) hCu x 1 g
    rw [hv₁, im]
    simpa only [mul_one] using this
  have hd2 : ∃ C : ℝ, ∀ g : UJ ε, ‖⟪v₁, σ (umat g) v₁⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))) := by
    refine ⟨Cv * Real.exp (c * (dOp (umat x) + dOp (umat x⁻¹))), fun g => ?_⟩
    have := decay_shift (δ := fun g : UJ ε => dOp (umat g)) hinv hsub hc0
      (f := fun g : UJ ε => ⟪v, σ (umat g) v⟫_ℂ) hCv x x⁻¹ g
    have e : ⟪v₁, σ (umat g) v₁⟫_ℂ = ⟪v, σ (umat (x * g * x⁻¹)) v⟫_ℂ := by
      rw [hv₁, im, hmul (x * g) x⁻¹]; rfl
    rw [e]; exact this
  obtain ⟨-, hI2, hI3⟩ := GlobalTheory.T.unitary_rep_matrix_coefficient_bound n ε W ν hW hν β hβ hβt hβ1 H σ d c u v₁ v₁ hσ hd hc hd1 hd1 hd2
  have hpt : ∀ g, ((β g).toReal : ℂ) * ((∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν) *
      star (∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν)) =
      (((β g).toReal * ‖∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  simp_rw [hpt] at hI2 hI3
  have hR : Integrable (fun g => (β g).toReal * ‖∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν‖ ^ 2) (muG ε) := by
    exact hI2.re.congr (Filter.Eventually.of_forall (fun g => by
      simp only [RCLike.re_to_complex, Complex.ofReal_re]))
  rw [integral_complex_ofReal] at hI3
  have hR3 : ∫ g, (β g).toReal * ‖∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν‖ ^ 2 ∂(muG ε) =
      ((∫ m, ⟪v₁, σ (umat m) v₁⟫_ℂ ∂ν) * ((‖u‖ ^ 2 / d : ℝ) : ℂ)).re := by
    rw [← hI3, Complex.ofReal_re]
  have hvv : ∫ m, ⟪v₁, σ (umat m) v₁⟫_ℂ ∂ν = (Real.exp r : ℂ) * ∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν := by
    have key := integral_conj (Real.exp_pos r).le h1 (fun m => ⟪v, σ (umat m) v⟫_ℂ)
    rw [← key]
    congr 1; funext m
    rw [hv₁, im, hmul (x * m) x⁻¹]; rfl
  have hfun : (fun g => (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (x * g))) u⟫_ℂ ∂ν‖ ^ 2) =
      fun g => Real.exp (-r) ^ 2 * ((β g).toReal * ‖∫ m, ⟪v₁, σ (umat (m * g)) u⟫_ℂ ∂ν‖ ^ 2) := by
    funext g
    rw [hA g, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; ring
  rw [hfun]
  refine ⟨hR.const_mul _, ?_⟩
  rw [integral_const_mul, hR3, hvv]
  have he : Real.exp (-r) * Real.exp r = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero]
  calc _ = Real.exp (-r) * (Real.exp (-r) * Real.exp r) *
        ((∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * (‖u‖ ^ 2 / d)) := by ring
    _ = _ := by rw [he, mul_one]

theorem torus_lipschitz : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ β : UJ ε → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → ∀ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm → (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) → (∀ g : UJ ε, ∃ k : UJ ε, umat k ∈ Kset ε ∧ ∀ s, a s * g * (k⁻¹ * a s * k)⁻¹ * g⁻¹ ∈ NW ε W) → ∀ κ : ℝ, (∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (w : H) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 8 * n * rkR ε < c → (∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0) → ∃ C₀ : ℝ, ∀ v : H, (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∀ X, inG ε X → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))))) → ∀ s : ℝ, |s| ≤ 1 → ∫ g : UJ ε, (β g).toReal * ‖(∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν)‖ ^ 2 ∂(muG ε) ≤ C₀ * s ^ 2 * (∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re := by
  intro n ε W ν hW hν β hβ hβt hβ1 a Hm hHm ha hconj κ hκ H _ _ _ σ d c w L hσ hd hc hL
  obtain ⟨E, hE1, -, hE3⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  refine ⟨((Hm * Hmᴴ).trace).re * Real.exp |κ| * ∑ i, ‖L (E i)‖ ^ 2 / d, ?_⟩
  intro v hvw hvv hvL s hs
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have e : ∀ g : UJ ε, (∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) -
        (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν) = 0 := by
      intro g; rw [sub_eq_zero]; congr 1
    have hz : ∑ i : Fin (0 ^ 2), ‖L (E i)‖ ^ 2 / d = 0 :=
      Finset.sum_eq_zero (fun i _ => absurd i.2 (by simp))
    rw [hz]
    simp [e]
  have hn : 1 ≤ n := hnpos
  have hρ : IsURep (fun g : UJ ε => σ (umat g)) := isURep_umat hσ
  have cd := GlobalTheory.Count.Cartan.cartan_distances n ε
  have hinv : ∀ g : UJ ε, dOp (umat g⁻¹) = dOp (umat g) := fun g => (cd.2.1 g g hn).2.1
  have hsub : ∀ g g' : UJ ε, dOp (umat (g * g')) ≤ dOp (umat g) + dOp (umat g') :=
    fun g g' => (cd.2.1 g g' hn).2.2.1
  have hδc : Continuous fun g : UJ ε => dOp (umat g) := cd.2.2.2.2
  have hnr : (0:ℝ) ≤ (n:ℝ) * (rkR ε : ℝ) := mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _)
  have hc0 : 0 ≤ c := by nlinarith
  have hνint : Integrable (fun m : UJ ε => Real.exp (-(c * dOp (umat m)))) ν :=
    (GlobalTheory.T.unipotentRadical_volume_growth n ε W ν hW hν).2 c (by nlinarith)
  haveI : SigmaFinite ν := by
    obtain ⟨C, hC⟩ := (GlobalTheory.T.unipotentRadical_volume_growth n ε W ν hW hν).1
    exact ({ set := fun k : ℕ => {m : UJ ε | dOp (umat m) ≤ k}
             set_mem := fun _ => Set.mem_univ _
             finite := fun k => (hC k (Nat.cast_nonneg k)).trans_lt ENNReal.ofReal_lt_top
             spanning := Set.eq_univ_of_forall fun m =>
               Set.mem_iUnion.2 ⟨⌈dOp (umat m)⌉₊, show dOp (umat m) ≤ (⌈dOp (umat m)⌉₊ : ℝ) from Nat.le_ceil _⟩ } :
             ν.FiniteSpanningSetsIn Set.univ).sigmaFinite
  have hNW := GlobalTheory.T.haar_subgroup_bi_invariant n ε W ν hW hν
  obtain ⟨haC, -, -, hainv⟩ := onePar ha
  have hnorm : ∀ X, inG ε X → ((X * Xᴴ).trace).re = ∑ i, (((X * (E i)ᴴ).trace).re) ^ 2 := by
    intro X hX
    have hXe := hE3 X hX
    have h1 : X * Xᴴ = ∑ i, ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • (E i * Xᴴ) := by
      calc X * Xᴴ = (∑ i, ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • E i) * Xᴴ := by rw [← hXe]
        _ = _ := by rw [Finset.sum_mul]; simp_rw [Matrix.smul_mul]
    have h2 : ∀ i, ((E i * Xᴴ).trace).re = ((X * (E i)ᴴ).trace).re := by
      intro i
      have : E i * Xᴴ = (X * (E i)ᴴ)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [this, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
    rw [h1, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, h2, sq]
  have hM : 0 ≤ ((Hm * Hmᴴ).trace).re := by
    rw [hnorm Hm hHm.1]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hΦ : ∀ i, Continuous fun p : ℝ × UJ ε =>
      ∫ m, ⟪v, σ (umat (m * (a p.1 * p.2))) (L (E i))⟫_ℂ ∂ν := by
    intro i
    have hu := hvL (E i) (hE1 i).1
    have hc' := (GlobalTheory.T.unitary_rep_matrix_coefficient_bound n ε W ν hW hν β hβ hβt hβ1 H σ d c (L (E i)) v v hσ hd hc hu hu hvv).1
    exact hc'.comp ((haC.comp continuous_fst).mul continuous_snd)
  have hB : ∀ i (t : ℝ), |t| ≤ 1 →
      Integrable (fun g => (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν‖ ^ 2) (muG ε) ∧
      ∫ g, (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν‖ ^ 2 ∂(muG ε) ≤
        Real.exp |κ| * ((∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * (‖L (E i)‖ ^ 2 / d)) := by
    intro i t ht
    have h2 : ν.map (fun m => (a t)⁻¹ * m * (a t)⁻¹⁻¹) = ENNReal.ofReal (Real.exp (-(κ * t))) • ν := by
      have := hκ (-t); rw [← hainv t, mul_neg] at this; exact this
    obtain ⟨hI, hE⟩ := norm_shift hn hW hν hβ hβt hβ1 (hκ t) h2 hσ hd hc (hvL (E i) (hE1 i).1) hvv
    refine ⟨hI, ?_⟩
    have h0 : 0 ≤ ∫ g, (β g).toReal * ‖∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν‖ ^ 2 ∂(muG ε) :=
      integral_nonneg (fun g => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    rw [hE] at h0 ⊢
    have hexp : Real.exp (-(κ * t)) ≤ Real.exp |κ| := by
      apply Real.exp_le_exp.mpr
      have : |κ * t| ≤ |κ| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg κ) ht
      linarith [neg_le_abs (κ * t)]
    exact mul_le_mul_of_nonneg_right hexp ((mul_nonneg_iff_of_pos_left (Real.exp_pos _)).1 h0)
  have hD : ∀ g : UJ ε, ∃ y : Fin (n ^ 2) → ℝ, ∑ i, y i ^ 2 ≤ ((Hm * Hmᴴ).trace).re ∧
      (∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν) =
        ∫ t in (0:ℝ)..s, ∑ i, (y i : ℂ) * ∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν := by
    intro g
    obtain ⟨k, hk, hkn⟩ := hconj g
    obtain ⟨hXg, htr, hexpg⟩ := conj_facts hk hHm.1
    set Xg := umat k⁻¹ * Hm * umat k with hXgdef
    refine ⟨fun i => ((Xg * (E i)ᴴ).trace).re, ?_, ?_⟩
    · show ∑ i, (((Xg * (E i)ᴴ).trace).re) ^ 2 ≤ ((Hm * Hmᴴ).trace).re
      rw [← hnorm Xg hXg, htr]
    obtain ⟨b, hbdef⟩ : ∃ b : ℝ → UJ ε, b = fun t => k⁻¹ * a t * k := ⟨_, rfl⟩
    have hbX : ∀ t : ℝ, umat (b t) = NormedSpace.exp ((t : ℂ) • Xg) := by
      intro t
      rw [hexpg t, hbdef]
      show umat k⁻¹ * umat (a t) * umat k = _
      rw [ha t]
    obtain ⟨hbc, hb0, hbh, -⟩ := onePar hbX
    have hder : HasDerivAt (fun t : ℝ => σ (umat (b t)) w) (L Xg) 0 := by
      have e : (fun t : ℝ => σ (umat (b t)) w) = fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Xg)) w := by
        funext t; rw [hbX]
      rw [e]; exact hL Xg hXg
    have hF : (∫ m, ⟪v, σ (umat (m * (g * b s))) w⟫_ℂ ∂ν) - ∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν =
        ∫ t in (0:ℝ)..s, ∫ m, ⟪v, σ (umat (m * (g * b t))) (L Xg)⟫_ℂ ∂ν :=
      ftc (ρ := fun g : UJ ε => σ (umat g)) (δ := fun g : UJ ε => dOp (umat g)) hρ hδc hinv hsub hc0
        hνint hbc hb0 hbh hder hvw (hvL Xg hXg) g s
    have hinvar : ∀ (t : ℝ) (u : H), ∫ m, ⟪v, σ (umat (m * (g * b t))) u⟫_ℂ ∂ν =
        ∫ m, ⟪v, σ (umat (m * (a t * g))) u⟫_ℂ ∂ν := by
      intro t u
      have hn' : a t * g * (b t)⁻¹ * g⁻¹ ∈ NW ε W := by rw [hbdef]; exact hkn t
      have key := integral_right (hNW.1 _ hn') (fun m => ⟪v, σ (umat (m * (g * b t))) u⟫_ℂ)
      rw [← key]
      congr 1; funext m
      have e : m * (a t * g * (b t)⁻¹ * g⁻¹) * (g * b t) = m * (a t * g) := by group
      simp only [e]
    have hint_i : ∀ (t : ℝ) i, Integrable (fun m => ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ) ν :=
      fun t i => integrable_coef (ρ := fun g : UJ ε => σ (umat g)) (δ := fun g : UJ ε => dOp (umat g))
        hρ hinv hsub hc0 hνint (hvL (E i) (hE1 i).1) (a t * g)
    have hLX : L Xg = ∑ i, (((Xg * (E i)ᴴ).trace).re) • L (E i) := by
      conv_lhs => rw [hE3 Xg hXg]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← map_smul]; congr 1
    have hDform : ∀ t : ℝ, ∫ m, ⟪v, σ (umat (m * (a t * g))) (L Xg)⟫_ℂ ∂ν =
        ∑ i, ((((Xg * (E i)ᴴ).trace).re : ℝ) : ℂ) *
          ∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν := by
      intro t
      rw [hLX]
      have hpt : ∀ m : UJ ε, ⟪v, σ (umat (m * (a t * g))) (∑ i, (((Xg * (E i)ᴴ).trace).re) • L (E i))⟫_ℂ =
          ∑ i, ((((Xg * (E i)ᴴ).trace).re : ℝ) : ℂ) * ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ := by
        intro m
        rw [map_sum, inner_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [ContinuousLinearMap.map_smul_of_tower, ← Complex.coe_smul, inner_smul_right]
      simp only [hpt]
      rw [integral_finset_sum _ (fun i _ => (hint_i t i).const_mul _)]
      simp_rw [integral_const_mul]
    show (∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν) =
      ∫ t in (0:ℝ)..s, ∑ i, ((((Xg * (E i)ᴴ).trace).re : ℝ) : ℂ) *
        ∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν
    rw [← hinvar s w, hF]
    congr 1; funext t
    rw [hinvar t, hDform t]
  have key := torus_lipschitz_l2_bound (muG ε) (fun g => (β g).toReal) hβ.ennreal_toReal (fun g => ENNReal.toReal_nonneg)
    (fun i t g => ∫ m, ⟪v, σ (umat (m * (a t * g))) (L (E i))⟫_ℂ ∂ν) hΦ
    (fun g => (∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - ∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν)
    ((Hm * Hmᴴ).trace).re s hM hs
    (fun i => Real.exp |κ| * ((∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * (‖L (E i)‖ ^ 2 / d))) hD hB
  refine key.trans (le_of_eq ?_)
  have hs' : ∑ i, Real.exp |κ| * ((∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * (‖L (E i)‖ ^ 2 / d)) =
      Real.exp |κ| * (∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re * ∑ i, ‖L (E i)‖ ^ 2 / d := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hs']; ring

end GlobalTheory.TorusLip
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_parameter_conjugation_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ β : UJ ε → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → ∀ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm → (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) → (∀ g : UJ ε, ∃ k : UJ ε, umat k ∈ Kset ε ∧ ∀ s, a s * g * (k⁻¹ * a s * k)⁻¹ * g⁻¹ ∈ NW ε W) → ∀ κ : ℝ, (∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (w : H) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 8 * n * rkR ε < c → (∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0) → ∃ C₀ : ℝ, ∀ v : H, (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∀ X, inG ε X → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))))) → ∀ s : ℝ, |s| ≤ 1 → ∫ g : UJ ε, (β g).toReal * ‖(∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν)‖ ^ 2 ∂(muG ε) ≤ C₀ * s ^ 2 * (∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re := by
  atlas_forward_decl GlobalTheory.TorusLip.torus_lipschitz
end
