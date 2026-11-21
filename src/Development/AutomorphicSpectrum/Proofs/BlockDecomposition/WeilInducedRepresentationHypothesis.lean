import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RWConstMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NsgDivNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompUnitMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitRepresentationHypothesis
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHaarMeasureComapSubtype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussConstantHypothesis

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2LocalData.WRepNProof

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [Field E] [TopologicalSpace E] [MeasurableSpace E] [Algebra F E]

theorem nsg_one : nsg E (1 : F) = 1 := by
  unfold nsg
  exact if_pos ⟨1, by simp⟩

theorem rW_n (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (b : F) (Φ : E → ℂ) :
    rWm χ σ μ lam !![1, b; 0, 1] Φ = fun z => (χ (b * Algebra.norm F z) : ℂ) * Φ z := by
  funext z
  simp [rWm, rW, nsg_one]

theorem rW_mul_n (hfin : Module.finrank F E = 2) (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ)
    (g : Matrix (Fin 2) (Fin 2) F) (b : F) (Φ : E → ℂ) :
    rWm χ σ μ lam (g * !![1, b; 0, 1]) Φ = rWm χ σ μ lam g (rWm χ σ μ lam !![1, b; 0, 1] Φ) := by
  rw [rW_n]
  funext z
  have e00 : (g * !![1, b; 0, 1]) 0 0 = g 0 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * !![1, b; 0, 1]) 0 1 = g 0 0 * b + g 0 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * !![1, b; 0, 1]) 1 0 = g 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * !![1, b; 0, 1]) 1 1 = g 1 0 * b + g 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [rWm, rW, e00, e01, e10, e11]
  by_cases hc : g 1 0 = 0
  · rw [if_pos (e10.trans hc), if_pos hc]
    have hN : Algebra.norm F (algebraMap F E (g 0 0) * z) = g 0 0 ^ 2 * Algebra.norm F z := by
      rw [map_mul, Algebra.norm_algebraMap, hfin]
    have hadd : g 0 0 * (g 0 0 * b + g 0 1) * Algebra.norm F z =
        g 0 0 * g 0 1 * Algebra.norm F z + b * (g 0 0 ^ 2 * Algebra.norm F z) := by ring
    rw [hN, hadd, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  · rw [if_neg (fun h => hc (e10.symm.trans h)), if_neg hc]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hadd : (g 0 0 * Algebra.norm F z + (g 1 0 * b + g 1 1) * Algebra.norm F u -
          Algebra.trace F E (σ z * u)) / g 1 0 =
        (g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u - Algebra.trace F E (σ z * u)) / g 1 0 +
          b * Algebra.norm F u := by
      field_simp
      ring
    beta_reduce
    rw [hadd, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring

end GlobalTheory.CompanionTheory.GL2LocalData.WRepNProof

theorem GlobalTheory.CompanionTheory.GL2LocalData.wRepN : Ad3.K.GL2LocalData.WRepN := by
  intro F _ _ _ _ _ _ _ χ _ _ E _ _ _ _ _ _ _ hfin _ σ _ η _ g _ b Φ _
  exact GlobalTheory.CompanionTheory.GL2LocalData.WRepNProof.rW_mul_n hfin χ σ _ _ g b Φ
end
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSquare

open GlobalTheory.CompanionTheory.WeilSB

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]
  [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem square_identity (a : Fˣ) (u z : E) :
    (a : F) * Algebra.norm F u + Algebra.trace F E (conj F E u * z) =
      (a : F) * Algebra.norm F (u + algebraMap F E ((a : F)⁻¹) * z) + -(Algebra.norm F z) / a := by
  have ha : (a : F) ≠ 0 := a.ne_zero
  have h1 : Algebra.trace F E (conj F E u * z) = Algebra.trace F E (u * conj F E z) := by
    rw [← trace_conj (K := F) (conj F E u * z), map_mul, conj_conj]
  have h2 : u * conj F E (algebraMap F E ((a : F)⁻¹) * z) =
      algebraMap F E ((a : F)⁻¹) * (u * conj F E z) := by
    rw [map_mul, conj_algebraMap]
    ring
  rw [norm_add (K := F) u, h2, trace_algebraMap_mul, h1, map_mul (Algebra.norm F), norm_algebraMap_eq_sq]
  field_simp
  ring

theorem setIntegral_ball_add (μ : Measure E) [μ.IsAddHaarMeasure] (G : E → ℂ) {n : ℤ} {w : E}
    (hw : w ∈ valBall E n) :
    ∫ u in (valBall E n : Set E), G (u + w) ∂μ = ∫ u in (valBall E n : Set E), G u ∂μ := by
  have e : (valBall E n : Set E).indicator (fun u => G (u + w)) =
      fun u => (valBall E n : Set E).indicator G (u + w) := by
    funext u
    by_cases hu : u ∈ valBall E n
    · have hu' : u + w ∈ valBall E n := add_mem hu hw
      rw [Set.indicator_of_mem (show u ∈ (valBall E n : Set E) from hu),
        Set.indicator_of_mem (show u + w ∈ (valBall E n : Set E) from hu')]
    · have hu' : u + w ∉ valBall E n := fun h => hu (by simpa using sub_mem h hw)
      rw [Set.indicator_of_notMem (show u ∉ (valBall E n : Set E) from hu),
        Set.indicator_of_notMem (show u + w ∉ (valBall E n : Set E) from hu')]
  rw [← integral_indicator (measurableSet_valBall n), ← integral_indicator (measurableSet_valBall n), e]
  exact integral_add_right_eq_self _ w

theorem core_of_haar {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) (μ : Measure E) [μ.IsAddHaarMeasure] (a : Fˣ)
    {Φ : E → ℂ} (hΦ : Φ ∈ SBE E) :
    ∃ n₀ : ℤ, ∀ n ≤ n₀,
      ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTs χ (conj F E) μ Φ u ∂μ =
        (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂μ) *
          ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂μ := by
  have hN := continuous_norm_of (F := F) (E := E) hcont
  have hψ : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hψ1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  have hΦs : Φ ∈ schwartzBruhat E := ⟨hΦ.1, hΦ.2⟩
  have hFT : ∀ u, FTs χ (conj F E) μ Φ u = localFourier μ (chE E χ) Φ (conj F E u) := by
    intro u
    unfold FTs localFourier
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show Φ z * (χ (Algebra.trace F E (conj F E u * z)) : ℂ) =
      Φ z * (χ (Algebra.trace F E (z * conj F E u)) : ℂ)
    rw [mul_comm (conj F E u) z]
  obtain ⟨-, M₁, -, hM₁⟩ := exists_invariant_of_mem_schwartzBruhat
    (localFourier_mem_schwartzBruhat μ hψ hψ1 hΦs)
  obtain ⟨-, M₂, -, hM₂⟩ := exists_invariant_of_mem_schwartzBruhat hΦs
  have ha0 : algebraMap F E ((a : F)⁻¹) ≠ 0 := (map_ne_zero _).2 (inv_ne_zero a.ne_zero)
  have hai : algebraMap F E ((a : F)⁻¹) ∈ valBall E (ord (algebraMap F E ((a : F)⁻¹))) :=
    (mem_valBall_iff_le_ord ha0).2 le_rfl
  refine ⟨min M₁ (ord (algebraMap F E ((a : F)⁻¹)) + M₂), fun n hn => ?_⟩
  have hn₁ : n ≤ M₁ := hn.trans (min_le_left _ _)
  have hn₂ : n ≤ ord (algebraMap F E ((a : F)⁻¹)) + M₂ := hn.trans (min_le_right _ _)
  have hfin : IsFiniteMeasure (μ.restrict (valBall E n : Set E)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_valBall n).measure_lt_top⟩
  set G : E → ℂ := fun u => (χ ((a : F) * Algebra.norm F u) : ℂ) with hG
  set K : E → E → ℂ := fun u z => G u * (Φ z * (χ (Algebra.trace F E (conj F E u * z)) : ℂ)) with hK
  have hint : Integrable (Function.uncurry K) ((μ.restrict (valBall E n : Set E)).prod μ) := by
    have hΦi : Integrable Φ μ := integrable_of_mem_schwartzBruhat μ hΦs
    have hp := (integrable_const (μ := μ.restrict (valBall E n : Set E)) (1 : ℂ)).mul_prod hΦi
    have hc : Continuous fun p : E × E => (χ ((a : F) * Algebra.norm F p.1) : ℂ) *
        (chE E χ (conj F E p.1 * p.2) : ℂ) :=
      ((continuous_subtype_val.comp hχ).comp (continuous_const.mul (hN.comp continuous_fst))).mul
        ((continuous_subtype_val.comp hψ).comp
          ((continuous_conj.comp continuous_fst).mul continuous_snd))
    have hb := hp.bdd_mul (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      rw [norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul])
    refine hb.congr (Filter.Eventually.of_forall fun p => ?_)
    show _ = G p.1 * (Φ p.2 * (χ (Algebra.trace F E (conj F E p.1 * p.2)) : ℂ))
    show (χ ((a : F) * Algebra.norm F p.1) : ℂ) * (χ (Algebra.trace F E (conj F E p.1 * p.2)) : ℂ) *
      (1 * Φ p.2) = _
    simp only [hG]
    ring
  have hinner : ∀ z, ∫ u in (valBall E n : Set E), K u z ∂μ =
      (∫ u in (valBall E n : Set E), G u ∂μ) * ((χ (-(Algebra.norm F z) / a) : ℂ) * Φ z) := by
    intro z
    by_cases hz : Φ z = 0
    · simp [hK, hz]
    have hw : algebraMap F E ((a : F)⁻¹) * z ∈ valBall E n :=
      valBall_antitone hn₂ (mul_mem_valBall hai (hM₂ z hz))
    have e : ∀ u, K u z = ((χ (-(Algebra.norm F z) / a) : ℂ) * Φ z) *
        G (u + algebraMap F E ((a : F)⁻¹) * z) := by
      intro u
      have h := congrArg (fun t => (χ t : ℂ)) (square_identity a u z)
      simp only [AddChar.map_add_eq_mul, Circle.coe_mul] at h
      simp only [hK, hG]
      linear_combination Φ z * h
    simp only [e]
    rw [integral_const_mul, setIntegral_ball_add μ G hw]
    ring
  calc ∫ u, G u * FTs χ (conj F E) μ Φ u ∂μ
      = ∫ u in (valBall E n : Set E), G u * FTs χ (conj F E) μ Φ u ∂μ := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
        have : localFourier μ (chE E χ) Φ (conj F E u) = 0 := by
          by_contra h
          exact hu (conj_mem_valBall_iff.1 (valBall_antitone hn₁ (hM₁ _ h)))
        rw [hFT, this, mul_zero]
    _ = ∫ u in (valBall E n : Set E), ∫ z, K u z ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show G u * FTs χ (conj F E) μ Φ u = ∫ z, K u z ∂μ
        simp only [hK]
        rw [integral_const_mul]
        rfl
    _ = ∫ z, ∫ u in (valBall E n : Set E), K u z ∂μ ∂μ := integral_integral_swap hint
    _ = _ := by
        simp only [hinner]
        rw [integral_const_mul]

end Main

theorem gauss_core : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∃ n₀ : ℤ, ∀ n ≤ n₀,
  ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
    (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ) *
      ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη a Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hσc : σ = conj F E := (eq_one_or_eq_conj σ).resolve_left hσ
  subst hσc
  exact core_of_haar hχ hχ1 hcont (muE E χ) a hΦ

end GlobalTheory.CompanionTheory.WeilSquare
end
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
theorem _root_.GlobalTheory.T.norm_form_integral_fourier_factorization : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∃ n₀ : ℤ, ∀ n ≤ n₀,
  ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
    (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ) *
      ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSquare.gauss_core | exact GlobalTheory.CompanionTheory.WeilSquare.gauss_core | (intros; apply GlobalTheory.CompanionTheory.WeilSquare.gauss_core <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilSquare.gauss_core | exact GlobalTheory.CompanionTheory.WeilSquare.gauss_core | (intros; apply GlobalTheory.CompanionTheory.WeilSquare.gauss_core <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilSquare.core_of_haar | exact GlobalTheory.CompanionTheory.WeilSquare.core_of_haar | (intros; apply GlobalTheory.CompanionTheory.WeilSquare.core_of_haar <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilSquare.setIntegral_ball_add | exact GlobalTheory.CompanionTheory.WeilSquare.setIntegral_ball_add | (intros; apply GlobalTheory.CompanionTheory.WeilSquare.setIntegral_ball_add <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilSquare.square_identity | exact GlobalTheory.CompanionTheory.WeilSquare.square_identity | (intros; apply GlobalTheory.CompanionTheory.WeilSquare.square_identity <;> assumption)
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSB

theorem ballIntegral_stable :
    (ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∃ n₀ : ℤ, ∀ n ≤ n₀,
      ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
        (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ) *
          ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) →
    ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∃ (c : ℂ) (n₀ : ℤ), ∀ n ≤ n₀,
      ∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ = c := by
  intro H F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη a
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hN := continuous_norm_of (F := F) (E := E) hcont
  have hlc := isLocallyConstant_char hχ hχ1
  have hf : IsLocallyConstant (fun z : E => (χ (-(Algebra.norm F z) / a) : ℂ)) :=
    hlc.comp_continuous (hN.neg.div_const _)
  have h0 : (χ (-(Algebra.norm F (0 : E)) / a) : ℂ) = 1 := by
    simp [Algebra.norm_zero]
  have hU : {z : E | (χ (-(Algebra.norm F z) / a) : ℂ) = 1} ∈ nhds (0 : E) :=
    (hf.isOpen_fiber 1).mem_nhds h0
  obtain ⟨m, -, hm⟩ := hasBasis_nhds_zero_valBall.mem_iff.1 hU
  have hclopen : IsClopen (valBall E m : Set E) := ⟨isClosed_valBall m, isOpen_valBall m⟩
  have hΦ₀ : (valBall E m : Set E).indicator (fun _ => (1 : ℂ)) ∈ SBE E :=
    ⟨by
        have h : IsLocallyConstant (⇑(LocallyConstant.charFn ℂ hclopen)) :=
          LocallyConstant.isLocallyConstant _
        rw [LocallyConstant.coe_charFn] at h
        exact h,
      HasCompactSupport.intro (isCompact_valBall m) fun x hx => Set.indicator_of_notMem hx _⟩
  obtain ⟨n₀, hn₀⟩ := H F χ hχ hχ1 E hfr hcont σ hσ η hη a _ hΦ₀
  have hJ : ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) *
      (valBall E m : Set E).indicator (fun _ => (1 : ℂ)) z ∂muE E χ =
      (((muE E χ).real (valBall E m : Set E) : ℝ) : ℂ) := by
    have e : (fun z => (χ (-(Algebra.norm F z) / a) : ℂ) *
        (valBall E m : Set E).indicator (fun _ => (1 : ℂ)) z) =
        (valBall E m : Set E).indicator (fun _ => (1 : ℂ)) := by
      funext z
      by_cases hz : z ∈ (valBall E m : Set E)
      · rw [Set.indicator_of_mem hz, mul_one]
        exact hm hz
      · rw [Set.indicator_of_notMem hz, mul_zero]
    rw [e, integral_indicator hclopen.isOpen.measurableSet]
    simp
  have hV : (muE E χ).real (valBall E m : Set E) ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(hclopen.isOpen.measure_pos _ ⟨0, zero_mem _⟩).ne',
      (isCompact_valBall m).measure_lt_top.ne⟩
  have hV' : (((muE E χ).real (valBall E m : Set E) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hV
  refine ⟨(∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) *
      FTE E χ σ ((valBall E m : Set E).indicator (fun _ => (1 : ℂ))) u ∂muE E χ) /
      (((muE E χ).real (valBall E m : Set E) : ℝ) : ℂ), n₀, fun n hn => ?_⟩
  rw [hn₀ n hn, hJ, mul_div_cancel_right₀ _ hV']

end GlobalTheory.CompanionTheory.WeilSB
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_form_ball_integral_stabilizes : (ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∃ n₀ : ℤ, ∀ n ≤ n₀,
  ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
    (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ) *
      ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) → ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∃ (c : ℂ) (n₀ : ℤ), ∀ n ≤ n₀,
  ∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ = c := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WeilSB.ballIntegral_stable
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilGaussScale

theorem mul_mem_valBall_add_ord_iff {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {t : K} (ht : t ≠ 0) (n : ℤ) (u : K) :
    t * u ∈ (valBall K (n + ord t) : Set K) ↔ u ∈ (valBall K n : Set K) := by
  rw [← smul_valBall ht n, ← smul_eq_mul]
  exact Set.smul_mem_smul_set_iff₀ ht _ _

theorem integral_valBall_dilation : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (t : Eˣ) (n : ℤ),
  ∫ u in (valBall E n : Set E), (χ (Algebra.norm F (t : E) * Algebra.norm F u) : ℂ) ∂muE E χ =
    (((modulus (Algebra.norm F (t : E)) : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ u in (valBall E (n + ord (t : E)) : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη t n
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  rw [modulus_norm (K := F) (t : E)]
  set f : E → ℂ := (valBall E (n + ord (t : E)) : Set E).indicator
    (fun u => (χ (Algebra.norm F u) : ℂ)) with hf
  have hsub := integral_comp_mul_left (muE E χ) t.ne_zero f
  have hpt : (fun u => f ((t : E) * u)) = (valBall E n : Set E).indicator
      (fun u => (χ (Algebra.norm F (t : E) * Algebra.norm F u) : ℂ)) := by
    funext u
    by_cases hu : u ∈ (valBall E n : Set E)
    · rw [Set.indicator_of_mem hu, hf, Set.indicator_of_mem
        ((mul_mem_valBall_add_ord_iff t.ne_zero n u).2 hu), map_mul]
    · rw [Set.indicator_of_notMem hu, hf, Set.indicator_of_notMem
        (fun h => hu ((mul_mem_valBall_add_ord_iff t.ne_zero n u).1 h))]
  rw [hpt, integral_indicator (measurableSet_valBall n), hf,
    integral_indicator (measurableSet_valBall _)] at hsub
  rw [hsub, Complex.real_smul]

end GlobalTheory.CompanionTheory.WeilGaussScale
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_form_ball_integral_scaling : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (t : Eˣ) (n : ℤ),
  ∫ u in (valBall E n : Set E), (χ (Algebra.norm F (t : E) * Algebra.norm F u) : ℂ) ∂muE E χ =
    (((modulus (Algebra.norm F (t : E)) : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ u in (valBall E (n + ord (t : E)) : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WeilGaussScale.integral_valBall_dilation
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.NormFib

theorem map_norm_add_translate_eq_smul : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : NNReal,
  (multHaar E).map (normUnits F E) + (multHaar E).map (fun x => a * normUnits F E x) = κ • multHaar F := by
  intro F E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc a ha
  have hO : IsOpen ((normUnits F E).range : Set Fˣ) :=
    GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.isOpen_range_normUnits (K := F) (E := E)
  obtain ⟨c, -, hmap⟩ := exists_map_eq_smul_restrict (normUnits F E)
    (isProperMap_normUnits F E) hO (multHaar E) (multHaar F)
  set H : Set Fˣ := ((normUnits F E).range : Set Fˣ) with hH
  have hHm : MeasurableSet H := hO.measurableSet
  have hmeasN : Measurable (normUnits F E) := (continuous_normUnits F E).measurable
  have hmul : Measurable (fun y : Fˣ => a * y) := measurable_const_mul a
  have hcompl : (fun y : Fˣ => a * y) ⁻¹' Hᶜ = H := by
    ext y
    have h := Subgroup.mul_mem_iff_of_index_two (index_range_normUnits_eq_two F E) (a := a) (b := y)
    simp only [Set.mem_preimage, Set.mem_compl_iff, hH, SetLike.mem_coe]
    tauto
  have hsecond : (multHaar E).map (fun x => a * normUnits F E x) =
      c • (multHaar F).restrict Hᶜ := by
    have e1 : (multHaar E).map (fun x => a * normUnits F E x) =
        ((multHaar E).map (normUnits F E)).map (fun y : Fˣ => a * y) :=
      (Measure.map_map hmul hmeasN).symm
    have e2 : (multHaar F).restrict Hᶜ = ((multHaar F).restrict H).map (fun y : Fˣ => a * y) := by
      conv_lhs => rw [← map_mul_left_eq_self (multHaar F) a]
      rw [(measurableEmbedding_mulLeft a).restrict_map, hcompl]
    rw [e1, hmap, e2, Measure.map_smul]
  refine ⟨c, ?_⟩
  rw [hsecond, hmap, ← smul_add, Measure.restrict_add_restrict_compl hHm]

end GlobalTheory.CompanionTheory.NormFib
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_norm_ball_integral_vanishes : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : NNReal,
  (multHaar E).map (normUnits F E) + (multHaar E).map (fun x => a * normUnits F E x) = κ • multHaar F := by
  atlas_forward_decl GlobalTheory.CompanionTheory.NormFib.map_norm_add_translate_eq_smul
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilPush

section One

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem setLIntegral_compl_zero_indicator {T : Set K} (hT : MeasurableSet T) :
    ∫⁻ x in {0}ᶜ, T.indicator 1 x ∂(haarIntegers K) = haarIntegers K T := by
  have h : (haarIntegers K).restrict ({0}ᶜ : Set K) = haarIntegers K :=
    Measure.restrict_eq_self_of_ae_mem
      ((measure_eq_zero_iff_ae_notMem.mp haarIntegers_singleton_zero).mono fun x hx => hx)
  rw [h, lintegral_indicator_one hT]

end One

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]
  [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

def gS (S : Set F) (y : F) : ENNReal := S.indicator 1 y * (modulus y : ENNReal)

theorem measurable_gS {S : Set F} (hS : MeasurableSet S) : Measurable (gS S) :=
  (measurable_one.indicator hS).mul measurable_modulus.coe_nnreal_ennreal

theorem lintegral_gS {S : Set F} (hS : MeasurableSet S) :
    ∫⁻ u : Fˣ, gS S (u : F) ∂(multHaar F) = multHaarConst F * haarIntegers F S := by
  rw [lintegral_multHaar (measurable_gS hS), ← setLIntegral_compl_zero_indicator hS]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
  have h0 : (modulus x : ENNReal) ≠ 0 := by exact_mod_cast (modulus_pos hx).ne'
  simp only [gS]
  rw [mul_comm (S.indicator 1 x), ← mul_assoc, ENNReal.inv_mul_cancel h0 ENNReal.coe_ne_top, one_mul]

theorem continuous_normUnits (h : Continuous (algebraMap F E)) : Continuous (normUnits F E) := by
  have hN := GlobalTheory.CompanionTheory.WeilSB.continuous_norm_of (F := F) (E := E) h
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have e : (Units.val ∘ (normUnits F E) : Eˣ → F) = fun x : Eˣ => Algebra.norm F (x : E) :=
      funext fun x => coe_normUnits x
    rw [e]
    exact hN.comp Units.continuous_val
  · have e : (fun x : Eˣ => (((normUnits F E x)⁻¹ : Fˣ) : F)) =
        fun x : Eˣ => Algebra.norm F ((x⁻¹ : Eˣ) : E) := funext fun x => by
      rw [← map_inv, coe_normUnits]
    show Continuous (fun x : Eˣ => (((normUnits F E x)⁻¹ : Fˣ) : F))
    rw [e]
    exact hN.comp (Units.continuous_val.comp continuous_inv)

theorem lintegral_gS_norm (h : Continuous (algebraMap F E)) (c : Fˣ) {S : Set F}
    (hS : MeasurableSet S) :
    ∫⁻ u : Eˣ, gS S ((c : F) * Algebra.norm F (u : E)) ∂(multHaar E) =
      multHaarConst E * ((modulus (c : F) : ENNReal) *
        haarIntegers E ((fun u : E => (c : F) * Algebra.norm F u) ⁻¹' S)) := by
  have hN := GlobalTheory.CompanionTheory.WeilSB.continuous_norm_of (F := F) (E := E) h
  have hm : Measurable (fun u : E => (c : F) * Algebra.norm F u) :=
    (continuous_const.mul hN).measurable
  have hT : MeasurableSet ((fun u : E => (c : F) * Algebra.norm F u) ⁻¹' S) := hm hS
  rw [lintegral_multHaar (g := fun x : E => gS S ((c : F) * Algebra.norm F x))
    ((measurable_gS hS).comp hm), ← setLIntegral_compl_zero_indicator hT,
    ← lintegral_const_mul _ (measurable_one.indicator hT)]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
  have h0 : (modulus x : ENNReal) ≠ 0 := by exact_mod_cast (modulus_pos hx).ne'
  have hmod : (modulus ((c : F) * Algebra.norm F x) : ENNReal) =
      (modulus (c : F) : ENNReal) * (modulus x : ENNReal) := by
    rw [modulus_mul, modulus_norm]; push_cast; rfl
  have hi : (((fun u : E => (c : F) * Algebra.norm F u) ⁻¹' S).indicator 1 x : ENNReal) =
      S.indicator 1 ((c : F) * Algebra.norm F x) := rfl
  simp only [gS]
  rw [hmod, hi]
  calc _ = ((modulus x : ENNReal))⁻¹ * (modulus x : ENNReal) *
        (S.indicator 1 ((c : F) * Algebra.norm F x) * (modulus (c : F) : ENNReal)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel h0 ENNReal.coe_ne_top, one_mul, mul_comm]

theorem haar_identity (h : Continuous (algebraMap F E)) (a : Fˣ) (κ₀ : NNReal)
    (H : (multHaar E).map (normUnits F E) + (multHaar E).map (fun x => a * normUnits F E x) =
      κ₀ • multHaar F) {S : Set F} (hS : MeasurableSet S) :
    multHaarConst E * (haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) +
      (modulus (a : F) : ENNReal) * haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S)) =
    (κ₀ : ENNReal) * multHaarConst F * haarIntegers F S := by
  have hc := continuous_normUnits (F := F) (E := E) h
  have hm1 : Measurable (normUnits F E) := hc.measurable
  have hm2 : Measurable (fun x : Eˣ => a * normUnits F E x) := (continuous_const.mul hc).measurable
  have hg : Measurable (fun u : Fˣ => gS S (u : F)) :=
    (measurable_gS hS).comp Units.continuous_val.measurable
  have key := congrArg (fun μ : Measure Fˣ => ∫⁻ u, gS S (u : F) ∂μ) H
  rw [lintegral_add_measure, lintegral_map hg hm1, lintegral_map hg hm2, lintegral_smul_measure,
    lintegral_gS hS] at key
  have e1 : ∫⁻ u : Eˣ, gS S ((normUnits F E u : Fˣ) : F) ∂(multHaar E) =
      multHaarConst E * haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) := by
    have := lintegral_gS_norm (F := F) (E := E) h 1 hS
    simpa [coe_normUnits, modulus_one] using this
  have e2 : ∫⁻ u : Eˣ, gS S (((a * normUnits F E u : Fˣ)) : F) ∂(multHaar E) =
      multHaarConst E * ((modulus (a : F) : ENNReal) *
        haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S)) := by
    have := lintegral_gS_norm (F := F) (E := E) h a hS
    simpa [coe_normUnits] using this
  rw [e1, e2] at key
  rw [mul_add, key, ENNReal.smul_def, smul_eq_mul, mul_assoc]

end Main

theorem push_of_multHaar
    (H : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
      [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : NNReal,
      (multHaar E).map (normUnits F E) + (multHaar E).map (fun x => a * normUnits F E x) = κ • multHaar F) :
    ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
      [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : ENNReal, κ ≠ ⊤ ∧ ∀ S : Set F, MeasurableSet S →
      haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) + (modulus (a : F) : ENNReal) * haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S) = κ * haarIntegers F S := by
  intro F E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcont a ha
  obtain ⟨κ₀, hκ⟩ := H F E hcont a ha
  have hE0 := multHaarConst_ne_zero (K := E)
  have hEt := multHaarConst_ne_top (K := E)
  refine ⟨(multHaarConst E)⁻¹ * ((κ₀ : ENNReal) * multHaarConst F), ?_, fun S hS => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hE0)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top multHaarConst_ne_top)
  · have key := haar_identity (F := F) (E := E) hcont a κ₀ hκ hS
    rw [mul_assoc, ← key, ← mul_assoc, ENNReal.inv_mul_cancel hE0 hEt, one_mul]

end GlobalTheory.CompanionTheory.WeilPush
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_norm_gauss_integral_sign : (∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : NNReal,
  (multHaar E).map (normUnits F E) + (multHaar E).map (fun x => a * normUnits F E x) = κ • multHaar F) → ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : ENNReal, κ ≠ ⊤ ∧ ∀ S : Set F, MeasurableSet S →
  haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) + (modulus (a : F) : ENNReal) * haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S) = κ * haarIntegers F S := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WeilPush.push_of_multHaar
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilGaussNon

section Char

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem integral_valBall_char_eq_zero (μ : Measure F) [μ.IsAddHaarMeasure] {χ : AddChar F Circle}
    {m : ℤ} {b : F} (hb : b ∈ valBall F m) (hχb : χ b ≠ 1) :
    ∫ x in (valBall F m : Set F), (χ x : ℂ) ∂μ = 0 := by
  have hDm : MeasurableSet (valBall F m : Set F) := (isOpen_valBall m).measurableSet
  rw [← integral_indicator hDm]
  set g : F → ℂ := (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) with hg
  have e1 : ∫ x, g (x + b) ∂μ = ∫ x, g x ∂μ := integral_add_right_eq_self g b
  have e2 : ∀ x, g (x + b) = (χ b : ℂ) * g x := by
    intro x
    by_cases hx : x ∈ (valBall F m : Set F)
    · have hxb : x + b ∈ (valBall F m : Set F) := (valBall F m).add_mem hx hb
      rw [hg, Set.indicator_of_mem hxb, Set.indicator_of_mem hx, AddChar.map_add_eq_mul]
      push_cast
      ring
    · have hxb : x + b ∉ (valBall F m : Set F) := fun h => hx (by
        have := sub_mem (show x + b ∈ valBall F m from h) hb
        simpa using this)
      rw [hg, Set.indicator_of_notMem hxb, Set.indicator_of_notMem hx, mul_zero]
  simp_rw [e2] at e1
  rw [integral_const_mul] at e1
  have h1 : ((χ b : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hχb (Circle.ext (by simpa using h))
  have h2 : ((χ b : ℂ) - 1) * ∫ x, g x ∂μ = 0 := by linear_combination e1
  exact (mul_eq_zero.1 h2).resolve_left h1

end Char

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]
  [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

variable (F E) in

def radius (c : F) (m : ℤ) : ℤ := -((ord c - m) / (residueDegree F E : ℤ))

theorem preimage_valBall {c : F} (hc : c ≠ 0) (m : ℤ) :
    (fun u : E => c * Algebra.norm F u) ⁻¹' (valBall F m : Set F) =
      (valBall E (radius F E c m) : Set E) := by
  ext u
  by_cases hu : u = 0
  · subst hu
    simp [zero_mem]
  · have hN : Algebra.norm F u ≠ 0 := (normUnits F E (Units.mk0 u hu)).ne_zero
    simp only [Set.mem_preimage, SetLike.mem_coe]
    rw [mem_valBall_iff_le_ord (mul_ne_zero hc hN), mem_valBall_iff_le_ord hu, ord_mul hc hN,
      ord_norm, radius]
    have hf : (0 : ℤ) < residueDegree F E := by exact_mod_cast residueDegree_pos F E
    rw [neg_le, Int.le_ediv_iff_mul_le hf]
    constructor <;> intro h <;> linarith

theorem radius_le {c : F} {m N₀ : ℤ} (h : m ≤ ord c + residueDegree F E * N₀) :
    radius F E c m ≤ N₀ := by
  have hf : (0 : ℤ) < residueDegree F E := by exact_mod_cast residueDegree_pos F E
  rw [radius, neg_le, Int.le_ediv_iff_mul_le hf]
  linarith

theorem map_facts {χ : AddChar F Circle} (hχ : Continuous χ) {P : E → F} (hP : Continuous P)
    {m n : ℤ} (hpre : P ⁻¹' (valBall F m : Set F) = (valBall E n : Set E)) :
    Integrable ((valBall F m : Set F).indicator (fun x => (χ x : ℂ)))
        ((haarIntegers E).map P) ∧
      ∫ x, (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) x ∂((haarIntegers E).map P) =
        ∫ u in (valBall E n : Set E), (χ (P u) : ℂ) ∂haarIntegers E := by
  have hD : MeasurableSet (valBall F m : Set F) := (isOpen_valBall m).measurableSet
  have hc : Continuous fun x => (χ x : ℂ) := continuous_induced_dom.comp hχ
  have hg : Measurable ((valBall F m : Set F).indicator (fun x => (χ x : ℂ))) :=
    hc.measurable.indicator hD
  constructor
  · rw [integrable_indicator_iff hD]
    refine Measure.integrableOn_of_bounded (M := 1) ?_ hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq (Circle.norm_coe _))
    rw [Measure.map_apply hP.measurable hD, hpre]
    exact (isCompact_valBall n).measure_lt_top.ne
  · rw [integral_map hP.aemeasurable hg.aestronglyMeasurable,
      ← integral_indicator (isOpen_valBall n).measurableSet]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ (valBall E n : Set E)
    · have hu' : P u ∈ (valBall F m : Set F) := by
        have : u ∈ P ⁻¹' (valBall F m : Set F) := hpre ▸ hu
        exact this
      simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hu']
    · have hu' : P u ∉ (valBall F m : Set F) := fun h => hu (hpre ▸ (show u ∈ P ⁻¹' _ from h))
      simp only [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']

theorem ball_sum_eq_zero (hcont : Continuous (algebraMap F E)) {χ : AddChar F Circle}
    (hχ : Continuous χ) {a : F} (ha : a ≠ 0) (c : NNReal) (κ : ENNReal)
    (hm : ∀ S : Set F, MeasurableSet S →
      haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) +
        (c : ENNReal) * haarIntegers E ((fun u : E => a * Algebra.norm F u) ⁻¹' S) =
          κ * haarIntegers F S)
    {m : ℤ} {b : F} (hb : b ∈ valBall F m) (hχb : χ b ≠ 1) (ν : Measure E) [ν.IsAddHaarMeasure] :
    (∫ u in (valBall E (radius F E 1 m) : Set E), (χ (Algebra.norm F u) : ℂ) ∂ν) +
      ((c : ℝ) : ℂ) * ∫ u in (valBall E (radius F E a m) : Set E),
        (χ (a * Algebra.norm F u) : ℂ) ∂ν = 0 := by
  have hN : Continuous (Algebra.norm F : E → F) := GlobalTheory.CompanionTheory.WeilSB.continuous_norm_of hcont
  have hNa : Continuous (fun u : E => a * Algebra.norm F u) := continuous_const.mul hN
  have p1 : (Algebra.norm F : E → F) ⁻¹' (valBall F m : Set F) =
      (valBall E (radius F E 1 m) : Set E) := by
    rw [← preimage_valBall one_ne_zero m]
    simp only [one_mul]
  obtain ⟨i1, e1⟩ := map_facts hχ hN p1
  obtain ⟨i2, e2⟩ := map_facts hχ hNa (preimage_valBall ha m)
  have hsum : (haarIntegers E).map (Algebra.norm F : E → F) +
      (c : ENNReal) • (haarIntegers E).map (fun u : E => a * Algebra.norm F u) =
        κ • haarIntegers F := by
    ext S hS
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply hN.measurable hS, Measure.map_apply hNa.measurable hS]
    exact hm S hS
  have key : ∫ x, (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) x
      ∂((haarIntegers E).map (Algebra.norm F : E → F) +
        (c : ENNReal) • (haarIntegers E).map (fun u : E => a * Algebra.norm F u)) =
      ∫ x, (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) x ∂(κ • haarIntegers F) := by
    rw [hsum]
  rw [integral_add_measure i1 (i2.smul_measure ENNReal.coe_ne_top), integral_smul_measure,
    integral_smul_measure, e1, e2, integral_indicator (isOpen_valBall m).measurableSet,
    integral_valBall_char_eq_zero _ hb hχb, smul_zero] at key
  obtain ⟨t, ht⟩ : ∃ t : ENNReal, ν = t • haarIntegers E := ⟨_, eq_smul_haarIntegers ν⟩
  rw [ht, Measure.restrict_smul, Measure.restrict_smul, integral_smul_measure,
    integral_smul_measure]
  rw [ENNReal.coe_toReal, Complex.real_smul] at key
  rw [Complex.real_smul, Complex.real_smul]
  linear_combination (t.toReal : ℂ) * key

end Main

theorem ball_integrals_cancel : (∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : ENNReal, κ ≠ ⊤ ∧ ∀ S : Set F, MeasurableSet S →
  haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) + (modulus (a : F) : ENNReal) * haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S) = κ * haarIntegers F S) → ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), (¬ ∃ t : Eˣ, Algebra.norm F (t : E) = a) → ∀ N₀ : ℤ,
  ∃ n₁ ≤ N₀, ∃ n₂ ≤ N₀,
    (∫ u in (valBall E n₁ : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ) +
      ((modulus (a : F) : ℝ) : ℂ) * ∫ u in (valBall E n₂ : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ = 0 := by
  intro H F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη a hna N₀
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hnr : a ∉ (normUnits F E).range := fun ⟨t, ht⟩ => hna ⟨t, by rw [← coe_normUnits, ht]⟩
  obtain ⟨κ, -, hκ⟩ := H F E hcont a hnr
  obtain ⟨b, hχb⟩ := AddChar.ne_one_iff.1 hχ1
  obtain ⟨M, hM⟩ := exists_mem_valBall_neg_nat b
  obtain ⟨m, h0, h1, h2⟩ : ∃ m : ℤ, m ≤ -(M : ℤ) ∧ m ≤ ord (1 : F) + residueDegree F E * N₀ ∧
      m ≤ ord (a : F) + residueDegree F E * N₀ :=
    ⟨min (-(M : ℤ)) (min (ord (1 : F) + residueDegree F E * N₀)
      (ord (a : F) + residueDegree F E * N₀)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hbm : b ∈ valBall F m := valBall_antitone h0 hM
  exact ⟨radius F E 1 m, radius_le h1, radius F E (a : F) m, radius_le h2,
    ball_sum_eq_zero hcont hχ a.ne_zero _ κ hκ hbm hχb (muE E χ)⟩

end GlobalTheory.CompanionTheory.WeilGaussNon
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_norm_weil_constant_value : (∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : ENNReal, κ ≠ ⊤ ∧ ∀ S : Set F, MeasurableSet S →
  haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) + (modulus (a : F) : ENNReal) * haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S) = κ * haarIntegers F S) → ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), (¬ ∃ t : Eˣ, Algebra.norm F (t : E) = a) → ∀ N₀ : ℤ,
  ∃ n₁ ≤ N₀, ∃ n₂ ≤ N₀,
    (∫ u in (valBall E n₁ : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ) +
      ((modulus (a : F) : ℝ) : ℂ) * ∫ u in (valBall E n₂ : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WeilGaussNon.ball_integrals_cancel
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WGaussEx

theorem wGaussEx : Ad3.K.GL2LocalData.WGaussEx := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη
  have hcore := GlobalTheory.T.norm_form_integral_fourier_factorization F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hst := GlobalTheory.T.norm_form_ball_integral_stabilizes GlobalTheory.T.norm_form_integral_fourier_factorization F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hsc := GlobalTheory.T.norm_form_ball_integral_scaling F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hnon := GlobalTheory.T.non_norm_weil_constant_value (GlobalTheory.T.non_norm_gauss_integral_sign GlobalTheory.T.non_norm_ball_integral_vanishes) F χ hχ hχ1 E hfr hcont σ hσ η hη
  choose c n₀ hc using hst
  refine ⟨c 1, fun a Φ hΦ => ?_⟩
  obtain ⟨n₁, h₁⟩ := hcore a Φ hΦ
  have hL := h₁ (min n₁ (n₀ a)) (min_le_left _ _)
  rw [hc a _ (min_le_right _ _)] at hL
  rw [hL]
  congr 1
  have hne : ((modulus (a : F) : ℝ) : ℂ) ≠ 0 := by
    have : (modulus (a : F) : ℝ) ≠ 0 := by
      simpa using modulus_ne_zero a.ne_zero
    exact_mod_cast this
  by_cases ha : ∃ t : Eˣ, Algebra.norm F (t : E) = a
  · obtain ⟨t, ht⟩ := ha
    have hn : nsg E (a : F) = 1 := by
      rw [nsg, if_pos ⟨t, ht⟩]
    let m := min (n₀ a) (min (n₀ 1) (n₀ 1 - ord (t : E)))
    have e := hsc t m
    have e1 : ∫ u in (valBall E m : Set E), (χ (Algebra.norm F (t : E) * Algebra.norm F u) : ℂ) ∂muE E χ = c a := by
      rw [ht]; exact hc a m (min_le_left _ _)
    have e2 : ∫ u in (valBall E (m + ord (t : E)) : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ = c 1 := by
      have := hc 1 (m + ord (t : E)) (by
        have : m ≤ n₀ 1 - ord (t : E) := (min_le_right _ _).trans (min_le_right _ _)
        omega)
      simpa using this
    rw [e1, e2, ht] at e
    rw [e, hn]
    push_cast
    ring
  · have hn : nsg E (a : F) = -1 := by
      rw [nsg, if_neg ha]
    obtain ⟨m₁, hm₁, m₂, hm₂, e⟩ := hnon a ha (min (n₀ 1) (n₀ a))
    have e1 : ∫ u in (valBall E m₁ : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ = c 1 := by
      have := hc 1 m₁ (hm₁.trans (min_le_left _ _))
      simpa using this
    rw [e1, hc a m₂ (hm₂.trans (min_le_right _ _))] at e
    rw [hn]
    push_cast
    field_simp
    linear_combination e

end GlobalTheory.CompanionTheory.WGaussEx
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_gauss_sum_existence_hypothesis : Ad3.K.GL2LocalData.WGaussEx := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WGaussEx.wGaussEx
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilRepW

open GlobalTheory.CompanionTheory.WeilSB (sb_comp sb_mul isLocallyConstant_char continuous_norm_of)
open GlobalTheory.CompanionTheory.SplitRep (chi_add modulus_neg_one modulus_neg')

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]
  [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem norm_neg' (x : E) : Algebra.norm F (-x) = Algebra.norm F x := by
  apply (algebraMap F E).injective
  simp [algebraMap_norm_eq_mul_conj]

theorem fts_apply (χ : AddChar F Circle) (μ : Measure E) (Φ : E → ℂ) (u : E) :
    FTs χ (conj F E) μ Φ u = localFourier μ (chE E χ) Φ (conj F E u) := by
  simp only [FTs, localFourier]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show Φ z * (χ _ : ℂ) = Φ z * (χ (Algebra.trace F E (z * conj F E u)) : ℂ)
  rw [mul_comm (conj F E u)]

theorem integral_conj (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → ℂ) :
    ∫ x, f (conj F E x) ∂μ = ∫ x, f x ∂μ := by
  have h := (conjContinuousAddEquiv F E).toHomeomorph.measurableEmbedding.integral_map (μ := μ) f
  have e : ((conjContinuousAddEquiv F E).toHomeomorph : E → E) = conj F E := rfl
  rw [e, map_conj_eq] at h
  exact h.symm

theorem fts_sbe {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) (μ : Measure E)
    [μ.IsAddHaarMeasure] {Φ : E → ℂ} (hΦ : Φ ∈ SBE E) : FTs χ (conj F E) μ Φ ∈ SBE E := by
  have hχE : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hχE1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  have e : FTs χ (conj F E) μ Φ = fun u =>
      localFourier μ (chE E χ) Φ ((conjContinuousAddEquiv F E).toHomeomorph u) :=
    funext fun u => fts_apply χ μ Φ u
  rw [e]
  exact sb_comp _ (localFourier_mem_schwartzBruhat μ hχE hχE1 hΦ)

theorem fts_fts {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) {Φ : E → ℂ}
    (hΦ : Φ ∈ SBE E) (z : E) :
    FTs χ (conj F E) (muE E χ) (FTs χ (conj F E) (muE E χ) Φ) z = Φ (-z) := by
  have hχE : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hχE1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  rw [fts_apply, ← localFourier_localFourier_selfDual hχE hχE1 hΦ z]
  calc localFourier (muE E χ) (chE E χ) (FTs χ (conj F E) (muE E χ) Φ) (conj F E z)
      = ∫ u, (fun v => localFourier (muE E χ) (chE E χ) Φ v * (chE E χ (v * z) : ℂ)) (conj F E u)
          ∂muE E χ := by
        rw [localFourier]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        have e : conj F E u * z = conj F E (u * conj F E z) := by simp [map_mul]
        show FTs χ (conj F E) (muE E χ) Φ u * (χ (Algebra.trace F E (u * conj F E z)) : ℂ) =
          localFourier (muE E χ) (chE E χ) Φ (conj F E u) * (χ (Algebra.trace F E (conj F E u * z)) : ℂ)
        rw [fts_apply, e, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.trace_conj]
    _ = ∫ v, localFourier (muE E χ) (chE E χ) Φ v * (chE E χ (v * z) : ℂ) ∂muE E χ :=
        integral_conj (F := F) (muE E χ) (fun v => localFourier (muE E χ) (chE E χ) Φ v * (chE E χ (v * z) : ℂ))
    _ = _ := rfl

omit [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
  [ValuativeRel E] [IsNonarchimedeanLocalField E] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace F] [TopologicalSpace E] in
theorem nsg_one : nsg E (1 : F) = 1 := by
  unfold nsg
  exact if_pos ⟨1, by simp⟩

omit [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
  [ValuativeRel E] [IsNonarchimedeanLocalField E] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace F] [TopologicalSpace E] in
theorem nsg_sq (x : F) : nsg E x * nsg E x = 1 := by
  unfold nsg
  split_ifs <;> norm_num

omit [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
  [ValuativeRel E] [IsNonarchimedeanLocalField E] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace F] [TopologicalSpace E] in
theorem nsg_mul {η : Fˣ →* ℂˣ} (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {x y : F}
    (hx : x ≠ 0) (hy : y ≠ 0) : nsg E (x * y) = nsg E x * nsg E y := by
  have h := hη (Units.mk0 x hx * Units.mk0 y hy)
  rw [map_mul, Units.val_mul, hη, hη] at h
  simpa using h.symm

theorem rWm_zero (χ : AddChar F Circle) (μ : Measure E) (lam : ℂ) {g : Matrix (Fin 2) (Fin 2) F}
    (h : g 1 0 = 0) (Φ : E → ℂ) (z : E) :
    rWm χ (conj F E) μ lam g Φ z = (χ (g 0 0 * g 0 1 * Algebra.norm F z) : ℂ) * nsg E (g 0 0) *
      ((modulus (g 0 0) : ℝ) : ℂ) * Φ (algebraMap F E (g 0 0) * z) := by
  simp only [rWm, rW, if_pos h]

theorem rWm_ne (χ : AddChar F Circle) (μ : Measure E) (lam : ℂ) {g : Matrix (Fin 2) (Fin 2) F}
    (h : g 1 0 ≠ 0) (Φ : E → ℂ) (z : E) :
    rWm χ (conj F E) μ lam g Φ z = lam * nsg E (-(g 1 0)) * (((modulus (g 1 0) : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ u, (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u -
        Algebra.trace F E (conj F E z * u)) / g 1 0) : ℂ) * Φ u ∂μ := by
  simp only [rWm, rW, if_neg h]

theorem rW_w (χ : AddChar F Circle) (μ : Measure E) (lam : ℂ) (Φ : E → ℂ) :
    rWm χ (conj F E) μ lam !![0, 1; -1, 0] Φ = fun z => lam * FTs χ (conj F E) μ Φ z := by
  funext z
  rw [rWm_ne χ μ lam (by simp)]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, modulus_neg_one, neg_neg, nsg_one]
  simp only [NNReal.coe_one, inv_one, Complex.ofReal_one, mul_one]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have e : (0 * Algebra.norm F z + 0 * Algebra.norm F u - Algebra.trace F E (conj F E z * u)) / (-1 : F) =
      Algebra.trace F E (conj F E z * u) := by ring
  show (χ _ : ℂ) * Φ u = Φ u * (χ _ : ℂ)
  rw [e, mul_comm]

def GaussAt (χ : AddChar F Circle) (lam : ℂ) : Prop :=
  ∀ (a : Fˣ), ∀ Φ ∈ SBE E,
    ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTs χ (conj F E) (muE E χ) Φ u ∂muE E χ =
      lam * nsg E (a : F) * (((modulus (a : F) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ

theorem lam_sq {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) {lam : ℂ} (hG : GaussAt (E := E) χ lam) :
    lam * lam * nsg E (-1 : F) = 1 := by
  have hN := continuous_norm_of (F := F) (E := E) hcont
  have hlc := isLocallyConstant_char hχ hχ1
  set f : E → ℂ := (valBall E 0 : Set E).indicator (fun _ => (1 : ℂ)) with hf
  have hfS : f ∈ SBE E := indicator_valBall_zero_mem_schwartzBruhat (K := E)
  set Φ : E → ℂ := fun z => (χ (-(Algebra.norm F z)) : ℂ) * f z with hΦd
  have hΦ : Φ ∈ SBE E := sb_mul (hlc.comp_continuous hN.neg) hfS
  set I : ℂ := ∫ z, (χ (Algebra.norm F z) : ℂ) * Φ z ∂muE E χ with hI
  have hI1 : I = (((muE E χ).real (valBall E 0 : Set E) : ℝ) : ℂ) := by
    have e : ∀ z, (χ (Algebra.norm F z) : ℂ) * Φ z = f z := fun z => by
      simp only [hΦd]
      rw [← mul_assoc, ← chi_add, add_neg_cancel, AddChar.map_zero_eq_one]
      simp
    simp only [hI, e, hf]
    rw [integral_indicator_const (1 : ℂ) (measurableSet_valBall 0)]
    simp
  have hI0 : I ≠ 0 := by
    rw [hI1]
    have hpos : 0 < (muE E χ) (valBall E 0 : Set E) :=
      (isOpen_valBall 0).measure_pos _ ⟨0, zero_mem _⟩
    have hfin := (isCompact_valBall (K := E) 0).measure_lt_top (μ := muE E χ)
    have : 0 < (muE E χ).real (valBall E 0 : Set E) := ENNReal.toReal_pos hpos.ne' hfin.ne
    exact_mod_cast this.ne'
  have h1 := hG 1 _ (fts_sbe hχ hχ1 (muE E χ) hΦ)
  have h2 := hG (-1) Φ hΦ
  have hL : ∫ u, (χ (((1 : Fˣ) : F) * Algebra.norm F u) : ℂ) *
      FTs χ (conj F E) (muE E χ) (FTs χ (conj F E) (muE E χ) Φ) u ∂muE E χ = I := by
    rw [hI, ← integral_neg_eq_self (fun z => (χ (Algebra.norm F z) : ℂ) * Φ z)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show _ * _ = _ * _
    rw [fts_fts hχ hχ1 hΦ, norm_neg', Units.val_one, one_mul]
  have hR1 : ∫ z, (χ (-(Algebra.norm F z) / ((1 : Fˣ) : F)) : ℂ) *
      FTs χ (conj F E) (muE E χ) Φ z ∂muE E χ =
      ∫ u, (χ (((-1 : Fˣ) : F) * Algebra.norm F u) : ℂ) * FTs χ (conj F E) (muE E χ) Φ u ∂muE E χ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp
  have hR2 : ∫ z, (χ (-(Algebra.norm F z) / ((-1 : Fˣ) : F)) : ℂ) * Φ z ∂muE E χ = I := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp
  rw [hL, hR1, h2, hR2] at h1
  simp only [Units.val_one, Units.val_neg, modulus_neg_one, modulus_one, nsg_one] at h1
  simp only [NNReal.coe_one, inv_one, Complex.ofReal_one, mul_one] at h1
  have : I * (lam * lam * nsg E (-1 : F) - 1) = 0 := by linear_combination -h1
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hI0
  · linear_combination h

theorem lam_mul_self {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) {lam : ℂ} (hG : GaussAt (E := E) χ lam) :
    lam * lam = nsg E (-1 : F) := by
  have h := lam_sq hχ hχ1 hcont hG
  have hs := nsg_sq (E := E) (-1 : F)
  linear_combination nsg E (-1 : F) * h - lam * lam * hs

theorem gauss_step {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) {η : Fˣ →* ℂˣ}
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {lam : ℂ} (hG : GaussAt (E := E) χ lam)
    {Φ : E → ℂ} (hΦ : Φ ∈ SBE E) {a b c d : F} (hc : c ≠ 0) (hd : d ≠ 0)
    (hdet : a * d - b * c = 1) (z : E) :
    lam * nsg E (-c) * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v -
        Algebra.trace F E (conj F E z * v)) / c) : ℂ) *
          (lam * FTs χ (conj F E) (muE E χ) Φ v) ∂muE E χ =
    lam * nsg E d * (((modulus d : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ u, (χ ((-b * Algebra.norm F z + c * Algebra.norm F u -
        Algebra.trace F E (conj F E z * u)) / (-d)) : ℂ) * Φ u ∂muE E χ := by
  have hχE : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hχE1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  have ha : a = (1 + b * c) / d := by
    field_simp
    linear_combination hdet
  set t : E := algebraMap F E d⁻¹ * z with ht
  have hJt : conj F E t = algebraMap F E d⁻¹ * conj F E z := by
    rw [ht, map_mul, conj_algebraMap]
  set Ψ : E → ℂ := fun u => (χ (Algebra.trace F E (conj F E t * u)) : ℂ) * Φ u with hΨd
  have hΨ : Ψ ∈ SBE E :=
    sb_mul (f := fun u => (chE E χ (conj F E t * u) : ℂ))
      ((isLocallyConstant_char hχE hχE1).comp_continuous (continuous_const.mul continuous_id)) hΦ
  have hA : d / c ≠ 0 := div_ne_zero hd hc
  have hG' := hG (Units.mk0 (d / c) hA) Ψ hΨ
  simp only [Units.val_mk0] at hG'
  have hFT : ∀ v, FTs χ (conj F E) (muE E χ) Ψ v = FTs χ (conj F E) (muE E χ) Φ (v + t) := by
    intro v
    simp only [FTs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : conj F E (v + t) * u = conj F E t * u + conj F E v * u := by
      rw [map_add]
      ring
    show (χ _ : ℂ) * Φ u * (χ _ : ℂ) = Φ u * (χ _ : ℂ)
    rw [e, map_add, chi_add]
    ring
  have h1 : ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v -
        Algebra.trace F E (conj F E z * v)) / c) : ℂ) * FTs χ (conj F E) (muE E χ) Φ v ∂muE E χ =
      (χ (b * Algebra.norm F z / d) : ℂ) * ∫ v, (χ (d / c * Algebra.norm F v) : ℂ) *
        FTs χ (conj F E) (muE E χ) Ψ v ∂muE E χ := by
    rw [← integral_add_right_eq_self (fun v => (χ ((a * Algebra.norm F z + d * Algebra.norm F v -
        Algebra.trace F E (conj F E z * v)) / c) : ℂ) * FTs χ (conj F E) (muE E χ) Φ v) t,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hNt : Algebra.norm F t = d⁻¹ ^ 2 * Algebra.norm F z := by
      rw [ht, map_mul, norm_algebraMap_eq_sq]
    have hT1 : Algebra.trace F E (v * conj F E t) = d⁻¹ * Algebra.trace F E (conj F E z * v) := by
      rw [hJt, show v * (algebraMap F E d⁻¹ * conj F E z) =
        algebraMap F E d⁻¹ * (conj F E z * v) by ring, trace_algebraMap_mul]
    have hT2 : Algebra.trace F E (conj F E z * (v + t)) =
        Algebra.trace F E (conj F E z * v) + d⁻¹ * (2 * Algebra.norm F z) := by
      have e2 : conj F E z * t = algebraMap F E d⁻¹ * algebraMap F E (Algebra.norm F z) := by
        rw [algebraMap_norm_eq_mul_conj (K := F), ht]
        ring
      rw [mul_add, map_add, e2, trace_algebraMap_mul, Algebra.trace_algebraMap,
        (Fact.out : Module.finrank F E = 2)]
      simp
    have e : (a * Algebra.norm F z + d * Algebra.norm F (v + t) -
        Algebra.trace F E (conj F E z * (v + t))) / c =
        b * Algebra.norm F z / d + d / c * Algebra.norm F v := by
      rw [norm_add, hNt, hT1, hT2, ha]
      field_simp
      ring
    show (χ _ : ℂ) * _ = _ * ((χ _ : ℂ) * _)
    rw [e, chi_add, hFT]
    ring
  have h2 : ∫ u, (χ ((-b * Algebra.norm F z + c * Algebra.norm F u -
        Algebra.trace F E (conj F E z * u)) / (-d)) : ℂ) * Φ u ∂muE E χ =
      (χ (b * Algebra.norm F z / d) : ℂ) * ∫ u, (χ (-(Algebra.norm F u) / (d / c)) : ℂ) * Ψ u ∂muE E χ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hT : Algebra.trace F E (conj F E t * u) = d⁻¹ * Algebra.trace F E (conj F E z * u) := by
      rw [hJt, mul_assoc, trace_algebraMap_mul]
    have e : (-b * Algebra.norm F z + c * Algebra.norm F u -
        Algebra.trace F E (conj F E z * u)) / (-d) =
        b * Algebra.norm F z / d + (-(Algebra.norm F u) / (d / c) +
          Algebra.trace F E (conj F E t * u)) := by
      rw [hT]
      field_simp
      ring
    simp only [hΨd, e, chi_add]
    ring
  have hMc : ((modulus c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hc
  have hMd : ((modulus d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hd
  have hmod : modulus (d / c) = modulus d * (modulus c)⁻¹ := by
    rw [div_eq_mul_inv, modulus_mul, modulus_inv]
  have hl := lam_mul_self hχ hχ1 hcont hG
  have hs : nsg E (-c) * nsg E (d / c) = nsg E (-1 : F) * nsg E d := by
    rw [← nsg_mul hη (neg_ne_zero.2 hc) hA, ← nsg_mul hη (neg_ne_zero.2 one_ne_zero) hd]
    congr 1
    field_simp
  have hM := nsg_sq (E := E) (-1 : F)
  have hfac : ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v -
        Algebra.trace F E (conj F E z * v)) / c) : ℂ) *
          (lam * FTs χ (conj F E) (muE E χ) Φ v) ∂muE E χ =
      lam * ∫ v, (χ ((a * Algebra.norm F z + d * Algebra.norm F v -
        Algebra.trace F E (conj F E z * v)) / c) : ℂ) * FTs χ (conj F E) (muE E χ) Φ v ∂muE E χ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show _ * (_ * _) = _ * (_ * _)
    ring
  rw [hfac, h1, hG', h2, hmod]
  generalize (∫ u, (χ (-(Algebra.norm F u) / (d / c)) : ℂ) * Ψ u ∂muE E χ) = I
  generalize (χ (b * Algebra.norm F z / d) : ℂ) = X
  push_cast
  have key : lam * lam * (nsg E (-c) * nsg E (d / c)) = nsg E d := by
    rw [hs, hl, ← mul_assoc, hM, one_mul]
  have hMc' : (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus c : ℝ) : ℂ)) = 1 := by
    push_cast
    field_simp
  push_cast at hMc'
  simp only [inv_inv, mul_inv]
  linear_combination (lam * X * I * ((modulus d : ℝ) : ℂ)⁻¹ * (((modulus c : ℝ) : ℂ)⁻¹ * ((modulus c : ℝ) : ℂ))) * key +
    (lam * X * I * ((modulus d : ℝ) : ℂ)⁻¹ * nsg E d) * hMc'

theorem rep_w {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) {η : Fˣ →* ℂˣ}
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {lam : ℂ} (hG : GaussAt (E := E) χ lam)
    {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1) {Φ : E → ℂ} (hΦ : Φ ∈ SBE E) :
    rWm χ (conj F E) (muE E χ) lam (g * !![0, 1; -1, 0]) Φ =
      rWm χ (conj F E) (muE E χ) lam g (rWm χ (conj F E) (muE E χ) lam !![0, 1; -1, 0] Φ) := by
  have e00 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 0 0 = -g 0 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 0 1 = g 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 1 0 = -g 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)) 1 1 = g 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hd2 : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hg
  have hl := lam_mul_self hχ hχ1 hcont hG
  rw [rW_w]
  funext z
  by_cases hd : g 1 1 = 0
  · have hbc : g 0 1 * g 1 0 = -1 := by rw [hd] at hd2; linear_combination -hd2
    have hb : g 0 1 ≠ 0 := fun h => by rw [h] at hbc; simp at hbc
    have hc : g 1 0 ≠ 0 := fun h => by rw [h] at hbc; simp at hbc
    have hcb : g 1 0 = -(g 0 1)⁻¹ := by field_simp; linear_combination hbc
    have hinv : ∫ u, FTs χ (conj F E) (muE E χ) Φ u *
        (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u)) : ℂ) ∂muE E χ =
        Φ (-(algebraMap F E (g 0 1) * z)) := fts_fts hχ hχ1 hΦ _
    rw [rWm_zero χ _ lam (by rw [e10, hd, neg_zero]), rWm_ne χ _ lam hc, e00, e01, hd, modulus_neg']
    have e1 : ∫ u, (χ ((g 0 0 * Algebra.norm F z + 0 * Algebra.norm F u -
        Algebra.trace F E (conj F E z * u)) / g 1 0) : ℂ) *
          (lam * FTs χ (conj F E) (muE E χ) Φ u) ∂muE E χ =
        lam * ((χ (-g 0 1 * g 0 0 * Algebra.norm F z) : ℂ) * ∫ u, FTs χ (conj F E) (muE E χ) Φ u *
          (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u)) : ℂ) ∂muE E χ) := by
      rw [← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      have hT : Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u) =
          g 0 1 * Algebra.trace F E (conj F E z * u) := by
        rw [map_mul (conj F E), conj_algebraMap, mul_assoc, trace_algebraMap_mul]
      have e : (g 0 0 * Algebra.norm F z + 0 * Algebra.norm F u -
          Algebra.trace F E (conj F E z * u)) / g 1 0 =
          -g 0 1 * g 0 0 * Algebra.norm F z +
            Algebra.trace F E (conj F E (algebraMap F E (g 0 1) * z) * u) := by
        rw [hT, hcb]
        field_simp
        ring
      show (χ _ : ℂ) * (_ * _) = _ * (_ * (_ * _))
      rw [e, chi_add]
      ring
    have hm : modulus (g 1 0) = (modulus (g 0 1))⁻¹ := by
      rw [hcb, modulus_neg', modulus_inv]
    have hneg : -(algebraMap F E (g 0 1) * z) = algebraMap F E (-g 0 1) * z := by simp
    have hs1 : nsg E (-(g 1 0)) * nsg E (g 0 1) = 1 := by
      rw [← nsg_mul hη (neg_ne_zero.2 hc) hb, show -(g 1 0) * g 0 1 = 1 by linear_combination -hbc,
        nsg_one]
    have hs2 : nsg E (-g 0 1) = nsg E (-1 : F) * nsg E (g 0 1) := by
      rw [← nsg_mul hη (neg_ne_zero.2 one_ne_zero) hb]
      congr 1
      ring
    have hB := nsg_sq (E := E) (g 0 1)
    have hs3 : nsg E (-(g 1 0)) = nsg E (g 0 1) := by linear_combination nsg E (g 0 1) * hs1 - nsg E (-(g 1 0)) * hB
    rw [e1, hinv, hm, hneg, hs3, hs2, ← hl]
    push_cast
    simp only [inv_inv]
    ring
  · by_cases hc : g 1 0 = 0
    · have had : g 0 0 * g 1 1 = 1 := by rw [hc] at hd2; linear_combination hd2
      have ha : g 0 0 ≠ 0 := fun h => by rw [h] at had; simp at had
      have hda : g 1 1 = (g 0 0)⁻¹ := by field_simp; linear_combination had
      have hFT : FTs χ (conj F E) (muE E χ) Φ (algebraMap F E (g 0 0) * z) =
          ∫ u, Φ u * (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u)) : ℂ) ∂muE E χ := rfl
      rw [rWm_ne χ _ lam (by rw [e10]; exact neg_ne_zero.mpr hd), rWm_zero χ _ lam hc, e00, e10, e11,
        modulus_neg', hFT, hc]
      have hs : nsg E (- -(g 1 1)) = nsg E (g 0 0) := by
        have h1 : nsg E (g 1 1) * nsg E (g 0 0) = 1 := by
          rw [← nsg_mul hη hd ha, mul_comm, had, nsg_one]
        have hB := nsg_sq (E := E) (g 0 0)
        rw [neg_neg]
        linear_combination nsg E (g 0 0) * h1 - nsg E (g 1 1) * hB
      have e1 : ∫ u, (χ ((-g 0 1 * Algebra.norm F z + 0 * Algebra.norm F u -
          Algebra.trace F E (conj F E z * u)) / -(g 1 1)) : ℂ) * Φ u ∂muE E χ =
          (χ (g 0 0 * g 0 1 * Algebra.norm F z) : ℂ) * ∫ u, Φ u *
            (χ (Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u)) : ℂ) ∂muE E χ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        have hT : Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u) =
            g 0 0 * Algebra.trace F E (conj F E z * u) := by
          rw [map_mul (conj F E), conj_algebraMap, mul_assoc, trace_algebraMap_mul]
        have e : (-g 0 1 * Algebra.norm F z + 0 * Algebra.norm F u -
            Algebra.trace F E (conj F E z * u)) / -(g 1 1) =
            g 0 0 * g 0 1 * Algebra.norm F z +
              Algebra.trace F E (conj F E (algebraMap F E (g 0 0) * z) * u) := by
          rw [hT, hda]
          field_simp
          ring
        show (χ _ : ℂ) * _ = _ * (_ * _)
        rw [e, chi_add]
        ring
      rw [e1, hs, hda, modulus_inv]
      push_cast
      simp only [inv_inv]
      ring
    · rw [rWm_ne χ _ lam (by rw [e10]; exact neg_ne_zero.mpr hd), rWm_ne χ _ lam hc, e00, e10, e11,
        modulus_neg', neg_neg]
      exact (gauss_step hχ hχ1 hcont hη hG hΦ hc hd hd2 z).symm

theorem wRepW : Ad3.K.GL2LocalData.WRepW := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη g hg Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hσc : σ = conj F E := (eq_one_or_eq_conj σ).resolve_left hσ
  subst hσc
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.weil_gauss_sum_existence_hypothesis F χ hχ hχ1 E hfr hcont _ hσ η hη
  have hl : γ = lamE E χ η := GlobalTheory.T.weil_gauss_constant_hypothesis F χ hχ hχ1 E hfr hcont _ hσ η hη γ hγ
  subst hl
  exact rep_w hχ hχ1 hcont hη hγ hg hΦ

end GlobalTheory.CompanionTheory.WeilRepW
end
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
theorem _root_.GlobalTheory.T.weil_representation_whittaker_hypothesis : Ad3.K.GL2LocalData.WRepW := by
  first | exact @GlobalTheory.CompanionTheory.WeilRepW.wRepW | exact GlobalTheory.CompanionTheory.WeilRepW.wRepW | (intros; apply GlobalTheory.CompanionTheory.WeilRepW.wRepW <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilRepW.wRepW | exact GlobalTheory.CompanionTheory.WeilRepW.wRepW | (intros; apply GlobalTheory.CompanionTheory.WeilRepW.wRepW <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilRepW.rep_w | exact GlobalTheory.CompanionTheory.WeilRepW.rep_w | (intros; apply GlobalTheory.CompanionTheory.WeilRepW.rep_w <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilRepW.gauss_step | exact GlobalTheory.CompanionTheory.WeilRepW.gauss_step | (intros; apply GlobalTheory.CompanionTheory.WeilRepW.gauss_step <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilRepW.lam_mul_self | exact GlobalTheory.CompanionTheory.WeilRepW.lam_mul_self | (intros; apply GlobalTheory.CompanionTheory.WeilRepW.lam_mul_self <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilRepW.lam_sq | exact GlobalTheory.CompanionTheory.WeilRepW.lam_sq | (intros; apply GlobalTheory.CompanionTheory.WeilRepW.lam_sq <;> assumption)
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2LocalData.WRepProof

def RightRule {F X : Type} [Field F] (R : Matrix (Fin 2) (Fin 2) F → X → X) (S : Set X)
    (h : Matrix (Fin 2) (Fin 2) F) : Prop :=
  h.det = 1 ∧ ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ S, R (g * h) Φ = R g (R h Φ)

theorem RightRule.mul {F X : Type} [Field F] {R : Matrix (Fin 2) (Fin 2) F → X → X} {S : Set X}
    (hS : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ S, R g Φ ∈ S)
    {h₁ h₂ : Matrix (Fin 2) (Fin 2) F} (p₁ : RightRule R S h₁) (p₂ : RightRule R S h₂) :
    RightRule R S (h₁ * h₂) := by
  refine ⟨by rw [Matrix.det_mul, p₁.1, p₂.1, one_mul], fun g hg Φ hΦ => ?_⟩
  have hΦ' := hS h₂ p₂.1 Φ hΦ
  rw [← mul_assoc, p₂.2 (g * h₁) (by rw [Matrix.det_mul, hg, p₁.1, one_mul]) Φ hΦ,
    p₁.2 g hg _ hΦ', p₂.2 h₁ p₁.1 Φ hΦ]

theorem rightRule_all {F X : Type} [Field F] {R : Matrix (Fin 2) (Fin 2) F → X → X} {S : Set X}
    (hS : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ S, R g Φ ∈ S)
    (hN : ∀ b : F, RightRule R S !![1, b; 0, 1])
    (hM : ∀ s : Fˣ, RightRule R S !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)])
    (hW : RightRule R S !![0, 1; -1, 0])
    (h : Matrix (Fin 2) (Fin 2) F) (hh : h.det = 1) : RightRule R S h := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact hh
  by_cases hc : h 1 0 = 0
  · rw [hc, mul_zero, sub_zero] at hdet
    have h0 : h 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have e : h = !![1, h 0 1 * h 0 0; 0, 1] * !![((Units.mk0 _ h0 : Fˣ) : F), 0; 0, (((Units.mk0 _ h0)⁻¹ : Fˣ) : F)] := by
      have e1 : h 1 1 = (h 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, e1, h0]
    rw [e]
    exact (hN _).mul hS (hM _)
  · have hs : -(h 1 0)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hc)
    have e : h = !![1, h 0 0 / h 1 0; 0, 1] *
        (!![((Units.mk0 _ hs : Fˣ) : F), 0; 0, (((Units.mk0 _ hs)⁻¹ : Fˣ) : F)] *
          (!![0, 1; -1, 0] * !![1, h 1 1 / h 1 0; 0, 1])) := by
      have e1 : h 0 1 = (h 0 0 * h 1 1 - 1) / h 1 0 := by
        rw [← hdet]
        field_simp
        ring
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      all_goals first | field_simp | skip
      all_goals first | (rw [e1]; field_simp; ring) | ring
    rw [e]
    exact (hN _).mul hS ((hM _).mul hS (hW.mul hS (hN _)))

end GlobalTheory.CompanionTheory.GL2LocalData.WRepProof

open GlobalTheory.CompanionTheory.GL2LocalData.WRepProof in

theorem GlobalTheory.CompanionTheory.GL2LocalData.wRep : Ad3.K.GL2LocalData.WRep := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη g h hg hh Φ hΦ
  have hS : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ SBE E, rWE E χ σ η g Φ ∈ SBE E :=
    fun g hg Φ hΦ => (GlobalTheory.CompanionTheory.WeilSB.wsb F χ hχ hχ1 E hfr hcont σ hσ η hη g hg Φ hΦ).1
  have hN : ∀ b : F, RightRule (rWE E χ σ η) (SBE E) !![1, b; 0, 1] := fun b =>
    ⟨by simp [Matrix.det_fin_two], fun g hg Φ hΦ =>
      GlobalTheory.CompanionTheory.GL2LocalData.wRepN F χ hχ hχ1 E hfr hcont σ hσ η hη g hg b Φ hΦ⟩
  have hM : ∀ s : Fˣ, RightRule (rWE E χ σ η) (SBE E) !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)] := fun s =>
    ⟨by simp [Matrix.det_fin_two], fun g hg Φ hΦ =>
      GlobalTheory.CompanionTheory.WeilTorus.wRepM F χ hχ hχ1 E hfr hcont σ hσ η hη g hg s Φ hΦ⟩
  have hW : RightRule (rWE E χ σ η) (SBE E) !![0, 1; -1, 0] :=
    ⟨by simp [Matrix.det_fin_two], fun g hg Φ hΦ =>
      GlobalTheory.T.weil_representation_whittaker_hypothesis F χ hχ hχ1 E hfr hcont σ hσ η hη g hg Φ hΦ⟩
  exact (rightRule_all hS hN hM hW h hh).2 g hg Φ hΦ
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_hypothesis : Ad3.K.GL2LocalData.WRep := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2LocalData.wRep
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilPiRep

section Red

variable {F : Type} [Field F]

def red (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  !![M 0 0 / M.det, M 0 1; M 1 0 / M.det, M 1 1]

theorem det_red {M : Matrix (Fin 2) (Fin 2) F} (hM : M.det ≠ 0) : (red M).det = 1 := by
  have e : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M
  simp only [red, Matrix.det_fin_two_of]
  field_simp
  rw [e]

theorem det_cjA {A : F} (hA : A ≠ 0) (M : Matrix (Fin 2) (Fin 2) F) : (cjA A M).det = M.det := by
  simp only [cjA, Matrix.det_fin_two_of, Matrix.det_fin_two M]
  field_simp

theorem red_mul {M N : Matrix (Fin 2) (Fin 2) F} (hM : M.det ≠ 0) (hN : N.det ≠ 0) :
    red (M * N) = red M * cjA M.det (red N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [red, cjA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_mul] <;> field_simp

end Red

section Dil

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]

theorem dil_mem {c : Eˣ →* ℂˣ} {Φ : E → ℂ} (hΦ : Φ ∈ SBc F E c) (t : Eˣ) :
    (fun y => Φ (y * (t : E))) ∈ SBc F E c := by
  refine ⟨hΦ.1.comp_continuous (continuous_mul_const _),
    hΦ.2.1.comp_homeomorph (Homeomorph.mulRight₀ (t : E) t.ne_zero), fun u hu x => ?_⟩
  show Φ (x * (u : E) * (t : E)) = _ * Φ (x * (t : E))
  rw [mul_right_comm, hΦ.2.2 u hu]

theorem const_mul_mem {c : Eˣ →* ℂˣ} {f : E → ℂ} (hf : f ∈ SBc F E c) (k : ℂ) :
    (fun y => k * f y) ∈ SBc F E c := by
  have h1 : IsLocallyConstant f := hf.1
  refine ⟨(IsLocallyConstant.const k).mul h1, hf.2.1.mul_left, fun u hu x => ?_⟩
  show k * f (x * (u : E)) = _ * (k * f x)
  rw [hf.2.2 u hu]
  ring

end Dil

theorem wPiRep : Ad3.K.GL2LocalData.WPiRep := by
  unfold WPiRep ForEF
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c Φ hΦ g h hh
  have wch := GlobalTheory.CompanionTheory.WeilChoice.wchoice F χ hχ hχ1 E hfr hcont σ hσ η hη
  have wdg := GlobalTheory.CompanionTheory.WeilDilation.wDiagT F χ hχ hχ1 E hfr hcont σ hσ η hη
  have wsb := GlobalTheory.CompanionTheory.WeilSB.wsb F χ hχ hχ1 E hfr hcont σ hσ η hη
  have wrp := GlobalTheory.T.weil_representation_hypothesis F χ hχ hχ1 E hfr hcont σ hσ η hη
  beta_reduce at wch wdg wsb wrp
  have hdet : ∀ x : GL (Fin 2) F, (x.val).det ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero
  obtain ⟨t, hnt, hpi⟩ : ∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det ∧
      piE E χ σ η c h Φ = fun x => (((c t : ℂˣ) : ℂ) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        rWE E χ σ η (red h.val) (fun y => Φ (y * (t : E))) x := by
    refine ⟨hh.choose, hh.choose_spec, ?_⟩
    funext x
    change piG χ σ (muE E χ) (lamE E χ η) c h Φ x = _
    unfold piG
    rw [dif_pos hh]
    rfl
  set k : ℂ := ((c t : ℂˣ) : ℂ) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) with hk
  set Ψ : E → ℂ := fun y => Φ (y * (t : E)) with hΨdef
  have hΨ : Ψ ∈ SBc F E c := dil_mem hΦ t
  have hΨE : Ψ ∈ SBE E := ⟨hΨ.1, hΨ.2.1⟩
  have hd1 : (red h.val).det = 1 := det_red (hdet h)
  have hmem : piE E χ σ η c h Φ ∈ SBc F E c := by
    rw [hpi]
    exact const_mul_mem ((wsb _ hd1 Ψ hΨE).2 c hΨ) k
  refine ⟨?_, hmem⟩
  by_cases hg : ∃ tg : Eˣ, Algebra.norm F (tg : E) = (g.val).det
  · obtain ⟨tg, htg⟩ := hg
    have hdg := hdet g
    have hgh : Algebra.norm F ((tg * t : Eˣ) : E) = ((g * h).val).det := by
      rw [Units.val_mul, map_mul, htg, hnt, Units.val_mul, Matrix.det_mul]
    rw [wch c Φ hΦ (g * h) (tg * t) hgh, wch c _ hmem g tg htg]
    set f : E → ℂ := fun y => Ψ (y * (tg : E)) with hfdef
    have hfE : f ∈ SBE E := by
      have := dil_mem hΨ tg
      exact ⟨this.1, this.2.1⟩
    have hcj : (cjA (g.val).det (red h.val)).det = 1 := by rw [det_cjA hdg, hd1]
    have hgd : (red g.val).det = 1 := det_red hdg
    have hL : (fun y => Φ (y * ((tg * t : Eˣ) : E))) = f := by
      funext y
      simp only [hfdef, hΨdef, Units.val_mul, mul_assoc]
    have hR : (fun y => piE E χ σ η c h Φ (y * (tg : E))) =
        fun y => k * rWE E χ σ η (cjA (g.val).det (red h.val)) f y := by
      funext y
      have := congrFun (wdg (red h.val) hd1 tg Ψ hΨE) y
      rw [htg] at this
      rw [hpi]
      simp only []
      rw [this]
    have e1 : rW χ σ (muE E χ) (lamE E χ η) (((g * h).val) 0 0 / ((g * h).val).det) (((g * h).val) 0 1)
        (((g * h).val) 1 0 / ((g * h).val).det) (((g * h).val) 1 1) f 1 =
        rWE E χ σ η (red (g * h).val) f 1 := rfl
    have e2 : rW χ σ (muE E χ) (lamE E χ η) ((g.val) 0 0 / (g.val).det) ((g.val) 0 1)
        ((g.val) 1 0 / (g.val).det) ((g.val) 1 1)
        (fun y => k * rWE E χ σ η (cjA (g.val).det (red h.val)) f y) 1 =
        k * rWE E χ σ η (red g.val) (rWE E χ σ η (cjA (g.val).det (red h.val)) f) 1 :=
      GlobalTheory.CompanionTheory.WeilChoice.rW_const_mul _ _ _ _ _ _ _ _ _ _ _
    rw [hL, hR, e1, e2, Units.val_mul, red_mul hdg (hdet h), wrp _ _ hgd hcj f hfE]
    have e3 : (((modulus ((g.val * h.val).det) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
        (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
      rw [Matrix.det_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    rw [e3, map_mul, Units.val_mul, hk]
    ring
  · have hg' : ¬ ∃ s : Eˣ, Algebra.norm F (s : E) = ((g * h).val).det := by
      rintro ⟨s, hs⟩
      refine hg ⟨s * t⁻¹, ?_⟩
      have hn : Algebra.norm F ((t⁻¹ : Eˣ) : E) * (h.val).det = 1 := by
        rw [← hnt, ← map_mul, Units.inv_mul, map_one]
      rw [Units.val_mul, map_mul, hs, Units.val_mul, Matrix.det_mul, mul_assoc, mul_comm (h.val).det, hn, mul_one]
    change Wc χ σ (muE E χ) (lamE E χ η) c Φ (g * h) = Wc χ σ (muE E χ) (lamE E χ η) c _ g
    unfold Wc
    rw [dif_neg hg', dif_neg hg]

end GlobalTheory.CompanionTheory.WeilPiRep
end
end
