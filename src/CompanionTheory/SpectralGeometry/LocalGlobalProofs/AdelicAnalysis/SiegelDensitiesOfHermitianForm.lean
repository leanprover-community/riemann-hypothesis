import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsIsCharAF
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocallyFinite
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresTransitivityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasuresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualHermMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualAdelicMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasuresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfRankSmallOrZeroStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueIntegrable

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_pure_tensor_eq_prod_of_isEulerProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → IsLocallyFiniteMeasure minf → (∀ v, IsLocallyFiniteMeasure (m v)) → ∀ (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf → Measurable Φ ∧ Integrable Φ I ∧ Multipliable (fun v => ∫ X, Φv v X ∂(m v)) ∧ ∫ X, Φ X ∂I = (∫ X, Φinf X ∂minf) * ∏' v, ∫ X, Φv v X ∂(m v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerInt.euler_int | exact GlobalTheory.CompanionTheory.SW.EulerInt.euler_int | (intros; apply GlobalTheory.CompanionTheory.SW.EulerInt.euler_int <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_scaling_selfdual_herm_measures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ n : ℕ, ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν, SdHerm F E σ (Ainf F) (psiInf F ψ) n ν ↔ ν = cinf • coordHerm (Ainf F) σ b laminf n) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) n ν ↔ ν = c v • coordHerm (Fv F v) σ b (lam v) n) := by
  first | exact @GlobalTheory.CompanionTheory.SW.sdHerm_eq_coord | exact GlobalTheory.CompanionTheory.SW.sdHerm_eq_coord | (intros; apply GlobalTheory.CompanionTheory.SW.sdHerm_eq_coord <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_scaling_selfdual_adelic_measures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ n : ℕ, ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) n μ ↔ μ = cinf • coordW (Ainf F) b laminf n M) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ, SdW F E σ M J (Fv F v) (psiV F ψ v) n μ ↔ μ = c v • coordW (Fv F v) b (lam v) n M) := by
  first | exact @GlobalTheory.CompanionTheory.SW.SdTuples.sdW_coord | exact GlobalTheory.CompanionTheory.SW.SdTuples.sdW_coord | (intros; apply GlobalTheory.CompanionTheory.SW.SdTuples.sdW_coord <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_mean_value_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Measurable Φ → Integrable Φ (thetaMeas σ J μ 𝓕 S) → meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaMean.mean_thetaS_eq_integral | exact GlobalTheory.CompanionTheory.SW.ThetaMean.mean_thetaS_eq_integral | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaMean.mean_thetaS_eq_integral <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TopDens

theorem rescale_tprod {ι : Type} (a : ℝ≥0) (r : ι → ℝ≥0) (h1 : ∀ᶠ v in Filter.cofinite, r v = 1)
    (h2 : a * ∏ᶠ v, r v = 1) (y : ℂ) (x : ι → ℂ) (hx : Multipliable x) :
    Multipliable (fun v => r v • x v) ∧ (a • y) * ∏' v, r v • x v = y * ∏' v, x v := by
  have hfin : (Function.mulSupport r).Finite := by
    simpa [Filter.eventually_cofinite, Function.mulSupport] using h1
  let φ : ℝ≥0 →* ℂ := (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom
  have hφ : ∀ t : ℝ≥0, φ t = ((t : ℝ) : ℂ) := fun _ => rfl
  have hs : ∀ (t : ℝ≥0) (z : ℂ), t • z = φ t * z := by
    intro t z
    rw [hφ, NNReal.smul_def, Complex.real_smul]
  have hfin' : (Function.mulSupport fun v => φ (r v)).Finite := by
    refine hfin.subset ?_
    intro v hv hv'
    exact hv (by simp [hv'])
  have hm : Multipliable fun v => φ (r v) := multipliable_of_hasFiniteMulSupport hfin'
  simp only [hs]
  refine ⟨hm.mul hx, ?_⟩
  rw [hm.tprod_mul hx, tprod_eq_finprod hfin', ← φ.map_finprod hfin]
  calc φ a * y * (φ (∏ᶠ v, r v) * ∏' v, x v) = φ (a * ∏ᶠ v, r v) * (y * ∏' v, x v) := by
        rw [map_mul]; ring
    _ = _ := by rw [h2, map_one, one_mul]

theorem siegelDensities (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    SiegelDensities F E σ M J := by
  intro n hn T hT hdet d b Φ Φinf Φf Φv hc _ hsm hpure hprod
  have hfv : FinVol F E σ M J := GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M J hJ
  refine ⟨hfv.1, fun μ hμ => ⟨(hfv.2 μ hμ).1, fun 𝓕 h𝓕 =>
    ⟨GlobalTheory.CompanionTheory.SW.CharEx.exists_isCharAF F, fun ψ hψ => ?_⟩⟩⟩
  obtain ⟨⟨laminf, hli⟩, hlv⟩ := GlobalTheory.T.exists_standard_local_measures F
  choose lam hlam using hlv
  obtain ⟨ci, c, hc1, hWi, hWv⟩ := GlobalTheory.T.exists_unit_scaling_selfdual_adelic_measures F E σ hCM M J hJ d b laminf lam hli hlam ψ hψ n
  obtain ⟨ei, e, he1, hHi, hHv⟩ := GlobalTheory.T.exists_unit_scaling_selfdual_herm_measures F E σ hCM d b laminf lam hli hlam ψ hψ n
  obtain ⟨hci0, hc0, -, -, hdiv, -⟩ := GlobalTheory.T.unit_product_closure_properties F ci ei c e hc1 he1
  obtain ⟨hei0, he0, -⟩ := GlobalTheory.T.unit_product_closure_properties F ei ci e c he1 hc1
  refine ⟨⟨_, (hWi _).2 rfl⟩, fun μinf hμinf => ⟨⟨_, (hHi _).2 rfl⟩, fun νinf hνinf =>
    ⟨⟨_, fun v => (hWv v _).2 rfl⟩, fun μv hμv => ⟨⟨_, fun v => (hHv v _).2 rfl⟩, fun νv hνv => ?_⟩⟩⟩⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v : HeightOneSpectrum (𝓞 F), IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  have key : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R],
      IsLocR R → ∀ l : Measure R, l.IsAddHaarMeasure →
      ∃ m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E),
        IsGramFib R σ J n (coordW R b l n M) (coordHerm R σ b l n) m ∧ (∀ S, IsLocallyFiniteMeasure (m S)) ∧
        ∀ (a a' : ℝ≥0), a ≠ 0 → a' ≠ 0 → (a • coordW R b l n M).IsAddHaarMeasure →
          (a' • coordHerm R σ b l n).IsAddHaarMeasure →
          ∀ φ : (Fin n → Fin M → R ⊗[F] E) → ℂ, Continuous φ → HasCompactSupport φ →
          IsContDensityOn (a • coordW R b l n M) (gramR R σ J) Subtype.val (a' • coordHerm R σ b l n)
            {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} φ
            (fun S => (a / a') • ∫ X, φ X ∂(m S)) := by
    intro R _ _ _ _ _ hR l hl
    obtain ⟨i1, i2, i3, i4, -⟩ := id hR
    obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b l hl
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M J hJ R hR n _ _ (hW n M) (hH n)
    refine ⟨m, hm, fun S => (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ R hR n _ _ m (hW n M) (hH n) hm S).1, ?_⟩
    intro a a' ha ha' h1 h2 φ hφ hφc
    have h3 := GlobalTheory.T.gram_fiber_measures_scaling F E σ hCM M J hJ R hR n _ _ m (hW n M) (hH n) hm a a' ha ha'
    have h4 := (GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ hCM M J hJ R hR n _ _ _ h1 h2 h3 φ hφ hφc).1
    simpa only [integral_smul_nnreal_measure] using h4
  obtain ⟨minf, hmi, hfi, hdi⟩ := key (Ainf F) hLi laminf hli.1
  choose m hm hf hd using fun v => key (Fv F v) (hLv v) (lam v) (hlam v).1
  have e1 := (hWi μinf).1 hμinf
  have e2 := (hHi νinf).1 hνinf
  have e3 := fun v => (hWv v (μv v)).1 (hμv v)
  have e4 := fun v => (hHv v (νv v)).1 (hνv v)
  have hnM : n = 0 ∨ n + 2 ≤ M := by omega
  have hE := GlobalTheory.T.siegel_weil_measure_of_rank_small_or_zero F E σ hCM n M J hJ hnM T hT hdet d b laminf lam hli hlam μ 𝓕 hμ h𝓕 minf m hmi hm
  obtain ⟨hmeas, hint, hmul, hI⟩ := GlobalTheory.T.integral_pure_tensor_eq_prod_of_isEulerProd F E σ hCM d b n M _ _ _ hE (hfi _) (fun v => hf v _)
    Φ Φinf Φf Φv hc hsm.1 hpure hprod
  have hθ := GlobalTheory.T.siegel_mean_value_integrable F E σ hCM M J hJ μ 𝓕 hμ h𝓕 n _ Φ hmeas hint
  obtain ⟨r1, r2⟩ := rescale_tprod (ci / ei) (fun v => c v / e v) hdiv.1 hdiv.2
    (∫ X, Φinf X ∂(minf (hermOf (Ainf F) σ T hT))) _ hmul
  refine ⟨fun S => (ci / ei) • ∫ X, Φinf X ∂(minf S), fun v S => (c v / e v) • ∫ X, Φv v X ∂(m v S),
    ?_, fun v => ?_, r1, ?_⟩
  · have := hdi ci ei hci0 hei0 (e1 ▸ hμinf.1) (e2 ▸ hνinf.1) Φinf hc hsm.1
    rwa [← e1, ← e2] at this
  · have := hd v (c v) (e v) (hc0 v) (he0 v) (e3 v ▸ (hμv v).1) (e4 v ▸ (hνv v).1) (Φv v)
      (hpure.1 v).1.continuous (hpure.1 v).2
    rwa [← e3 v, ← e4 v] at this
  · rw [hθ, hI]
    exact r2.symm

end GlobalTheory.CompanionTheory.SW.TopDens
end
