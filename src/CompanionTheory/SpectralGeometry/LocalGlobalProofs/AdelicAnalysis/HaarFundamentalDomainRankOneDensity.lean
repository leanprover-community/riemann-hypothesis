import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import CompanionTheory.AutomorphicTheory.ThetaDilations.BoundedA
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasisStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalProductGramFiberRankOneStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SymmetricInvertibleExistsPosdefCongruence
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGramFiberContinuousDensity
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsFiniteAdeleHaarNormalized
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscreteStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodular
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodularStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
import BuildAid.ForwardExisting
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuplesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdelicLatticeMembershipIff
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianContinuousRapidDecay
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaIntegralOverCoordinates
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureNonzeroVectorsBound
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteComponentCoordinatesActionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableFiniteLevelLatticeSet
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateBijectionTraceForm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanLocalDensityFormula

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.Core

theorem core_estimate : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 3 ≤ M → ∀ (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∀ (ρ : InfinitePlace F → (F →+* ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (Pm : InfinitePlace F → Matrix ι ι ℝ), (∀ w, (Pm w).PosDef) → (∀ w, Pm w * (B.map (ρ w))⁻¹ * Pm w = B.map (ρ w)) → ∀ [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (lf : Measure (FiniteAdeleRing (𝓞 F) F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ginf : Ω → InfinitePlace F → Matrix ι ι ℝ) (gf : Ω → Matrix ι ι (FiniteAdeleRing (𝓞 F) F)), (∀ w i j, Measurable fun ω => ginf ω w i j) → (∀ i j, Measurable fun ω => gf ω i j) → (∀ ω w, (ginf ω w)ᵀ * B.map (ρ w) * ginf ω w = B.map (ρ w)) → (∀ ω, (gf ω)ᵀ * B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) * gf ω = B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) → (∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F | (∀ i v, ((N : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂Pr ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))) → ∃ (C : ℝ) (Df : ℕ → FiniteAdeleRing (𝓞 F) F → ℝ) (Dinf : (InfinitePlace F → ℝ) → ℝ), (∀ a : ℕ, 0 < a → Continuous (Df a) ∧ (∀ y, 0 ≤ Df a y) ∧ ∀ U : Set (FiniteAdeleRing (𝓞 F) F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (FiniteAdeleRing (𝓞 F) F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ x)) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df a y) ∂lf) ∧ (Continuous Dinf ∧ (∀ y, 0 ≤ Dinf y) ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) ∧ ∀ a : ℕ, 0 < a → ∀ β : F, β ≠ 0 → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : ι → F | ∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂Pr = (I : ℝ≥0∞) ∧ |(I : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Df a (algebraMap F (FiniteAdeleRing (𝓞 F) F) β) * Dinf (fun w => ρ w β)| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.core

end GlobalTheory.CompanionTheory.SW.Core
end

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_majorant_gaussian : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 3 ≤ M → ∀ (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∀ (ρ : InfinitePlace F → (F →+* ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (Pm : InfinitePlace F → Matrix ι ι ℝ), (∀ w, (Pm w).PosDef) → (∀ w, Pm w * (B.map (ρ w))⁻¹ * Pm w = B.map (ρ w)) → ∀ [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (lf : Measure (FiniteAdeleRing (𝓞 F) F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ginf : Ω → InfinitePlace F → Matrix ι ι ℝ) (gf : Ω → Matrix ι ι (FiniteAdeleRing (𝓞 F) F)), (∀ w i j, Measurable fun ω => ginf ω w i j) → (∀ i j, Measurable fun ω => gf ω i j) → (∀ ω w, (ginf ω w)ᵀ * B.map (ρ w) * ginf ω w = B.map (ρ w)) → (∀ ω, (gf ω)ᵀ * B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) * gf ω = B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) → (∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F | (∀ i v, ((N : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂Pr ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))) → ∃ (C : ℝ) (Df : ℕ → FiniteAdeleRing (𝓞 F) F → ℝ) (Dinf : (InfinitePlace F → ℝ) → ℝ), (∀ a : ℕ, 0 < a → Continuous (Df a) ∧ (∀ y, 0 ≤ Df a y) ∧ ∀ U : Set (FiniteAdeleRing (𝓞 F) F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (FiniteAdeleRing (𝓞 F) F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ x)) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df a y) ∂lf) ∧ (Continuous Dinf ∧ (∀ y, 0 ≤ Dinf y) ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) ∧ ∀ a : ℕ, 0 < a → ∀ β : F, β ≠ 0 → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : ι → F | ∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂Pr = (I : ℝ≥0∞) ∧ |(I : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Df a (algebraMap F (FiniteAdeleRing (𝓞 F) F) β) * Dinf (fun w => ρ w β)| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.Core.core_estimate
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_adele_haar_normalized : ∀ (F : Type) [Field F] [NumberField F], ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧ lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 := by
  first | exact @GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one | exact GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one | (intros; apply GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one <;> assumption)
end

section
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem isProbabilityMeasure_prH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsProbabilityMeasure (prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ μ 𝓕 hμ h𝓕
  have hfin : μ 𝓕 < ⊤ := ((GlobalTheory.T.unitary_group_finite_volume F E σ hσ M J hJ).2 μ hμ).2 𝓕 h𝓕
  obtain ⟨hlc, hsc, ht2⟩ := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).1
  obtain ⟨htg, hlcH, hscH, ht2H, hbor, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have hcount : Countable (HFinIn (AF F) σ J) := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hσ M J hJ).1
  have hne : μ 𝓕 ≠ 0 :=
    (@GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain (HA (AF F) σ J) _ _ htg ht2H hlcH hscH _ hbor
      (HFinIn (AF F) σ J) hcount μ hμ 𝓕 h𝓕 hfin).1
  refine ⟨?_⟩
  simp only [prH, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hne hfin.ne

end GlobalTheory.CompanionTheory.SW.BB
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_probability_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsProbabilityMeasure (prH μ 𝓕) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.BB.isProbabilityMeasure_prH
end

section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB

theorem continuous_gmat_entry {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (p q : Fin M × Fin d) :
    Continuous fun h : HA R σ J => gmat R σ J b h p q := by
  classical
  have hact := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ R).2.2.2.2.2 1).1
  have hco : IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k :=
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R).2.2.2.2.2.2.1 d b
  let X : Fin 1 → Fin M → R ⊗[F] E := fun _ => Pi.single q.1 (inclR R (b q.2))
  have h1 : Continuous fun h : HA R σ J => actW R σ J h X :=
    hact.comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous fun h : HA R σ J => actW R σ J h X 0 p.1 :=
    (continuous_apply p.1).comp ((continuous_apply (0 : Fin 1)).comp h1)
  have h3 : Continuous fun h : HA R σ J =>
      (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2 :=
    (continuous_apply p.2).comp (hco.continuous.comp h2)
  refine h3.congr fun h => ?_
  simp [gmat, actW, actTup, X, Matrix.mulVec_single]

theorem ginf_gfin_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ w p q, Measurable fun ω => ginf e σ J b ω w p q) ∧ (∀ p q, Measurable fun ω => gfin σ J b ω p q) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b e he
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨htg, -, -, -, hbor, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have hinv : ∀ p q, Continuous fun ω : HA (AF F) σ J => gmat (AF F) σ J b ω⁻¹ p q := fun p q =>
    (continuous_gmat_entry σ hσ J hJ b (AF F) p q).comp continuous_inv
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  refine ⟨fun w p q => ?_, fun p q => ?_⟩
  · have hf : Continuous fun t : AF F => e (fstA F t) w :=
      (continuous_apply w).comp (he.continuous.comp continuous_fst)
    exact (hf.comp (hinv p q)).measurable
  · have hf : Continuous fun t : AF F => sndA F t := continuous_snd
    exact (hf.comp (hinv p q)).measurable

end GlobalTheory.CompanionTheory.SW.BB
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_coordinates_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ w p q, Measurable fun ω => ginf e σ J b ω w p q) ∧ (∀ p q, Measurable fun ω => gfin σ J b ω p q) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem isometry_map_ringHom {ι R S K : Type} [Fintype ι] [CommRing R] [CommRing S] [CommRing K]
    (φ : R →+* S) (α : K →+* R) (ψ : K →+* S) (hφ : ∀ x, φ (α x) = ψ x)
    (A : Matrix ι ι R) (B : Matrix ι ι K)
    (h : Aᵀ * B.map α * A = B.map α) :
    (A.map φ)ᵀ * B.map ψ * A.map φ = B.map ψ := by
  have hB : B.map ψ = (B.map α).map φ := by
    ext i j
    simp [hφ]
  have := congrArg (fun X => X.map φ) h
  simp only [Matrix.map_mul] at this
  rw [hB, ← Matrix.transpose_map]
  simpa using this

theorem ginf_gfin_isometry (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x)
    (hB : ∀ h : HA (AF F) σ J, (gmat (AF F) σ J b h)ᵀ * B.map (algebraMap F (AF F)) *
      gmat (AF F) σ J b h = B.map (algebraMap F (AF F))) :
    (∀ ω w, (ginf e σ J b ω w)ᵀ * B.map (ρ w) * ginf e σ J b ω w = B.map (ρ w)) ∧
      ∀ ω, (gfin σ J b ω)ᵀ * B.map (algebraMap F (Af F)) * gfin σ J b ω =
        B.map (algebraMap F (Af F)) := by
  refine ⟨fun ω w => ?_, fun ω => ?_⟩
  · exact isometry_map_ringHom
      ((Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp
        ((e : Ainf F →+* (InfinitePlace F → ℝ)).comp (fstA F : AF F →+* Ainf F)))
      (algebraMap F (AF F)) (ρ w)
      (fun x => by
        have h1 : fstA F (algebraMap F (AF F) x) = algebraMap F (Ainf F) x :=
          (fstA F).commutes x
        simpa [h1] using he x w)
      (gmat (AF F) σ J b ω⁻¹) B (hB ω⁻¹)
  · exact isometry_map_ringHom (sndA F : AF F →+* Af F)
      (algebraMap F (AF F)) (algebraMap F (Af F))
      (fun x => (sndA F).commutes x)
      (gmat (AF F) σ J b ω⁻¹) B (hB ω⁻¹)

end GlobalTheory.CompanionTheory.SW.BB
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_form_invariance_under_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ h : HA (AF F) σ J, (gmat (AF F) σ J b h)ᵀ * B.map (algebraMap F (AF F)) * gmat (AF F) σ J b h = B.map (algebraMap F (AF F))) → (∀ ω w, (ginf e σ J b ω w)ᵀ * B.map (ρ w) * ginf e σ J b ω w = B.map (ρ w)) ∧ ∀ ω, (gfin σ J b ω)ᵀ * B.map (algebraMap F (Af F)) * gfin σ J b ω = B.map (algebraMap F (Af F)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

theorem finDensity_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Af F ⊗[F] E, Algebra.trace (Af F) (Af F ⊗[F] E) (hR (Af F) σ J x y) = cv (Af F) b x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ cv (Af F) b y)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → ∀ (a : ℕ) (U : Set (Af F)), coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = (Measure.pi fun _ : Fin M × Fin d => lf) {x | (∀ i v, ((a : Af F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (Af F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ x)) ∈ U} := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b B hB lf hlf a U
  obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  obtain ⟨-, hme, hmap⟩ := GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hCM (Af F) d b lf hlf M
  rw [← hmap, hme.map_apply]
  congr 1
  ext X
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hl := GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b a X
  have ht : gramR (Af F) σ J X 0 0 = hR (Af F) σ J (X 0) (X 0) := rfl
  rw [ht, hB, ← hl]

end GlobalTheory.CompanionTheory.SW.BB
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_trace_form_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Af F ⊗[F] E, Algebra.trace (Af F) (Af F ⊗[F] E) (hR (Af F) σ J x y) = cv (Af F) b x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ cv (Af F) b y)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → ∀ (a : ℕ) (U : Set (Af F)), coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = (Measure.pi fun _ : Fin M × Fin d => lf) {x | (∀ i v, ((a : Af F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (Af F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ x)) ∈ U} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.BB.finDensity_coord
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.ScalTrace

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem hermScal_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (s : R) :
    (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = algebraMap R (R ⊗[F] E) s := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem trace_det : ∀ (F E : Type) [Field F] [Field E] [Algebra F E], (1 / 2 : F) ≠ 0 → Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (β : F), algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = algebraMap F R β ∧ (β ≠ 0 → IsUnit ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det) := by
  intro F E _ _ _ h2 hf σ R _ _ β
  have hfin : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hf
  have hent := hermScal_entry σ R (algebraMap F R β)
  refine ⟨?_, fun hβ => ?_⟩
  · rw [hent, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) (algebraMap F R β)]
    have h20 : (2 : F) ≠ 0 := by
      intro h
      apply h2
      simp [h]
    have hhalf : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
      rw [← map_mul, one_div, inv_mul_cancel₀ h20, map_one]
    rw [Fintype.card_fin, nsmul_eq_mul]
    have h2R : ((2 : ℕ) : R) = algebraMap F R 2 := by
      rw [map_ofNat]
      norm_num
    rw [h2R, ← mul_assoc, hhalf, one_mul]
  · rw [Matrix.det_fin_one, hent]
    exact ((isUnit_iff_ne_zero.2 hβ).map (algebraMap F R)).map (algebraMap R (R ⊗[F] E))

end GlobalTheory.CompanionTheory.SW.BB.ScalTrace
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_hermitian_trace_and_unit : ∀ (F E : Type) [Field F] [Field E] [Algebra F E], (1 / 2 : F) ≠ 0 → Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (β : F), algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = algebraMap F R β ∧ (β ≠ 0 → IsUnit ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.BB.ScalTrace.trace_det
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.CountHyp

theorem size_eq_sum {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M d : ℕ} (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ y w, |e y w| = ‖y w‖) (X : Fin 1 → Fin M → Ainf F ⊗[F] E) :
    sizeTup b X = ∑ w, ∑ p, |xw e b X w p| := by
  simp only [sizeTup, sizeInf, xw, cv, he, Fintype.sum_prod_type, Fin.sum_univ_one]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem size_le {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M d : ℕ} (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ y w, |e y w| = ‖y w‖) (X : Fin 1 → Fin M → Ainf F ⊗[F] E) {R : ℝ} (hR : 0 < R)
    (h : ∀ w, ‖xw e b X w‖ ≤ R) :
    sizeTup b X ≤ ((M * d * Fintype.card (InfinitePlace F) + 1 : ℕ) : ℝ) * R := by
  rw [size_eq_sum b e he]
  have h1 : ∀ w, ∑ p, |xw e b X w p| ≤ ((M * d : ℕ) : ℝ) * R := by
    intro w
    calc ∑ p, |xw e b X w p| ≤ ∑ _p : Fin M × Fin d, R :=
          Finset.sum_le_sum fun p _ => (norm_le_pi_norm (xw e b X w) p).trans (h w)
      _ = ((M * d : ℕ) : ℝ) * R := by simp
  calc ∑ w, ∑ p, |xw e b X w p| ≤ ∑ _w : InfinitePlace F, ((M * d : ℕ) : ℝ) * R :=
        Finset.sum_le_sum fun w _ => h1 w
    _ = ((M * d * Fintype.card (InfinitePlace F) : ℕ) : ℝ) * R := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hR.le
        push_cast
        linarith

theorem ofF_ne_zero_iff {F E : Type} [Field F] [Field E] [Algebra F E] {M d : ℕ}
    (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) : ofF b x ≠ 0 ↔ x ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · funext ⟨i, k⟩
    have h1 : ∑ k, x (i, k) • b k = 0 := congrFun (congrFun h 0) i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent (fun k => x (i, k)) h1 k
  · subst h
    funext a i
    simp [ofF]

theorem real_bound {C₀ c R : ℝ} (hc : 1 ≤ c) (hR : 0 < R) (a b : ℕ) :
    C₀ * ((c * R) ^ a + (c * R) ^ b) ≤ (|C₀| * (c ^ a + c ^ b)) * (R ^ a + R ^ b) := by
  have hc0 : 0 < c := by linarith
  have ha : 0 < c ^ a := by positivity
  have hb : 0 < c ^ b := by positivity
  have hRa : 0 < R ^ a := by positivity
  have hRb : 0 < R ^ b := by positivity
  have h1 : C₀ * ((c * R) ^ a + (c * R) ^ b) ≤ |C₀| * ((c * R) ^ a + (c * R) ^ b) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  refine h1.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [mul_pow, mul_pow]
  nlinarith [mul_pos ha hRb, mul_pos hb hRa]

theorem main_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ y w, |e y w| = ‖y w‖) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // x ≠ 0}, Set.indicator {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂(prH μ 𝓕) ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b ρ e hom hρ he μ 𝓕 hμ hF N hN
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.theta_measure_nonzero_vectors_bound F E σ hCM M J hJ hM d b μ 𝓕 hμ hF N hN
  set c : ℕ := M * d * Fintype.card (InfinitePlace F) + 1 with hc
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by
    have : 1 ≤ c := by omega
    exact_mod_cast this
  set a := Module.finrank ℚ F * M with ha
  set a2 := 2 * Module.finrank ℚ F * M with ha2
  refine ⟨|C₀| * ((c : ℝ) ^ a + (c : ℝ) ^ a2), fun R hR => ?_⟩

  set S : Set (Fin 1 → Fin M → AF F ⊗[F] E) :=
    {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧
      sizeTup b (projInf X) ≤ c * R} with hS
  have hmeasSize : Measurable fun X : Fin 1 → Fin M → AF F ⊗[F] E => sizeTup b (projInf X) := by
    obtain ⟨hp, -, -, -, -, -, -, -, hs⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hCM d b 1 1
    have hcont : Continuous fun y : AF F ⊗[F] E =>
        sizeInf b (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) := by
      have h := hs.comp (hp.comp (continuous_pi fun _ : Fin 1 => continuous_pi fun _ : Fin 1 =>
        (continuous_id : Continuous fun y : AF F ⊗[F] E => y)))
      simpa [Function.comp_def, sizeTup, projInf] using h
    haveI : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
    have hm := hcont.measurable
    unfold sizeTup projInf
    refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun i _ => ?_
    exact hm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hmeasS : MeasurableSet S :=
    (GlobalTheory.T.measurable_finite_level_lattice_set F E σ hCM d M b N).inter (measurableSet_le hmeasSize measurable_const)
  have hpull := GlobalTheory.T.theta_integral_over_coordinates F E σ hCM M J hJ d b μ 𝓕 hμ hF
    {x : Fin M × Fin d → F | x ≠ 0} {X : Fin 1 → Fin M → E | X ≠ 0}
    (fun x => ofF_ne_zero_iff b x) (S.indicator fun _ => (1 : ℝ≥0∞))
    (measurable_const.indicator hmeasS)
  rw [lintegral_indicator_const hmeasS, one_mul] at hpull
  have hpt : ∀ (ω : HA (AF F) σ J) (x : {x : Fin M × Fin d → F // x ≠ 0}),
      Set.indicator {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ≤
      S.indicator (fun _ => (1 : ℝ≥0∞)) (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) := by
    intro ω x
    by_cases hA : x.1 ∈ {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R}
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.infinite_component_coordinates_action F E σ hCM M J hJ d b ρ e hρ ω x.1
      have hY : actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1)) ∈ S := by
        refine ⟨(GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b N _).2 ?_, size_le b e he _ hR fun w => ?_⟩
        · rw [h2]
          exact hA.1
        · rw [h1 w]
          exact hA.2 w
      rw [Set.indicator_of_mem hA, Set.indicator_of_mem hY]
    · rw [Set.indicator_of_notMem hA]
      exact bot_le
  calc _ ≤ ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // x ≠ 0},
        S.indicator (fun _ => (1 : ℝ≥0∞)) (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) :=
        lintegral_mono fun ω => ENNReal.tsum_le_tsum fun x => hpt ω x
    _ = thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} S := hpull.symm
    _ ≤ ENNReal.ofReal (C₀ * (((c : ℝ) * R) ^ a + ((c : ℝ) * R) ^ a2)) :=
        hC₀ ((c : ℝ) * R) (mul_pos (by linarith) hR)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (real_bound hc1 hR a a2)

end GlobalTheory.CompanionTheory.SW.BB.CountHyp
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_rational_vector_count_ball_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ y w, |e y w| = ‖y w‖) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // x ≠ 0}, Set.indicator {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂(prH μ 𝓕) ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.BB.CountHyp.main_bound
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_bijection_trace_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) ∧ (∀ x : Fin M × Fin d → F, ofF b x ≠ 0 ↔ x ≠ 0) ∧ ∀ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (β : F) (x : Fin M × Fin d → F), gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff | exact GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff | (intros; apply GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.ThetaGauss

theorem continuous_gaussQ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (hom : IsHomeomorph e)
    (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) :
    Continuous (gaussQ e b Pm) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, -, -, -, hco, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  have hxw : ∀ w p, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w p := by
    intro w p
    have h := (hco d b).continuous
    exact (continuous_apply w).comp (hom.continuous.comp ((continuous_apply p.2).comp
      (h.comp ((continuous_apply p.1).comp (continuous_apply 0)))))
  have hxw' : ∀ w, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w := fun w =>
    continuous_pi (hxw w)
  unfold gaussQ
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ => ?_))
  exact (hxw' w).dotProduct (Continuous.matrix_mulVec continuous_const (hxw' w))

theorem lintegral_thetaMeas_gauss : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (a : ℕ), 0 < a → ∀ β : F, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (gaussQ e b Pm (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : Fin M × Fin d → F | ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂(prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b B hB ρ e hom hρ Pm μ 𝓕 hμ h𝓕 a ha β
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨hR, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  haveI := hBor 1 M
  have hA := GlobalTheory.T.measurable_finite_level_lattice_set F E σ hσ d M b a
  have hproj : Continuous (projInf : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    (GlobalTheory.T.adelic_tuple_projections F E σ hσ d b 1 M).1
  have hG : Continuous fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
      ENNReal.ofReal (gaussQ e b Pm (projInf X)) :=
    ENNReal.continuous_ofReal.comp ((continuous_gaussQ σ hσ b e hom Pm).comp hproj)
  rw [← lintegral_indicator hA]
  rw [GlobalTheory.T.theta_integral_over_coordinates F E σ hσ M J hJ d b μ 𝓕 hμ h𝓕
    {x | (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}
    {X | gramE σ J X = fun _ _ => algebraMap F E β}
    (fun x => (GlobalTheory.T.coordinate_bijection_trace_form F E σ hσ M J hJ d b).2.2 B hB β x) _
    (hG.measurable.indicator hA)]
  refine lintegral_congr fun ω => tsum_congr fun x => ?_
  obtain ⟨hinf, hfin⟩ := GlobalTheory.T.infinite_component_coordinates_action F E σ hσ M J hJ d b ρ e hρ ω x.1
  have hmem := GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b a (projFin (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))))
  rw [hfin] at hmem
  have hgauss : gaussQ e b Pm (projInf (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1)))) =
      Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x.1 j)) ⬝ᵥ
        (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x.1 j)))) := by
    simp only [gaussQ, hinf]
  by_cases hx : ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x.1 j)) i) v ∈
      v.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (by exact hmem.2 hx), Set.indicator_of_mem (by exact hx), hgauss]
  · rw [Set.indicator_of_notMem, Set.indicator_of_notMem]
    all_goals first | exact hx | exact fun h => hx (hmem.1 h)

end GlobalTheory.CompanionTheory.SW.BB.ThetaGauss
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_form_rational_theta_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (a : ℕ), 0 < a → ∀ β : F, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (gaussQ e b Pm (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : Fin M × Fin d → F | ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂(prH μ 𝓕) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.lintegral_thetaMeas_gauss | exact GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.lintegral_thetaMeas_gauss | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.lintegral_thetaMeas_gauss <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_local_density_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Ainf F ⊗[F] E, Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) = cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → ∀ Dinf : (InfinitePlace F → ℝ) → ℝ, Continuous Dinf → (∀ y, 0 ≤ Dinf y) → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → Fin M × Fin d → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) → ∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X) ∂(coordW (Ainf F) b laminf 1 M) = ∫⁻ S in U, ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)))) ∂(coordHerm (Ainf F) σ b laminf 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens | exact GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens | (intros; apply GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens <;> assumption)
end

section
section
namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem bound_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ β : F, β ≠ 0 → ∃ (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) (C : ℝ), Continuous φ ∧ (∀ X, 0 < φ X) ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β))) < ⊤ ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (φ (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = (I : ℝ≥0∞) ∧ |(I : ℝ) - (∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β)))).toReal * ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf hminf m hm β hβ
  obtain ⟨hF, hEc, hfin, hconj⟩ := id hCM
  have hd : d = 2 := by
    have h := Module.finrank_eq_card_basis b
    simpa [hfin] using h.symm
  obtain ⟨B, hBs, hBd, hBE, hBR⟩ := GlobalTheory.T.exists_trace_form_gram_matrix_in_basis F E σ hCM M J hJ d b
  obtain ⟨ρ, e, hρ, he, heρ, hen, hem⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF
  have hP : ∀ w, ∃ P : Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ,
      P.PosDef ∧ P * (B.map (ρ w))⁻¹ * P = B.map (ρ w) := by
    intro w
    refine GlobalTheory.T.symmetric_invertible_exists_posdef_congruence _ _ ?_ ?_
    · exact hBs.map _
    · have h := RingHom.map_det (ρ w) B
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero _).2 hBd
  choose Pm hPd hPm using hP
  obtain ⟨lf, hlf, hlf1⟩ := GlobalTheory.T.exists_finite_adele_haar_normalized F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI := GlobalTheory.T.quotient_probability_measure F E σ hCM M J hJ μ 𝓕 hμ h𝓕
  obtain ⟨hgi, hgf⟩ := GlobalTheory.T.gram_coordinates_measurable F E σ hCM M J hJ d b e he
  obtain ⟨hii, hif⟩ := GlobalTheory.T.trace_form_invariance_under_unitary F E σ M J d b B ρ e heρ
    (fun h => ((hBR (AF F)).2 h _ (fun p q => rfl)).1)
  have hcard : Fintype.card (Fin M × Fin d) = 2 * M := by simp [hd, mul_comm]
  obtain ⟨C, Df, Dinf, hDf, ⟨hDc, hD0, hDd⟩, hmain⟩ :=
    GlobalTheory.T.positive_majorant_gaussian F hF (Fin M × Fin d) M hcard hM B hBs hBd ρ hρ Pm hPd hPm lf hlf hlf1
      (HA (AF F) σ J) (prH μ 𝓕) (ginf e σ J b) (gfin σ J b) hgi hgf hii hif
      (fun N hN => GlobalTheory.T.average_rational_vector_count_ball_bound F E σ hCM M J hJ hM d b ρ e he heρ hen μ 𝓕 hμ h𝓕 N hN)
  obtain ⟨hgc, hgr⟩ := GlobalTheory.T.gaussian_continuous_rapid_decay F E σ hCM M d b e he hen Pm
  have h2 : (1 / 2 : F) ≠ 0 := by norm_num
  have hinfint : ∫⁻ X, ENNReal.ofReal (gaussQ e b Pm X)
      ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β))) =
      ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (fun w => ρ w β)) := by
    obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    obtain ⟨hK1, hK2, hK3⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1
    obtain ⟨t1, t2, t3, t4, t5, t6, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
    have hs := GlobalTheory.T.scalar_hermitian_trace_and_unit F E h2 hfin σ (Ainf F) β
    have hDcont : Continuous fun S : HermR (Ainf F) σ 1 =>
        (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) *
          Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))) := by
      refine continuous_const.mul (hDc.comp (he.continuous.comp (continuous_const.mul (t6.comp ?_))))
      exact (continuous_apply_apply 0 0).comp continuous_subtype_val
    have h := GlobalTheory.T.archimedean_gram_fiber_continuous_density F E σ hCM M J hJ d b (coordW (Ainf F) b laminf 1 M)
      (coordHerm (Ainf F) σ b laminf 1) minf (hK2 1 M) (hK3 1) hminf (gaussQ e b Pm) hgc
      (fun X => (Real.exp_pos _).le) (hgr hPd) _ hDcont
      (GlobalTheory.T.archimedean_local_density_formula F E σ hCM M J hJ hM d b B (hBR (Ainf F)).1 ρ e he heρ Pm laminf hinf.1
        (hem laminf hinf) Dinf hDc hD0 hDd) (hermScal (Ainf F) σ (algebraMap F _ β)) (hs.2 hβ)
    rw [h, hs.1]
    have : (e (algebraMap F (Ainf F) β)) = fun w => ρ w β := funext fun w => heρ β w
    rw [this]
  have hκ : 0 ≤ (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (fun w => ρ w β) :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) _) (hD0 _)
  refine ⟨gaussQ e b Pm, C, hgc, fun X => Real.exp_pos _, ?_, ?_⟩
  · rw [hinfint]; exact ENNReal.ofReal_lt_top
  · intro a ha
    obtain ⟨I, hI, hIb⟩ := hmain a ha β hβ
    obtain ⟨c1, c2, c3⟩ := hDf a ha
    have hprod := GlobalTheory.T.global_product_gram_fiber_rank_one F E σ hCM M J hJ d b lam hlam m hm lf hlf hlf1 a ha (Df a) c1 c2
      (fun U hU => by
        rw [GlobalTheory.T.finite_adelic_trace_form_coordinates F E σ hCM M J hJ d b B (hBR (Af F)).1 lf hlf a U]
        exact c3 U hU) β hβ
    refine ⟨I, ?_, ?_⟩
    · rw [GlobalTheory.T.trace_form_rational_theta_identity F E σ hCM M J hJ d b B hBE ρ e he heρ Pm μ 𝓕 hμ h𝓕 a ha β]
      exact hI
    · rw [hinfint, hprod.tprod_eq, ENNReal.toReal_ofReal hκ]
      convert hIb using 3
      ring

end GlobalTheory.CompanionTheory.SW.BB
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMeas_rank_one_sub_density_product_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ β : F, β ≠ 0 → ∃ (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) (C : ℝ), Continuous φ ∧ (∀ X, 0 < φ X) ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β))) < ⊤ ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (φ (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = (I : ℝ≥0∞) ∧ |(I : ℝ) - (∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β)))).toReal * ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.BB.bound_hermitian
end
