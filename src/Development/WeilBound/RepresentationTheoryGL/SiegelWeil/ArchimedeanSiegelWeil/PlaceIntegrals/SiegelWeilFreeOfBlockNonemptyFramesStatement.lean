import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SplitAnisotropic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentTarget
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGram
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeExtendByScalarBlock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeZeroRankOneOfThreeLe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.ZeroBlockCoefficientInductionLeftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPlaneUnfoldingIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneEulerProductMeasureExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductMeasureCovolumeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerVolumeAlmostAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicRankOneGlobalVolume
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContentZetaSeries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorsContentDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIsotropicOrbitOfE0
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingLatticeMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneZeroFibreVolume
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSiegelWeilUnramifiedMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupFiniteProductTailLimitStatement
import Development.WeilBound.CoreStatements.ThetaDilations.ContinuousPm

section
namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
theorem finite_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ p : ℕ, 1 ≤ p → 2 * p < M → ∀ (h₀ : ∀ a b : Fin p, σ ((0 : Matrix (Fin p) (Fin p) E) b a) = (0 : Matrix (Fin p) (Fin p) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ p → Measure (Fin p → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J p (coordW (Fv F v) b lam p M) (coordHerm (Fv F v) σ b lam p) m → m (hermOf (Fv F v) σ (0 : Matrix (Fin p) (Fin p) E) h₀) (latV b v) < ⊤ := by
  intro F E _ _ _ _ _ σ hσ M J hJ p hp hM h₀ d b v lam hlam m hm
  have hL := GlobalTheory.T.contDiffOn_chart_globalWhittakerCoefficient F E σ hσ d b p M v
  exact lt_top_iff_ne_top.2 (GlobalTheory.T.local_siegel_weil_unramified_measure F E σ hσ M J hJ p hp hM d b v lam hlam m hm _ (latV b v) hL.1 hL.2).2.1

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

theorem lintegral_pieces {V ι : Type} [MeasurableSpace V] [Countable ι] (μ : Measure V) (A : ι → Set V)
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A)) (Ψ : V → ℝ≥0∞)
    (κ : ι → ℝ≥0∞) (hv : ∀ i, ∀ y ∈ A i, Ψ y = κ i) (h0 : ∀ᵐ y ∂μ, y ∉ ⋃ i, A i → Ψ y = 0) :
    ∫⁻ y, Ψ y ∂μ = ∑' i, κ i * μ (A i) := by
  have hU : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
  rw [← lintegral_add_compl Ψ hU]
  have h2 : ∫⁻ y in (⋃ i, A i)ᶜ, Ψ y ∂μ = 0 := by
    have : ∫⁻ y in (⋃ i, A i)ᶜ, Ψ y ∂μ = ∫⁻ _ in (⋃ i, A i)ᶜ, 0 ∂μ := by
      refine lintegral_congr_ae ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' hU.compl]
      filter_upwards [h0] with y hy hyc
      exact hy hyc
    simpa using this
  rw [h2, add_zero, lintegral_iUnion hA hd]
  refine tsum_congr fun i => ?_
  rw [setLIntegral_congr_fun (g := fun _ => κ i) (hA i) (fun y hy => hv i y hy), setLIntegral_const]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

theorem hermOf_zero_val (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R]
    [Algebra F R] (p : ℕ) (h : ∀ a b : Fin p, σ ((0 : Matrix (Fin p) (Fin p) E) b a) = (0 : Matrix (Fin p) (Fin p) E) a b) :
    ((hermOf R σ (0 : Matrix (Fin p) (Fin p) E) h : HermR R σ p) : Matrix (Fin p) (Fin p) (R ⊗[F] E)) = 0 := by
  funext i j
  simp [hermOf]

theorem pow_index (a : ℝ≥0) (ha : a ≠ 0) (n N : ℕ) (hn : n ≤ N) :
    (a : ℝ≥0∞) ^ n * ENNReal.ofReal ((((a : ℝ))⁻¹) ^ N) = ENNReal.ofReal ((((a : ℝ))⁻¹) ^ (N - n)) := by
  have hpos : (0 : ℝ) < a := by exact_mod_cast pos_iff_ne_zero.2 ha
  rw [show (a : ℝ≥0∞) ^ n = ENNReal.ofReal ((a : ℝ) ^ n) by
    rw [ENNReal.ofReal_pow hpos.le, ENNReal.ofReal_coe_nnreal],
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, pow_add, inv_pow, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

theorem stageInt_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M n d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) {v : HeightOneSpectrum (𝓞 F)}
    (lam : Measure (Fv F v)) (m' : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : HA (Fv F v) σ (hypOne J))
    (hg : actW (Fv F v) σ (hypOne J) g (e0 _ M) ∉ latV b v) :
    stageInt (Fv F v) σ J b lam m' ((latV b v).indicator 1) g = 0 := by
  have hz : ∀ (Y : Fin n → Fin M → Fv F v ⊗[F] E) (a : Fin 1 → Fin n → Fv F v ⊗[F] E),
      ((latV b v).indicator 1 : (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
        (actW (Fv F v) σ (hypOne J) g (consA a Y)) = 0 := by
    intro Y a
    refine Set.indicator_of_notMem (fun hmem => hg ?_) _
    intro p i k
    have h := hmem 0 i k
    have e : actW (Fv F v) σ (hypOne J) g (e0 _ M) p = actW (Fv F v) σ (hypOne J) g (consA a Y) 0 := rfl
    rw [e]
    exact h
  simp [stageInt, hz]

theorem good_local (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) (hn1 : 1 ≤ n)
    (hnM : 2 * n < M)
    (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b)
    (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b)
    (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b)
    (d : ℕ) (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), IsStdV v lam →
      ∀ (m : HermR (Fv F v) σ (n + 1) → Measure (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E))
        (m₁ : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E))
        (m' : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFibFree (Fv F v) σ (hypOne J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 2)) (coordHerm (Fv F v) σ b lam (n + 1)) m →
      IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b lam 1 (M + 2)) (coordHerm (Fv F v) σ b lam 1) m₁ →
      IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' →
      m (hermOf (Fv F v) σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁) (latV b v) =
          m' (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v) *
            m₁ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v) *
            ENNReal.ofReal (zetaV E v (M + 1 - n)) ∧
        m₁ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) =
          m₁ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v) *
            ENNReal.ofReal (zetaV E v (M + 1)) := by
  have hJ' : IsHermND σ (hypOne J) := (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem F E σ hσ M J hJ).1
  filter_upwards [GlobalTheory.T.local_content_zeta_series F E σ hσ d b, GlobalTheory.T.primitive_vectors_content_decomposition F E σ hσ M J hJ d b] with v hc hp lam hlam m m₁ m' hm hm₁ hm'
  obtain ⟨ι, hι, c, w, hC, hZ⟩ := hc
  obtain ⟨pM, pL, pD, pE⟩ := hp ι c w hC
  obtain ⟨c1, c2, c3, -, -⟩ := hC
  have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨r1, r2, r3, r4, -⟩ := id hloc
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 (M + 2)
  set S₁ := hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ with hS₁
  set P := primV σ J b v with hP
  let A : ι → Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) := fun i => {y | ∃ y₀ ∈ P, y = scalT (c i) y₀}
  haveI := a8 (n + 1) (M + 2)
  have hlatM : MeasurableSet (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 (M + 2) v).2.1.measurableSet
  have hlatM' : MeasurableSet (latV b v : Set (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b (n + 1) (M + 2) v).2.1.measurableSet

  have hinv : ∀ i, ∃ u : Fv F v ⊗[F] E, u * c i = 1 := fun i => by
    obtain ⟨x, hx⟩ := (c1 i).1
    exact ⟨(x⁻¹ : (Fv F v ⊗[F] E)ˣ), by rw [← hx]; exact x.inv_mul⟩
  choose u hu using hinv
  have hscal : ∀ (x y : Fv F v ⊗[F] E) (z : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E),
      scalT x (scalT y z) = scalT (x * y) z := fun x y z => by
    funext p i
    simp [scalT, mul_assoc]
  have hone : ∀ z : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, scalT (1 : Fv F v ⊗[F] E) z = z := fun z => by
    funext p i
    simp [scalT]
  have hAset : ∀ i, A i = (scalT (u i)) ⁻¹' P := fun i => by
    ext y
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      show scalT (u i) (scalT (c i) y₀) ∈ P
      rw [hscal, hu, hone]
      exact hy₀
    · intro hy
      refine ⟨scalT (u i) y, hy, ?_⟩
      rw [hscal, mul_comm, hu, hone]
  have hcont : ∀ x : Fv F v ⊗[F] E, Continuous (scalT x : (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → _) := fun x =>
    continuous_pi fun p => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply p))
  have hAm : ∀ i, MeasurableSet (A i) := fun i => by
    rw [hAset]
    exact (hcont (u i)).measurable pM
  have hAd : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro y ⟨y₀, hy₀, rfl⟩ ⟨y₁, hy₁, he⟩
    exact hij (pD i j y₀ hy₀ y₁ hy₁ he)
  have hfree : ∀ᵐ y ∂(m₁ S₁), LinearIndependent (Fv F v ⊗[F] E) y ∧ gramR (Fv F v) σ (hypOne J) y = 0 := by
    have h := hm₁.1 S₁
    have h2 := compl_mem_ae_iff.2 h
    rw [compl_compl] at h2
    filter_upwards [h2] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨hy2, ?_⟩
    have h3 : gramR (Fv F v) σ (hypOne J) y = ((S₁ : HermR (Fv F v) σ 1) : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) := hy1
    rw [h3, hS₁, hermOf_zero_val]
  have hlatE : ∀ᵐ y ∂(m₁ S₁), y ∉ ⋃ i, A i → y ∉ latV b v := by
    filter_upwards [hfree] with y hy hyA hyl
    obtain ⟨i, y₀, hy₀, he⟩ := pE y hy.1 hy.2 hyl
    exact hyA (Set.mem_iUnion.2 ⟨i, y₀, hy₀, he⟩)
  have hAl : ∀ i, ∀ y ∈ A i, y ∈ latV b v := by
    rintro i y ⟨y₀, hy₀, rfl⟩
    exact pL i y₀ hy₀

  have e1 : m₁ S₁ (latV b v) = ∑' i, m₁ S₁ (A i) := by
    have h := lintegral_pieces (m₁ S₁) A hAm hAd ((latV b v).indicator 1) (fun _ => 1)
      (fun i y hy => by simp [Set.indicator_of_mem (hAl i y hy)])
      (by
        filter_upwards [hlatE] with y hy hyA
        simp [Set.indicator_of_notMem (hy hyA)])
    rw [lintegral_indicator_one hlatM] at h
    simpa using h

  have e2 : ∀ i, m₁ S₁ (A i) = m₁ S₁ P * ENNReal.ofReal ((((qv v ^ w i : ℝ≥0) : ℝ)⁻¹) ^ (M + 1)) := by
    intro i
    obtain ⟨t, ht1, ht2⟩ := c3 i
    have hq0 : qv v ≠ 0 := by
      intro h0
      have : Ideal.absNorm v.asIdeal = 0 := by simpa [qv] using h0
      exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 this)
    have ha : qv v ^ w i ≠ 0 := pow_ne_zero _ hq0
    have hs := GlobalTheory.T.local_rank_one_zero_fibre_volume F E σ hσ (M + 2) (hypOne J) hJ' (by omega) h₂ d b v lam hlam m₁ hm₁ (c i) (qv v ^ w i) t
      (c1 i).1 ha (c2 i lam hlam) ht1 (by rw [ht2]; push_cast; rfl) (A i) (hAm i)
    have hset : {y | scalT (c i) y ∈ A i} = P := by
      ext y
      constructor
      · rintro ⟨y₀, hy₀, he⟩
        have : scalT (u i) (scalT (c i) y) = scalT (u i) (scalT (c i) y₀) := by rw [he]
        rw [hscal, hscal, hu, hone, hone] at this
        exact this ▸ hy₀
      · intro hy
        exact ⟨y, hy, rfl⟩
    rw [hset] at hs
    have hpos : (0 : ℝ) < ((qv v ^ w i : ℝ≥0) : ℝ) := by exact_mod_cast pos_iff_ne_zero.2 ha
    have hN : M + 2 - 1 = M + 1 := by omega
    rw [hN] at hs
    rw [hs, mul_comm ((((qv v ^ w i : ℝ≥0) : ℝ≥0∞)) ^ (M + 1)), mul_assoc]
    have hmul : ((((qv v ^ w i : ℝ≥0) : ℝ≥0∞)) ^ (M + 1)) * ENNReal.ofReal ((((qv v ^ w i : ℝ≥0) : ℝ)⁻¹) ^ (M + 1)) = 1 := by
      have := pow_index (qv v ^ w i) ha (M + 1) (M + 1) le_rfl
      simpa using this
    rw [hmul, mul_one]
  have hr : ∀ i, (((qv v ^ w i : ℝ≥0) : ℝ)⁻¹) = ((qv v : ℝ) ^ w i)⁻¹ := fun i => by push_cast; rfl
  have hsum : ∀ s : ℕ, 1 ≤ s → ∑' i, ENNReal.ofReal ((((qv v ^ w i : ℝ≥0) : ℝ)⁻¹) ^ s) = ENNReal.ofReal (zetaV E v s) := by
    intro s hs
    have h := hZ s hs
    simp only [hr]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) h.summable, h.tsum_eq]
  refine ⟨?_, ?_⟩
  · obtain ⟨Ψ, hΨm, hΨ, hint⟩ := GlobalTheory.T.zero_block_coefficient_induction_left F E σ hσ M J hJ n hn1 hnM h₀ h₁ h₂ (Fv F v) hloc d b lam hlam.1 m m₁ m'
      hm hm₁ hm' ((latV b v).indicator 1) (measurable_one.indicator hlatM')
    rw [lintegral_indicator_one hlatM'] at hint
    set L' := m' (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v) with hL'
    have hval : ∀ i, ∀ y ∈ A i, Ψ y = (((qv v ^ w i : ℝ≥0) : ℝ≥0∞)) ^ n * L' := by
      rintro i y ⟨y₀, hy₀, rfl⟩
      obtain ⟨g, hg1, hg2⟩ := GlobalTheory.T.local_unit_scaling_lattice_measure F E σ hσ M J hJ n d b v lam hlam
        (m' (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀)) (c i) (qv v ^ w i) (c1 i).1 (c1 i).2
        (c2 i lam hlam) y₀ hy₀
      rw [← hg1, hΨ g, hg2]
    have hz : ∀ᵐ y ∂(m₁ S₁), y ∉ ⋃ i, A i → Ψ y = 0 := by
      filter_upwards [hfree, hlatE] with y hy hl hyA
      obtain ⟨g, rfl⟩ := GlobalTheory.T.local_isotropic_orbit_of_e0 F E σ hσ M J hJ v y hy.1 hy.2
      rw [hΨ g]
      exact stageInt_zero σ J b lam _ g (hl hyA)
    rw [hint, lintegral_pieces (m₁ S₁) A hAm hAd Ψ _ hval hz]
    have hterm : ∀ i, (((qv v ^ w i : ℝ≥0) : ℝ≥0∞)) ^ n * L' * m₁ S₁ (A i) =
        L' * m₁ S₁ P * ENNReal.ofReal ((((qv v ^ w i : ℝ≥0) : ℝ)⁻¹) ^ (M + 1 - n)) := by
      intro i
      have hq0 : qv v ^ w i ≠ 0 := by
        refine pow_ne_zero _ fun h0 => ?_
        have : Ideal.absNorm v.asIdeal = 0 := by simpa [qv] using h0
        exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 this)
      rw [e2, ← pow_index (qv v ^ w i) hq0 n (M + 1) (by omega)]
      ring
    simp only [hterm]
    rw [ENNReal.tsum_mul_left, hsum _ (by omega)]
  · rw [e1]
    simp only [e2]
    rw [ENNReal.tsum_mul_left, hsum _ (by omega)]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

theorem qv_ge_two {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : (2 : ℝ) ≤ (qv v : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  have : (qv v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by simp [qv]
  rw [this]
  exact_mod_cast h2

theorem inv_one_sub_bounds {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 4) :
    1 ≤ (1 - u)⁻¹ ∧ (1 - u)⁻¹ ≤ 1 + 4 * u ∧ 1 ≤ ((1 - u)⁻¹) ^ 2 ∧ ((1 - u)⁻¹) ^ 2 ≤ 1 + 4 * u := by
  have hp : 0 < 1 - u := by linarith
  have hw : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ hp).2 (by linarith)
  refine ⟨hw, ?_, one_le_pow₀ hw, ?_⟩
  · rw [inv_le_iff_one_le_mul₀ hp]
    nlinarith
  · rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0, mul_nonneg h0 (sub_nonneg.2 h1)]

theorem zetaV_bounds {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (s : ℕ) (hs : 2 ≤ s) :
    1 ≤ zetaV E v s ∧ zetaV E v s ≤ 1 + 4 * (1 / (qv v : ℝ) ^ 2) := by
  have hq := qv_ge_two v
  have hq1 : (1 : ℝ) ≤ (qv v : ℝ) := by linarith
  have hq0 : (0 : ℝ) < (qv v : ℝ) := by linarith
  have hsq : (4 : ℝ) ≤ (qv v : ℝ) ^ 2 := by nlinarith
  have hu : ∀ t : ℕ, 2 ≤ t → ((qv v : ℝ) ^ t)⁻¹ ≤ 1 / (qv v : ℝ) ^ 2 := fun t ht => by
    rw [one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hq1 ht)
  have hq4 : 1 / (qv v : ℝ) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hsq
  unfold zetaV
  split_ifs with hf
  · have h1 := hu (2 * s) (by omega)
    obtain ⟨a, b', -, -⟩ := inv_one_sub_bounds (u := ((qv v : ℝ) ^ (2 * s))⁻¹) (by positivity) (h1.trans hq4)
    exact ⟨a, b'.trans (by linarith)⟩
  · have h1 := hu s hs
    obtain ⟨-, -, a, b'⟩ := inv_one_sub_bounds (u := ((qv v : ℝ) ^ s)⁻¹) (by positivity) (h1.trans hq4)
    exact ⟨a, b'.trans (by linarith)⟩

theorem real_bound {x y p Z₁ Z₂ e : ℝ} (hy : y = p * Z₂) (hp : 0 ≤ p) (h1 : 1 ≤ Z₁) (h1' : Z₁ ≤ 1 + e)
    (h2 : 1 ≤ Z₂) (h2' : Z₂ ≤ 1 + e) (he : e ≤ 1) (hy1 : |y - 1| ≤ 1) :
    |x * p * Z₁ - 1| ≤ 4 * |x - 1| + 2 * e + |y - 1| := by
  have hy2 : y ≤ 2 := by linarith [(abs_le.1 hy1).2]
  have hp2 : p ≤ 2 := by nlinarith
  have hZ : Z₁ ≤ 2 := by linarith
  have e1 : x * p * Z₁ - 1 = (x - 1) * (p * Z₁) + p * (Z₁ - Z₂) + (y - 1) := by rw [hy]; ring
  have b1 : |(x - 1) * (p * Z₁)| ≤ 4 * |x - 1| := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ p * Z₁), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    nlinarith
  have b2 : |p * (Z₁ - Z₂)| ≤ 2 * e := by
    rw [abs_mul, abs_of_nonneg hp]
    have : |Z₁ - Z₂| ≤ e := abs_le.2 ⟨by linarith, by linarith⟩
    exact mul_le_mul hp2 this (abs_nonneg _) (by norm_num)
  rw [e1]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add b1 b2)) le_rfl)

theorem mass_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b) (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b) (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ (n + 1) → Measure (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E)) (m₁ : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) (m' : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) (n + 1) (coordW (Fv F v) b (lam v) (n + 1) (M + 2)) (coordHerm (Fv F v) σ b (lam v) (n + 1)) (m v)) → (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b (lam v) 1 (M + 2)) (coordHerm (Fv F v) σ b (lam v) 1) (m₁ v)) → (∀ v, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m' v)) → (∀ v, m₁ v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) < ⊤) → Summable (fun v => |(m₁ v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v)).toReal - 1|) → (∀ v, m' v (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v) < ⊤) → Summable (fun v => |(m' v (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v)).toReal - 1|) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁) (latV b v) < ⊤) ∧ Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁) (latV b v)).toReal - 1|) := by
  intro F E _ _ _ _ _ σ hσ M J hJ n hn1 hnM h₀ h₁ h₂ d b lam hlam m m₁ m' hm hm₁ hm' fin₁ sum₁ fin' sum'
  have hJ' : IsHermND σ (hypOne J) := (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem F E σ hσ M J hJ).1
  have fin₀ : ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁) (latV b v) < ⊤ := fun v =>
    GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH.finite_lt F E σ hσ (M + 2) (hypOne J) hJ' (n + 1) (by omega) (by omega) h₁ d b v (lam v) (hlam v) (m v) (hm v)
  refine ⟨fin₀, ?_⟩
  have hq : Summable fun v : HeightOneSpectrum (𝓞 F) => 1 / (qv v : ℝ) ^ 2 := by
    have := GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F
    simpa [qv] using this
  have hB : Summable fun v : HeightOneSpectrum (𝓞 F) =>
      4 * |(m' v (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v)).toReal - 1| +
        2 * (4 * (1 / (qv v : ℝ) ^ 2)) +
        |(m₁ v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v)).toReal - 1| :=
    ((sum'.mul_left 4).add ((hq.mul_left 4).mul_left 2)).add sum₁
  have hsmall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      |(m₁ v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v)).toReal - 1| < 1 :=
    sum₁.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  refine Summable.of_norm_bounded_eventually hB ?_
  filter_upwards [good_local F E σ hσ M J hJ n hn1 hnM h₀ h₁ h₂ d b, hsmall] with v hg hs
  obtain ⟨g1, g2⟩ := hg (lam v) (hlam v) (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v)
  obtain ⟨z1, z1'⟩ := zetaV_bounds E v (M + 1 - n) (by omega)
  obtain ⟨z2, z2'⟩ := zetaV_bounds E v (M + 1) (by omega)
  have hq2 := qv_ge_two v
  have he : 4 * (1 / (qv v : ℝ) ^ 2) ≤ 1 := by
    have h4 : (4 : ℝ) ≤ (qv v : ℝ) ^ 2 := by nlinarith
    rw [mul_one_div, div_le_one (by positivity)]
    exact h4
  rw [Real.norm_eq_abs, abs_abs, g1, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith)]
  refine real_bound ?_ ENNReal.toReal_nonneg z1 z1' z2 z2' he hs.le
  rw [g2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
theorem _root_.GlobalTheory.T.zero_block_coefficient_induction_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b) (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b) (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ (n + 1) → Measure (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E)) (m₁ : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) (m' : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) (n + 1) (coordW (Fv F v) b (lam v) (n + 1) (M + 2)) (coordHerm (Fv F v) σ b (lam v) (n + 1)) (m v)) → (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b (lam v) 1 (M + 2)) (coordHerm (Fv F v) σ b (lam v) 1) (m₁ v)) → (∀ v, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m' v)) → (∀ v, m₁ v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) < ⊤) → Summable (fun v => |(m₁ v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v)).toReal - 1|) → (∀ v, m' v (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v) < ⊤) → Summable (fun v => |(m' v (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v)).toReal - 1|) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁) (latV b v) < ⊤) ∧ Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁) (latV b v)).toReal - 1|) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH.mass_isotropic | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH.mass_isotropic
end

section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem lintegral_iSup_places {ι Ω : Type} [Countable ι] [DecidableEq ι] [MeasurableSpace Ω]
    (I : Measure Ω) (S : Finset ι) (term : Finset ι → Ω → ℝ≥0∞) (hm : ∀ S', Measurable (term S'))
    (hmono : ∀ S' S'', S ⊆ S' → S' ⊆ S'' → ∀ y, term S' y ≤ term S'' y) (A : ℝ≥0∞)
    (c : Finset ι → ℝ≥0∞) (hint : ∀ S', S ⊆ S' → ∫⁻ y, term S' y ∂I = A * c S') :
    ∫⁻ y, (⨆ S', term (S ∪ S') y) ∂I = A * ⨆ S', c (S ∪ S') := by
  have hd : Directed (· ≤ ·) (fun S' : Finset ι => term (S ∪ S')) := by
    intro S₁ S₂
    refine ⟨S₁ ∪ S₂, fun y => ?_, fun y => ?_⟩
    · exact hmono _ _ Finset.subset_union_left
        (Finset.union_subset_union_right Finset.subset_union_left) y
    · exact hmono _ _ Finset.subset_union_left
        (Finset.union_subset_union_right Finset.subset_union_right) y
  rw [lintegral_iSup_directed (fun S' => (hm _).aemeasurable) hd, ENNReal.mul_iSup]
  exact iSup_congr fun S' => hint _ Finset.subset_union_left

theorem latV_measurable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  exact (((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2).measurableSet

theorem fam_inf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)) (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ f, IsGramFibFree (Ainf F) σ J n (coordW (Ainf F) b lam n M) (coordHerm (Ainf F) σ b lam n) f := by
  have hB : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) _ b lam hlam
  exact GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hCM M n J hJ _ _ (hW n M) (hH n)

theorem fam_fin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ f, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) f := by
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  have hBv : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) _ b lam hlam
  exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J v n hCM hJ _ _ (hW n M) (hH n)

theorem hyp_step : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b) (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b), (framesE σ J (0 : Matrix (Fin n) (Fin n) E)).Nonempty → SWFree σ J (0 : Matrix (Fin n) (Fin n) E) h₀ → SWFree σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁ := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn hnM h₀ h₁ hne hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  obtain ⟨hJ', he0⟩ := GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ hCM M J hJ
  have h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b :=
    fun a b => by simp
  obtain ⟨m₁inf, hm₁inf⟩ := fam_inf σ hCM (hypOne J) hJ' b laminf hinf.1 1
  obtain ⟨m'inf, hm'inf⟩ := fam_inf σ hCM J hJ b laminf hinf.1 n
  choose m₁ hm₁ using fun v => fam_fin σ hCM (hypOne J) hJ' b v (lam v) (hlam v).1 1
  choose m' hm' using fun v => fam_fin σ hCM J hJ b v (lam v) (hlam v).1 n
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁
  have hE' := hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf m' hm'inf hm'
  have hE₁ := GlobalTheory.T.siegelWeilFree_zero_rank_one_of_three_le F E σ hCM (M + 2) (hypOne J) hJ' (by omega) h₂ ⟨_, he0⟩ d b laminf lam hinf hlam
    μ 𝓕 hμ h𝓕 m₁inf m₁ hm₁inf hm₁
  obtain ⟨hfinL, hsumL⟩ := GlobalTheory.T.zero_block_coefficient_induction_right F E σ hCM M J hJ n hn hnM h₀ h₁ h₂ d b lam hlam m m₁ m' hm hm₁ hm'
    hE₁.1 hE₁.2.1 hE'.1 hE'.2.1
  refine ⟨hfinL, hsumL, ?_⟩
  obtain ⟨dA, hdA, hdAE⟩ := GlobalTheory.T.covolume_one_euler_product_measure_exists F E σ hCM n d b laminf lam hinf hlam
  obtain ⟨hsumP, S₃, hS₃⟩ := GlobalTheory.T.hyperbolic_rank_one_global_volume F E σ hCM M J hJ (by omega) d b laminf lam hinf hlam h₂ m₁inf m₁
    hm₁inf hm₁ _ hE₁
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.euler_product_measure_covolume_one F E σ hCM M J hJ n d b laminf lam hinf hlam dA hdAE _ _ _ hE'
  have hStab := GlobalTheory.T.lattice_stabilizer_volume_almost_all F E σ hCM M J hJ n d b
  refine ⟨S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hStab).toFinset, fun S hS φinf φ hφinf hφ => ?_⟩
  have hS2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have hS3 : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have hS4 : ∀ v, v ∉ S → ∀ lam' : Measure (Fv F v), IsStdV v lam' →
      ∀ (m₀ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : HA (Fv F v) σ (hypOne J)),
      latStab σ (hypOne J) b v g → stageInt (Fv F v) σ J b lam' m₀ ((latV b v).indicator 1) g = m₀ (latV b v) := by
    intro v hv
    by_contra hc
    exact hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inr hc))
  have hlatm : ∀ v, MeasurableSet (latV b v : Set (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    fun v => latV_measurable σ hCM b (n + 1) (M + 2) v
  have stg := GlobalTheory.T.zero_block_coefficient_induction_left F E σ hCM M J hJ n hn hnM h₀ h₁ h₂
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := stg (Ainf F) hLi d b laminf hinf.1 minf m₁inf m'inf hminf hm₁inf
    hm'inf φinf hφinf
  choose Ψ hΨm hΨ1 hΨ2 using fun v => stg (Fv F v) (hLv v) d b (lam v) (hlam v).1 (m v) (m₁ v) (m' v)
    (hm v) (hm₁ v) (hm' v) (φ v) (hφ v)
  choose G hGm hG1 hG2 using fun v => stg (Fv F v) (hLv v) d b (lam v) (hlam v).1 (m v) (m₁ v) (m' v)
    (hm v) (hm₁ v) (hm' v) ((latV b v).indicator 1) (measurable_one.indicator (hlatm v))

  obtain ⟨τ, hτ⟩ : ∃ τ : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, τ v = (m' v (hermOf (Fv F v) σ 0 h₀) (latV b v)).toReal :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : HeightOneSpectrum (𝓞 F) → ℝ,
      ∀ v, p v = (m₁ v (hermOf (Fv F v) σ 0 h₂) (primV σ J b v)).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨Mv, hMv⟩ : ∃ Mv : HeightOneSpectrum (𝓞 F) → ℝ,
      ∀ v, Mv v = (m v (hermOf (Fv F v) σ 0 h₁) (latV b v)).toReal := ⟨_, fun _ => rfl⟩
  have hτ' : ∀ v, m' v (hermOf (Fv F v) σ 0 h₀) (latV b v) = ENNReal.ofReal (τ v) := fun v => by
    rw [hτ, ENNReal.ofReal_toReal (hE'.1 v).ne]
  have hMv' : ∀ v, m v (hermOf (Fv F v) σ 0 h₁) (latV b v) = ENNReal.ofReal (Mv v) := fun v => by
    rw [hMv, ENNReal.ofReal_toReal (hfinL v).ne]
  have hτ0 : ∀ v, 0 ≤ τ v := fun v => by rw [hτ]; exact ENNReal.toReal_nonneg
  have hp0 : ∀ v, 0 ≤ p v := fun v => by rw [hp]; exact ENNReal.toReal_nonneg
  have hM0 : ∀ v, 0 ≤ Mv v := fun v => by rw [hMv]; exact ENNReal.toReal_nonneg
  have hsumτ : Summable fun v => |τ v - 1| := by simpa only [hτ] using hE'.2.1
  have hsump : Summable fun v => |p v - 1| := by simpa only [hp] using hsumP
  have hsumM : Summable fun v => |Mv v - 1| := by simpa only [hMv] using hsumL
  have hGprim : ∀ v, v ∉ S → ∀ y ∈ primV σ J b v, G v y = ENNReal.ofReal (τ v) := by
    rintro v hv _ ⟨g, hg, rfl⟩
    rw [hG1 v g, hS4 v hv (lam v) (hlam v) _ g hg, hτ']

  have hle : ∀ v, v ∉ S → τ v * p v ≤ Mv v := by
    intro v hv
    have h1 : ENNReal.ofReal (τ v) * m₁ v (hermOf (Fv F v) σ 0 h₂) (primV σ J b v) ≤
        m v (hermOf (Fv F v) σ 0 h₁) (latV b v) := by
      have e1 : m v (hermOf (Fv F v) σ 0 h₁) (latV b v) = ∫⁻ y, G v y ∂(m₁ v (hermOf (Fv F v) σ 0 h₂)) := by
        rw [← hG2 v, lintegral_indicator_one (hlatm v)]
      rw [e1]
      refine le_trans ?_ (mul_meas_ge_le_lintegral (hGm v) (ENNReal.ofReal (τ v)))
      gcongr
      intro y hy
      exact (hGprim v hv y hy).ge
    by_cases hpt : m₁ v (hermOf (Fv F v) σ 0 h₂) (primV σ J b v) = ⊤
    · rw [hp, hpt]
      simpa using hM0 v
    · have h2 : ENNReal.ofReal (τ v * p v) ≤ ENNReal.ofReal (Mv v) := by
        rw [ENNReal.ofReal_mul (hτ0 v), hp, ENNReal.ofReal_toReal hpt, ← hMv']
        exact h1
      exact (ENNReal.ofReal_le_ofReal_iff (hM0 v)).1 h2

  have hpure := hS₂ S hS2 φinf φ Ψinf Ψ G hφinf hφ hΨinf1 hΨ1 hG1
  obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞,
      (fun v => if v ∈ S then Ψ v else G v) = Ψ' := ⟨_, rfl⟩
  rw [hΨ'] at hpure
  have hΨ'S : ∀ v, v ∈ S → Ψ' v = Ψ v := fun v hv => by rw [← hΨ']; simp [hv]
  have hΨ'N : ∀ v, v ∉ S → Ψ' v = G v := fun v hv => by rw [← hΨ']; simp [hv]
  have hΨ'm : ∀ v, Measurable (Ψ' v) := fun v => by
    by_cases hv : v ∈ S
    · rw [hΨ'S v hv]; exact hΨm v
    · rw [hΨ'N v hv]; exact hGm v
  have hpm : ∀ S', Measurable (purePr σ J b S' Ψinf Ψ') := fun S' =>
    GlobalTheory.T.euler_product_lintegral_limit F E σ hCM M J hJ d b S' Ψinf Ψ' hΨinfm hΨ'm
  obtain ⟨term, hterm⟩ : ∃ term : Finset (HeightOneSpectrum (𝓞 F)) → (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞,
      ∀ S' y, term S' y = ENNReal.ofReal (∏' v : {v // v ∉ S'}, τ v.1) * purePr σ J b S' Ψinf Ψ' y :=
    ⟨_, fun _ _ => rfl⟩
  have htm : ∀ S', Measurable (term S') := fun S' => by
    have e : term S' = fun y => ENNReal.ofReal (∏' v : {v // v ∉ S'}, τ v.1) * purePr σ J b S' Ψinf Ψ' y :=
      funext (hterm S')
    rw [e]
    exact (hpm S').const_mul _
  have hmono : ∀ S' S'', S ⊆ S' → S' ⊆ S'' → ∀ y, term S' y ≤ term S'' y := by
    intro S' S'' h1 h2 y
    rw [hterm, hterm]
    by_cases hy : ∀ v, v ∉ S' → projV v (projFin y) ∈ primV σ J b v
    · have hy2 : ∀ v, v ∉ S'' → projV v (projFin y) ∈ primV σ J b v := fun v hv => hy v fun h => hv (h2 h)
      have e1 : purePr σ J b S' Ψinf Ψ' y = Ψinf (projInf y) * ∏ v ∈ S', Ψ' v (projV v (projFin y)) :=
        Set.indicator_of_mem (s := {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S' → projV v (projFin y) ∈ primV σ J b v}) hy _
      have e2 : purePr σ J b S'' Ψinf Ψ' y = Ψinf (projInf y) * ∏ v ∈ S'', Ψ' v (projV v (projFin y)) :=
        Set.indicator_of_mem (s := {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S'' → projV v (projFin y) ∈ primV σ J b v}) hy2 _
      have e3 : ∏ v ∈ S'' \ S', Ψ' v (projV v (projFin y)) = ∏ v ∈ S'' \ S', ENNReal.ofReal (τ v) :=
        Finset.prod_congr rfl fun v hv => by
          have hvS' : v ∉ S' := (Finset.mem_sdiff.1 hv).2
          have hvS : v ∉ S := fun h => hvS' (h1 h)
          rw [hΨ'N v hvS, hGprim v hvS _ (hy v hvS')]
      have ht := GlobalTheory.T.tprod_complement_split_finset _ τ S' S'' hsumτ h2
      rw [e1, e2, ← Finset.prod_sdiff h2, e3, ht, ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hτ0 v),
        ENNReal.ofReal_prod_of_nonneg fun v _ => hτ0 v]
      exact le_of_eq (by ring)
    · have e1 : purePr σ J b S' Ψinf Ψ' y = 0 :=
        Set.indicator_of_notMem (s := {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S' → projV v (projFin y) ∈ primV σ J b v}) hy _
      rw [e1, mul_zero]
      exact bot_le
  have hτtail : ∀ S' : Finset (HeightOneSpectrum (𝓞 F)), 0 ≤ ∏' v : {v // v ∉ S'}, τ v.1 := fun S' =>
    (GlobalTheory.T.infinite_product_multipliable {v // v ∉ S'} (fun v => τ v.1) (hsumτ.subtype _)).2.2.2 fun _ => hτ0 _
  have hint : ∀ S', S ⊆ S' → ∫⁻ y, term S' y ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))) =
      ((∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ 0 h₁))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ 0 h₁))) *
        ENNReal.ofReal ((∏ v ∈ S' \ S, Mv v) * ((∏' v : {v // v ∉ S'}, τ v.1) * ∏' v : {v // v ∉ S'}, p v.1)) := by
    intro S' hS'
    simp_rw [hterm]
    rw [lintegral_const_mul _ (hpm S'), hS₃ S' (hS3.trans hS') Ψinf Ψ' hΨinfm hΨ'm, ← hΨinf2]
    have hprod : ∏ v ∈ S', ∫⁻ y, Ψ' v y ∂(m₁ v (hermOf (Fv F v) σ 0 h₂)) =
        (∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ 0 h₁))) * ENNReal.ofReal (∏ v ∈ S' \ S, Mv v) := by
      rw [← Finset.prod_sdiff hS', mul_comm]
      congr 1
      · exact Finset.prod_congr rfl fun v hv => by rw [hΨ'S v hv, hΨ2 v]
      · rw [ENNReal.ofReal_prod_of_nonneg fun v _ => hM0 v]
        refine Finset.prod_congr rfl fun v hv => ?_
        rw [hΨ'N v (Finset.mem_sdiff.1 hv).2, ← hG2 v, lintegral_indicator_one (hlatm v), hMv']
    have hpt : ∏' v : {v // v ∉ S'}, (m₁ v.1 (hermOf (Fv F v.1) σ 0 h₂) (primV σ J b v.1)).toReal =
        ∏' v : {v // v ∉ S'}, p v.1 := tprod_congr fun v => (hp v.1).symm
    rw [hprod, hpt, ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hM0 v), ENNReal.ofReal_mul (hτtail S')]
    ring
  have hcond : ∀ h : HA (AF F) σ (hypOne J), (⨆ S', term (S ∪ S') (actW (AF F) σ (hypOne J) h (e0 _ M))) =
      ∫⁻ Y, ∫⁻ a, pureL b S φinf φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA
        ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E))) := by
    intro h
    obtain ⟨Sh, hSSh, hSh⟩ := hpure h
    have hv : ∀ S', Sh ⊆ S' → term S' (actW (AF F) σ (hypOne J) h (e0 _ M)) =
        ∫⁻ Y, ∫⁻ a, pureL b S φinf φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA
          ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E))) := fun S' hS' => by
      rw [hterm, hSh S' hS']
      congr 2
      exact tprod_congr fun v => hτ v.1
    apply le_antisymm
    · refine iSup_le fun S' => ?_
      rw [← hv (S ∪ S' ∪ Sh) Finset.subset_union_right]
      exact hmono _ _ Finset.subset_union_left Finset.subset_union_left _
    · rw [← hv Sh subset_rfl]
      refine le_iSup_of_le Sh ?_
      rw [Finset.union_eq_right.2 hSSh]
  have hΦm := GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b (n + 1) (M + 2) S φinf φ hφinf hφ
  have hΨgm : Measurable fun y => ⨆ S', term (S ∪ S') y := Measurable.iSup fun S' => htm _
  have hB := GlobalTheory.T.hyperbolic_plane_unfolding_integral F E σ hCM M J hJ n hn hnM μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ dA hdA _ _ hΦm hΨgm hcond
  rw [hB, lintegral_iSup_places _ S term htm hmono _ _ hint,
    GlobalTheory.T.iSup_finite_product_tail_limit _ Mv τ p S hsumM hsumτ hsump hM0 hτ0 hp0 hle]
  simp only [ENNReal.coe_one, one_mul]
  congr 2
  exact tprod_congr fun v => hMv v.1

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
theorem _root_.GlobalTheory.T.zero_block_coefficient_rank_increase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b) (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b), (framesE σ J (0 : Matrix (Fin n) (Fin n) E)).Nonempty → SWFree σ J (0 : Matrix (Fin n) (Fin n) E) h₀ → SWFree σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hyp_step | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hyp_step
end

section
noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_add_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J x (y + z) = hE σ J x y + hE σ J x z := by
  simp [hE, hform, mul_add, Finset.sum_add_distrib]

theorem hE_add_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J (x + y) z = hE σ J x z + hE σ J y z := by
  simp [hE, hform, add_mul, Finset.sum_add_distrib]

theorem hE_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J x (c • y) = c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J (c • x) y = σ c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul,
    AlgHom.coe_toRingHom, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_herm (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (y z : Fin M → E) : σ (hE σ J y z) = hE σ J z y := by
  simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

def hLin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (Fin M → E) →ₗ[E] E where
  toFun y := hE σ J x y
  map_add' := hE_add_right σ J x
  map_smul' c y := by simp [hE_smul_right]

theorem hLin_apply (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hLin σ J x y = hE σ J x y := rfl

theorem hE_sum_right (σ : E →ₐ[F] E) {M : ℕ} {ι : Type} (J : Matrix (Fin M) (Fin M) E)
    (x : Fin M → E) (s : Finset ι) (c : ι → E) (y : ι → Fin M → E) :
    hE σ J x (∑ k ∈ s, c k • y k) = ∑ k ∈ s, c k * hE σ J x (y k) := by
  rw [← hLin_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hLin_apply, hE_smul_right]

theorem cT_mul_apply (σ : E →ₐ[F] E) {M N : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (col : Fin N → Fin M → E) (i j : Fin N) :
    (cT (σ : E →+* E) (Matrix.of fun a b => col b a : Matrix (Fin M) (Fin N) E) * J *
      (Matrix.of fun a b => col b a : Matrix (Fin M) (Fin N) E)) i j = hE σ J (col i) (col j) := by
  simp only [cT, Matrix.mul_apply, hE, hform, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem split_herm (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hT : ∀ a b, σ (T b a) = T a b)
    (s : E) (x : Fin (n + 1) → E) (hs0 : s ≠ 0) (hx : hE σ T x x = s) :
    ∃ (g : GL (Fin (n + 1)) E) (T₁ : Matrix (Fin n) (Fin n) E), (∀ a b, σ (T₁ b a) = T₁ a b) ∧
      blockOne s T₁ = cT (σ : E →+* E) (g : Matrix (Fin (n + 1)) (Fin (n + 1)) E) * T * g := by
  have hherm := hE_herm σ hσ T hT
  have hsurj : Function.Surjective (hLin σ T x) := fun e =>
    ⟨(e / s) • x, by rw [map_smul, hLin_apply, hx, smul_eq_mul]; field_simp⟩
  have hfr : Module.finrank E (LinearMap.ker (hLin σ T x)) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker (hLin σ T x)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
    simp at h
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker (hLin σ T x)) hfr
  have hb : ∀ k, hE σ T x (b k : Fin (n + 1) → E) = 0 := fun k => (b k).2
  let col : Fin (n + 1) → Fin (n + 1) → E := Fin.cons x (fun k => (b k : Fin (n + 1) → E))
  let gm : Matrix (Fin (n + 1)) (Fin (n + 1)) E := Matrix.of fun i j => col j i
  have hG : ∀ i j, (cT (σ : E →+* E) gm * T * gm) i j = hE σ T (col i) (col j) :=
    fun i j => cT_mul_apply σ T col i j
  have hdet : gm.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hsum : v 0 • x + ∑ k : Fin n, v k.succ • (b k : Fin (n + 1) → E) = 0 := by
      rw [← hv]
      ext i
      simp [gm, col, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
    have hv00 : v 0 = 0 := by
      have h1 := congrArg (hLin σ T x) hsum
      rw [map_add, map_smul, map_sum, map_zero, hLin_apply, hx, smul_eq_mul] at h1
      have h2 : ∀ k : Fin n, hLin σ T x (v k.succ • (b k : Fin (n + 1) → E)) = 0 := by
        intro k
        rw [map_smul, hLin_apply, hb, smul_zero]
      simp only [h2, Finset.sum_const_zero, add_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_right hs0
    have hker : ∑ k : Fin n, v k.succ • b k = 0 := by
      apply Subtype.ext
      rw [hv00, zero_smul, zero_add] at hsum
      simpa using hsum
    have hvs := Fintype.linearIndependent_iff.1 b.linearIndependent _ hker
    apply hv0
    ext i
    refine Fin.cases hv00 hvs i
  let T₁ : Matrix (Fin n) (Fin n) E := Matrix.of fun k l =>
    hE σ T (b k : Fin (n + 1) → E) (b l : Fin (n + 1) → E)
  have hblock : blockOne s T₁ = cT (σ : E →+* E) gm * T * gm := by
    ext i j
    rw [hG]
    refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
    · simp [blockOne, col, hx]
    · simp [blockOne, col, hb]
    · have h3 : hE σ T (b k : Fin (n + 1) → E) x = 0 := by
        rw [← hherm, hb, map_zero]
      simp [blockOne, col, h3]
    · simp [blockOne, col, T₁]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero gm hdet, T₁, fun k l => hherm _ _, hblock⟩

variable [NumberField F] [NumberField E]

theorem exists_value (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (h0 : T ≠ 0) :
    ∃ (t : F) (x : Fin n → E), t ≠ 0 ∧ hE σ T x x = algebraMap F E t := by
  obtain ⟨hσ, δ, hδ, hδs⟩ := HaarCoord.conj_facts hCM
  have hherm := hE_herm σ hσ T hT
  have hne : ∃ x, hE σ T x x ≠ 0 := by
    by_contra hall
    push_neg at hall
    have key : ∀ x y, hE σ T x y + hE σ T y x = 0 := by
      intro x y
      have h := hall (x + y)
      rw [hE_add_left, hE_add_right, hE_add_right, hall x, hall y] at h
      simpa using h
    have key2 : ∀ x y, hE σ T x y = 0 := by
      intro x y
      have h1 := key x (δ • y)
      rw [hE_smul_right, hE_smul_left, hδs] at h1
      have h2 := key x y
      have h3 : δ * (hE σ T x y - hE σ T y x) = 0 := by linear_combination h1
      have h4 := (mul_eq_zero.1 h3).resolve_left hδ
      have h5 : (2 : E) * hE σ T x y = 0 := by linear_combination h2 + h4
      exact (mul_eq_zero.1 h5).resolve_left two_ne_zero
    apply h0
    ext a b
    have := key2 (Pi.single a 1) (Pi.single b 1)
    simpa [hE, hform, Pi.single_apply] using this
  obtain ⟨x, hx⟩ := hne
  have hs : σ (hE σ T x x) = hE σ T x x := hherm x x
  obtain ⟨β, hβ, -, -⟩ := GlobalTheory.CompanionTheory.SW.hermOne_eq_scal F E σ hCM (fun _ _ => hE σ T x x) (fun _ _ => hs)
  have hβ' : hE σ T x x = algebraMap F E β := congrFun (congrFun hβ 0) 0
  refine ⟨β, x, ?_, hβ'⟩
  rintro rfl
  exact hx (by simpa using hβ')

theorem hE_hypOne_cons (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a b c d : E)
    (x y : Fin M → E) :
    hE σ (hypOne J) (Fin.cons a (Fin.cons b x) : Fin (M + 2) → E)
        (Fin.cons c (Fin.cons d y) : Fin (M + 2) → E) = σ a * d + σ b * c + hE σ J x y := by
  simp only [hE, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have e00 : hypOne J 0 0 = 0 := rfl
  have e01 : hypOne J 0 (Fin.succ 0) = 1 := rfl
  have e10 : hypOne J (Fin.succ 0) 0 = 1 := rfl
  have e11 : hypOne J (Fin.succ 0) (Fin.succ 0) = 0 := rfl
  have e0r : ∀ j : Fin M, hypOne J 0 j.succ.succ = 0 := fun _ => rfl
  have e1r : ∀ j : Fin M, hypOne J (Fin.succ 0) j.succ.succ = 0 := fun _ => rfl
  have er0 : ∀ i : Fin M, hypOne J i.succ.succ 0 = 0 := fun _ => rfl
  have er1 : ∀ i : Fin M, hypOne J i.succ.succ (Fin.succ 0) = 0 := fun _ => rfl
  have err : ∀ i j : Fin M, hypOne J i.succ.succ j.succ.succ = J i j := fun _ _ => rfl
  simp only [e00, e01, e10, e11, e0r, e1r, er0, er1, err]
  simp
  ring

theorem split_hyp (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin (M + 2)) (Fin (M + 2)) E) (hJ : IsHermND σ J) (x : Fin (M + 2) → E)
    (hx0 : x ≠ 0) (hxx : hE σ J x x = 0) :
    ∃ (g : GL (Fin (M + 2)) E) (J₁ : Matrix (Fin M) (Fin M) E), IsHermND σ J₁ ∧
      hypOne J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M + 2)) (Fin (M + 2)) E) * J * g ∧
      ∀ i, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) E) i 0 = x i := by
  obtain ⟨hσ, -⟩ := HaarCoord.conj_facts hCM
  have hherm := hE_herm σ hσ J hJ.1

  have hex : ∃ y₀, hE σ J x y₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := by
      funext j
      have := hall (Pi.single j 1)
      simpa [hE, hform, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hz : (fun i => σ (x i)) = 0 := by
      have hu : IsUnit J := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hJ.2)
      exact (Matrix.vecMul_injective_of_isUnit hu) (by simpa using hv)
    apply hx0
    funext i
    have := congrFun hz i
    simpa using this
  obtain ⟨y₀, hy₀⟩ := hex
  obtain ⟨y₁, hxy₁⟩ : ∃ y₁, hE σ J x y₁ = 1 :=
    ⟨(hE σ J x y₀)⁻¹ • y₀, by rw [hE_smul_right]; exact inv_mul_cancel₀ hy₀⟩
  have hy₁x : hE σ J y₁ x = 1 := by rw [← hherm, hxy₁, map_one]
  obtain ⟨q, hq⟩ : ∃ q, q = hE σ J y₁ y₁ := ⟨_, rfl⟩
  have hqs : σ q = q := by rw [hq]; exact hherm _ _
  obtain ⟨y, hy⟩ : ∃ y : Fin (M + 2) → E, y = y₁ + (-(q / 2)) • x := ⟨_, rfl⟩
  have hxy : hE σ J x y = 1 := by
    rw [hy, hE_add_right, hE_smul_right, hxy₁, hxx]; simp
  have hyx : hE σ J y x = 1 := by rw [← hherm, hxy, map_one]
  have hyy : hE σ J y y = 0 := by
    have hs2 : σ (-(q / 2)) = -(q / 2) := by
      rw [map_neg, map_div₀, hqs, map_ofNat]
    rw [hy, hE_add_right, hE_add_left, hE_add_left, hE_smul_right, hE_smul_right, hE_smul_left,
      hE_smul_left, hs2, hy₁x, hxy₁, hxx, ← hq]
    field_simp
    ring
  let ψ : (Fin (M + 2) → E) →ₗ[E] (Fin 2 → E) := LinearMap.pi ![hLin σ J x, hLin σ J y]
  have hψ0 : ∀ z, ψ z 0 = hE σ J x z := fun _ => rfl
  have hψ1 : ∀ z, ψ z 1 = hE σ J y z := fun _ => rfl
  have hsurj : Function.Surjective ψ := fun e =>
    ⟨e 0 • y + e 1 • x, by
      funext i
      fin_cases i
      · change ψ _ 0 = e 0
        rw [hψ0, hE_add_right, hE_smul_right, hE_smul_right, hxy, hxx]; simp
      · change ψ _ 1 = e 1
        rw [hψ1, hE_add_right, hE_smul_right, hE_smul_right, hyx, hyy]; simp⟩
  have hfr : Module.finrank E (LinearMap.ker ψ) = M := by
    have h := LinearMap.finrank_range_add_finrank_ker ψ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
    simp at h
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker ψ) hfr
  have hb0 : ∀ k, hE σ J x (b k : Fin (M + 2) → E) = 0 := fun k => by
    rw [← hψ0, LinearMap.mem_ker.1 (b k).2]; rfl
  have hb1 : ∀ k, hE σ J y (b k : Fin (M + 2) → E) = 0 := fun k => by
    rw [← hψ1, LinearMap.mem_ker.1 (b k).2]; rfl
  have hb0' : ∀ k, hE σ J (b k : Fin (M + 2) → E) x = 0 := fun k => by
    rw [← hherm, hb0, map_zero]
  have hb1' : ∀ k, hE σ J (b k : Fin (M + 2) → E) y = 0 := fun k => by
    rw [← hherm, hb1, map_zero]
  let col : Fin (M + 2) → Fin (M + 2) → E :=
    Fin.cons x (Fin.cons y (fun k => (b k : Fin (M + 2) → E)))
  let gm : Matrix (Fin (M + 2)) (Fin (M + 2)) E := Matrix.of fun i j => col j i
  have hG : ∀ i j, (cT (σ : E →+* E) gm * J * gm) i j = hE σ J (col i) (col j) :=
    fun i j => cT_mul_apply σ J col i j
  have hdet : gm.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hsum : v 0 • x + v (Fin.succ 0) • y +
        ∑ k : Fin M, v k.succ.succ • (b k : Fin (M + 2) → E) = 0 := by
      rw [← hv]
      ext i
      simp [gm, col, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm, add_assoc]
    have hsx := congrArg (hE σ J x) hsum
    have hsy := congrArg (hE σ J y) hsum
    have hz0 : hE σ J x 0 = 0 := GlobalTheory.CompanionTheory.SW.BlockAlg.hE_zero_right σ J x
    have hz1 : hE σ J y 0 = 0 := GlobalTheory.CompanionTheory.SW.BlockAlg.hE_zero_right σ J y
    rw [hz0, hE_add_right, hE_add_right, hE_smul_right, hE_smul_right, hE_sum_right, hxx, hxy] at hsx
    rw [hz1, hE_add_right, hE_add_right, hE_smul_right, hE_smul_right, hE_sum_right, hyx, hyy] at hsy
    simp only [hb0, hb1, mul_zero, Finset.sum_const_zero, add_zero, mul_one, zero_add] at hsx hsy
    have hker : ∑ k : Fin M, v k.succ.succ • b k = 0 := by
      apply Subtype.ext
      rw [hsx, hsy, zero_smul, zero_smul, zero_add, zero_add] at hsum
      simpa using hsum
    have hvs := Fintype.linearIndependent_iff.1 b.linearIndependent _ hker
    apply hv0
    ext i
    refine Fin.cases hsy (fun i => Fin.cases hsx hvs i) i
  let J₁ : Matrix (Fin M) (Fin M) E := Matrix.of fun k l =>
    hE σ J (b k : Fin (M + 2) → E) (b l : Fin (M + 2) → E)
  have hblock : hypOne J₁ = cT (σ : E →+* E) gm * J * gm := by
    ext i j
    rw [hG]
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i <;>
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) j
    · simpa [col, hypOne] using hxx.symm
    · simpa [col, hypOne] using hxy.symm
    · simpa [col, hypOne] using (hb0 l).symm
    · simpa [col, hypOne] using hyx.symm
    · simpa [col, hypOne] using hyy.symm
    · simpa [col, hypOne] using (hb1 l).symm
    · simpa [col, hypOne] using (hb0' k).symm
    · simpa [col, hypOne] using (hb1' k).symm
    · simp [col, hypOne, J₁]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero gm hdet, J₁, ⟨fun k l => hherm _ _, ?_⟩, hblock,
    fun i => rfl⟩
  intro hJ0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hJ0
  have hd0 : (hypOne J₁).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨Fin.cons 0 (Fin.cons 0 v), ?_, ?_⟩
    · intro h
      apply hv0
      funext i
      simpa using congrFun h i.succ.succ
    · funext i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hypOne]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hypOne]
      · have := congrFun hv k
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hypOne] using this
  rw [hblock, Matrix.det_mul, Matrix.det_mul] at hd0
  have h5 : (cT (σ : E →+* E) gm).det = σ gm.det := by
    rw [cT, Matrix.det_transpose]
    exact ((σ : E →+* E).map_det gm).symm
  rw [h5] at hd0
  have h6 : σ gm.det ≠ 0 := (map_ne_zero _).2 hdet
  exact mul_ne_zero (mul_ne_zero h6 hJ.2) hdet hd0

theorem frames_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) E) (X : Fin n → Fin M → E)
    (hX : X ∈ framesE σ J T) :
    Scale.rE X (g : Matrix (Fin n) (Fin n) E) ∈
      framesE σ J (cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * (g : Matrix (Fin n) (Fin n) E)) := by
  refine ⟨?_, by rw [Scale.gramE_rE, hX.2]⟩
  have hind := Fintype.linearIndependent_iff.1 hX.1
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have h1 : ∀ b, ((g : Matrix (Fin n) (Fin n) E).mulVec c) b = 0 := by
    refine hind _ ?_
    funext i
    have := congrFun hc i
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Scale.rE,
      Finset.mul_sum] at this ⊢
    rw [Finset.sum_comm] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  have h2 : (g : Matrix (Fin n) (Fin n) E).mulVec c = 0 := funext h1
  have h3 : c = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).mulVec
      ((g : Matrix (Fin n) (Fin n) E).mulVec c) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
    simp
  intro a
  rw [h3, h2]
  simp

theorem frames_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (g : GL (Fin M) E) (X : Fin n → Fin M → E)
    (hX : X ∈ framesE σ J T) :
    SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) X ∈
      framesE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) T := by
  have hgg : ∀ u : Fin M → E, (g : Matrix (Fin M) (Fin M) E).mulVec
      (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
    simp
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective
        (Matrix.mulVecLin ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) := fun u w h => by
      have h' : ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec u =
        ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec w := h
      rw [← hgg u, h', hgg]
    have hfun : SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) X =
        (Matrix.mulVecLin ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) ∘ X := by
      funext a
      rfl
    rw [hfun]
    exact LinearIndependent.map' hX.1
      (Matrix.mulVecLin ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E))
      (LinearMap.ker_eq_bot.2 hinj)
  · have key : ∀ a b, hE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
        (g : Matrix (Fin M) (Fin M) E))
        (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec (X a))
        (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec (X b)) = hE σ J (X a) (X b) := by
      intro a b
      simp only [hE, SWIsom.hform_conj, hgg]
    rw [← hX.2]
    funext a b
    exact key a b

theorem frames_tail_aniso (σ : E →ₐ[F] E) {M n : ℕ} (J₁ : Matrix (Fin M) (Fin M) E)
    (T₁ : Matrix (Fin n) (Fin n) E) (s : E) (hs : s ≠ 0) (X : Fin (n + 1) → Fin (M + 1) → E)
    (hX : X ∈ framesE σ (blockOne s J₁) (blockOne s T₁))
    (h0 : X 0 = Fin.cons 1 (fun _ => 0)) :
    (fun (a : Fin n) (i : Fin M) => X a.succ i.succ) ∈ framesE σ J₁ T₁ := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hgr : ∀ a b, hE σ (blockOne s J₁) (X a) (X b) = blockOne s T₁ a b := fun a b =>
    congrFun (congrFun hX.2 a) b
  have hc : ∀ a, X a = Fin.cons (X a 0) (fun i => X a i.succ) := fun a =>
    (Fin.cons_self_tail (X a)).symm
  have hfirst : ∀ a : Fin n, X a.succ 0 = 0 := by
    intro a
    have h := hgr 0 a.succ
    rw [h0, hc a.succ, BlockAlg.hE_blockOne_cons, hz, BlockAlg.hE_zero_left] at h
    have h2 : blockOne s T₁ 0 a.succ = 0 := rfl
    rw [h2] at h
    simp only [map_one, one_mul, add_zero] at h
    simpa [hs] using h
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc' a => ?_
    have h1 := Fintype.linearIndependent_iff.1 hX.1 (Fin.cons 0 c) (by
      rw [Fin.sum_univ_succ]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [hfirst]
      · have := congrFun hc' i
        simpa using this) a.succ
    simpa using h1
  · ext a b
    have h := hgr a.succ b.succ
    rw [hc a.succ, hc b.succ, BlockAlg.hE_blockOne_cons, hfirst, hfirst] at h
    have h2 : blockOne s T₁ a.succ b.succ = T₁ a b := rfl
    rw [h2] at h
    simpa [gramE] using h

theorem frames_tail_hyp (σ : E →ₐ[F] E) {M n : ℕ} (J₁ : Matrix (Fin M) (Fin M) E)
    (X : Fin (n + 1) → Fin (M + 2) → E) (hX : X ∈ framesE σ (hypOne J₁) 0)
    (h0 : X 0 = Fin.cons 1 (Fin.cons 0 (fun _ => 0))) :
    (fun (a : Fin n) (i : Fin M) => X a.succ i.succ.succ) ∈ framesE σ J₁ 0 := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hgr : ∀ a b, hE σ (hypOne J₁) (X a) (X b) = 0 := fun a b =>
    congrFun (congrFun hX.2 a) b
  have hc : ∀ a, X a = Fin.cons (X a 0) (Fin.cons (X a (Fin.succ 0)) (fun i => X a i.succ.succ)) :=
    fun a => by
      funext i
      refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i
  have hsec : ∀ a : Fin n, X a.succ (Fin.succ 0) = 0 := by
    intro a
    have h := hgr 0 a.succ
    rw [h0, hc a.succ, hE_hypOne_cons, hz, BlockAlg.hE_zero_left] at h
    simpa using h
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc' a => ?_
    have h1 := Fintype.linearIndependent_iff.1 hX.1
      (Fin.cons (-∑ k, c k * X k.succ 0) c) (by
      rw [Fin.sum_univ_succ, h0]
      funext i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
      · simp [Finset.sum_apply]
      · have hsec' : ∀ a : Fin n, X a.succ 1 = 0 := hsec
        simp [Finset.sum_apply, hsec']
      · have := congrFun hc' k
        simpa [Finset.sum_apply] using this) a.succ
    simpa using h1
  · ext a b
    have h := hgr a.succ b.succ
    rw [hc a.succ, hc b.succ, hE_hypOne_cons, hsec, hsec] at h
    simpa [gramE] using h

end Alg

section Main

theorem swFree_singular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det = 0 → 2 * n < M → (framesE σ J T).Nonempty → SWFree σ J T hT := by
  intro F E _ _ _ _ _ σ hCM n
  obtain ⟨hσ, -⟩ := HaarCoord.conj_facts hCM
  induction n with
  | zero =>
    intro M J hJ T hT hd
    simp at hd
  | succ n ih =>
    intro M J hJ T hT hd hM hfr
    obtain ⟨X, hX⟩ := hfr
    by_cases h0 : T = 0
    · subst h0
      rcases n with _ | n
      · exact GlobalTheory.T.siegelWeilFree_zero_rank_one_of_three_le F E σ hCM M J hJ (by omega) hT ⟨X, hX⟩
      · obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 2 := ⟨M - 2, by omega⟩
        have hx0 : X 0 ≠ 0 := hX.1.ne_zero 0
        have hxx : hE σ J (X 0) (X 0) = 0 := congrFun (congrFun hX.2 0) 0
        obtain ⟨g, J₁, hJ₁, hb, hcol⟩ := split_hyp σ hCM J hJ (X 0) hx0 hxx
        have hX' := frames_left σ J _ g X hX
        rw [← hb] at hX'
        have hfirst : SWIsom.ratAct ((g⁻¹ : GL (Fin (M₁ + 2)) E) : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) X 0 =
            Fin.cons 1 (Fin.cons 0 (fun _ => 0)) := by
          have he : (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E).mulVec
              (Fin.cons 1 (Fin.cons 0 (fun _ => 0))) = X 0 := by
            funext i
            rw [← hcol i]
            simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
          simp only [SWIsom.ratAct]
          rw [← he, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
          simp
        have hfr₁ := frames_tail_hyp σ J₁ _ hX' hfirst
        have h₀ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) =
            (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b := fun a b => by simp
        have hSW := ih M₁ J₁ hJ₁ 0 h₀ Matrix.det_zero (by omega) ⟨_, hfr₁⟩
        exact GlobalTheory.T.siegelWeilFree_of_congruent_form F E σ hCM (M₁ + 2) J hJ g _ hb (n + 1 + 1) 0 hT
          (GlobalTheory.T.zero_block_coefficient_rank_increase F E σ hCM M₁ J₁ hJ₁ (n + 1) (by omega) (by omega) h₀ hT ⟨_, hfr₁⟩ hSW)
    · obtain ⟨t, x, ht, hx⟩ := exists_value σ hCM T hT h0
      have hta : algebraMap F E t ≠ 0 := by simpa using ht
      obtain ⟨g, T₁, hT₁, hb⟩ := split_herm σ hσ T hT _ x hta hx
      obtain ⟨-, hblk, -, -⟩ := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM n T₁ t
      have hT' := hblk hT₁
      have hg0 : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) E).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
      have hd₁ : T₁.det = 0 := by
        have h := congrArg Matrix.det hb
        rw [BlockAlg.det_blockOne, Matrix.det_mul, Matrix.det_mul, hd] at h
        simp only [mul_zero, zero_mul] at h
        exact (mul_eq_zero.1 h).resolve_left hta
      have hX₁ := frames_right σ J T g X hX
      rw [← hb] at hX₁
      obtain ⟨Y, hY⟩ : ∃ Y, Y = Scale.rE X (g : Matrix (Fin (n + 1)) (Fin (n + 1)) E) := ⟨_, rfl⟩
      rw [← hY] at hX₁
      have hyy : hE σ J (Y 0) (Y 0) = algebraMap F E t := congrFun (congrFun hX₁.2 0) 0
      obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 1 := ⟨M - 1, by omega⟩
      obtain ⟨g', J₁, hJ₁, hb', hcol⟩ :=
        GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hCM M₁ J hJ t (Y 0) ht hyy
      have hX₂ := frames_left σ J _ g' Y hX₁
      rw [← hb'] at hX₂
      have hfirst : SWIsom.ratAct ((g'⁻¹ : GL (Fin (M₁ + 1)) E) : Matrix (Fin (M₁ + 1)) (Fin (M₁ + 1)) E) Y 0 =
          Fin.cons 1 (fun _ => 0) := by
        have he : (g' : Matrix (Fin (M₁ + 1)) (Fin (M₁ + 1)) E).mulVec
            (Fin.cons 1 (fun _ => 0)) = Y 0 := by
          funext i
          rw [← hcol i]
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        simp only [SWIsom.ratAct]
        rw [← he, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
        simp
      have hfr₁ := frames_tail_aniso σ J₁ T₁ _ hta _ hX₂ hfirst
      have hSW := ih M₁ J₁ hJ₁ T₁ hT₁ hd₁ (by omega) ⟨_, hfr₁⟩
      refine GlobalTheory.T.siegelWeilFree_of_congruent_matrix F E σ hCM (M₁ + 1) J hJ (n + 1) T hT g _ hT' hb ?_
      exact GlobalTheory.T.siegelWeilFree_of_congruent_form F E σ hCM (M₁ + 1) J hJ g' _ hb' (n + 1) _ hT'
        (GlobalTheory.T.siegelWeilFree_extend_by_scalar_block F E σ hCM M₁ J₁ hJ₁ t ht n (by omega) T₁ hT₁ hT' ⟨_, hfr₁⟩ hSW)

theorem swFree_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n t : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), IsBlockM t T → 2 * n < M → (framesE σ J T).Nonempty → SWFree σ J T hT := by
  intro F E _ _ _ _ _ σ hCM M J hJ n t T hT hB hM hfr
  obtain ⟨h, hz, -⟩ := hB
  exact swFree_singular F E σ hCM n M J hJ T hT
    (Matrix.det_eq_zero_of_row_eq_zero ⟨t, h⟩ fun j => hz _ _ (Or.inl le_rfl)) hM hfr

end Main

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.siegelWeil_free_of_block_nonempty_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n t : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), IsBlockM t T → 2 * n < M → (framesE σ J T).Nonempty → SWFree σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.swFree_block | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.swFree_block
end
