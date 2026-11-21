import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainExistsUnitaryStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaust
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFinite
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsRealFlowAdelicUnits
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FlowLatticeCountBounded
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CountingRationalVectorsBoxBound
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SplitAnisotropic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainTransportCongruentForm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscrete
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneRightInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionGlobal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InvariantMeasureCompactCoverBound
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainOfSubgroupFromCosetReps
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramOrbitCompactRepresentative
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerateStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureIntegralFormula

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SmallQ

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem gramR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : R)
    (X : Fin n → Fin M → R ⊗[F] E) (a c : Fin n) :
    gramR R σ J ((s ⊗ₜ[F] (1 : E)) • X) a c =
      ((s ⊗ₜ[F] (1 : E)) * (s ⊗ₜ[F] (1 : E))) * gramR R σ J X a c := by
  have hs : sigR R σ (s ⊗ₜ[F] (1 : E)) = s ⊗ₜ[F] (1 : E) := by simp [sigR]
  simp only [gramR, hR, hform, Pi.smul_apply, smul_eq_mul, map_mul, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem small_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (t : F) (Y : Fin 1 → Fin M → AF F ⊗[F] E), Y ∈ box b N r₀ → (gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)) → t = 0 := by
  intro F E _ _ _ _ _ σ hcm M J hJ d b N hN
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hcont : Continuous (gramR (AF F) σ J : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.2.2.2.2.2 1 M J
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_real_flow_adelic_units F E σ hcm
  have hbox := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hcm d b 1 M
  have hΩ : IsCompact (box b N 1 : Set (Fin 1 → Fin M → AF F ⊗[F] E)) := hbox.1 N 1 hN
  let φ : (Fin 1 → Fin M → AF F ⊗[F] E) → Fin 1 → Fin 1 → AF F ⊗[F] E :=
    fun Y a c => gramR (AF F) σ J Y a c
  have hφ : Continuous φ :=
    continuous_pi fun a => continuous_pi fun c => hcont.matrix_elem a c
  obtain ⟨x₀, C, hcount⟩ := GlobalTheory.T.flow_lattice_count_bounded F E σ hcm τ hτ 1 (φ '' box b N 1) (hΩ.image hφ)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, -(2 * x) < x₀ :=
    ⟨|x₀| + 1, by linarith [neg_abs_le x₀, abs_nonneg x₀]⟩
  refine ⟨Real.exp (-x), Real.exp_pos _, ?_⟩
  intro t Y hY hg
  by_contra ht
  have hY' : ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈ box b N 1 := by
    have h := (hbox.2.2 τ hτ N (Real.exp (-x)) x Y).2 hY
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  obtain ⟨-, θ, -, hθ⟩ := hτ
  have hc := hθ x
  have hsq : ((τ (Multiplicative.ofAdd (-(-(2 * x)))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) *
        ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := by
    rw [← Units.val_mul, ← map_mul, ← ofAdd_add]
    congr 3
    ring
  let X₀ : {X : Fin 1 → Fin 1 → E // X ≠ 0} :=
    ⟨fun _ _ => algebraMap F E t, fun h0 =>
      ht ((algebraMap F E).injective (by simpa using congrFun (congrFun h0 0) 0))⟩
  have hmem : ((τ (Multiplicative.ofAdd (-(-(2 * x)))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
      ratTup (AF F) X₀.1 ∈ φ '' box b N 1 := by
    refine ⟨_, hY', ?_⟩
    funext a c
    have h1 : gramR (AF F) σ J Y a c = inclR (AF F) (algebraMap F E t) := by rw [hg]
    simp only [φ]
    rw [hc, gramR_smul, h1, hsq, hc]
    rfl
  have hle := hcount (-(2 * x))
  rw [if_pos hx] at hle
  have h1 := (ENNReal.le_tsum X₀).trans hle
  rw [Set.indicator_of_mem hmem] at h1
  simp at h1

end GlobalTheory.CompanionTheory.SW.SmallQ
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_box_gram_scalar_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (t : F) (Y : Fin 1 → Fin M → AF F ⊗[F] E), Y ∈ box b N r₀ → (gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)) → t = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.SmallQ.small_length
end

section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_measure_compact_cover_bound : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∃ (C' : Set G) (K : ℝ≥0∞), IsCompact C' ∧ K < ⊤ ∧ ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ P → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ S : Set G, MeasurableSet S → (∀ᵐ p ∂ν, ∃ γ ∈ Γ, γ * p ∈ S) → ∀ f g : G → ℝ≥0∞, Measurable f → Measurable g → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ x, f x ≠ 0 → ∃ p ∈ P, ∃ c ∈ C, x = p * c) → (∀ p ∈ S, ∀ c ∈ C', f (p * c) ≤ g p) → ∫⁻ x in 𝓕, f x ∂μ ≤ K * ∫⁻ p in S, g p ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel | exact GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel | (intros; apply GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_of_subgroup_from_coset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain | exact GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain <;> assumption)
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Aniso

theorem mean_lt_top {G G₁ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure]
    (ι : G₁ →* G) (hι : IsClosedEmbedding ι) (Γ : Subgroup G) [Countable Γ]
    (Γ₁ : Subgroup G₁) (hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (𝓕₁ : Set G₁) (hm₁ : MeasurableSet 𝓕₁) (hfin : μ₁ 𝓕₁ < ⊤) (hcov : ∀ u, ∃ γ ∈ Γ₁, γ * u ∈ 𝓕₁)
    (Q : Type) (r : Q → G) (hr : ∀ q, r q ∈ Γ)
    (hQ : ∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ ⊓ ι.range)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1)
    (hinv : ∀ p ∈ ι.range, ∀ x, f (p * x) = f x)
    (C : Set G) (hC : IsCompact C) (hsupp : ∀ x, f x ≠ 0 → ∃ p ∈ ι.range, ∃ c ∈ C, x = p * c) :
    ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ < ⊤ := by
  have hme : MeasurableEmbedding ι := hι.measurableEmbedding
  have hνinv : ∀ p ∈ ι.range, (μ₁.map ι).map (fun g => p * g) = μ₁.map ι := by
    rintro _ ⟨u, rfl⟩
    rw [Measure.map_map (measurable_const_mul _) hme.measurable]
    have h : (fun g => ι u * g) ∘ ι = ι ∘ (fun g => u * g) := by
      ext g; simp
    rw [h, ← Measure.map_map hme.measurable (measurable_const_mul _), map_mul_left_eq_self]
  have hνpos : ∀ U ∈ 𝓝 (1 : G), (μ₁.map ι) U ≠ 0 := by
    intro U hU
    have h1 : ι ⁻¹' U ∈ 𝓝 (1 : G₁) :=
      hι.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
    have h2 : 0 < μ₁ (ι ⁻¹' U) := μ₁.measure_pos_of_mem_nhds h1
    have h3 : μ₁ (ι ⁻¹' U) ≤ (μ₁.map ι) U := Measure.le_map_apply hme.measurable.aemeasurable U
    exact (h2.trans_le h3).ne'
  obtain ⟨C', K, hC', hK, hcover⟩ := GlobalTheory.T.invariant_measure_compact_cover_bound G μ ι.range (μ₁.map ι) hνinv hνpos C hC
  obtain ⟨𝓕', h𝓕', hunf⟩ := GlobalTheory.T.fundamental_domain_of_subgroup_from_coset_reps G μ Γ (Γ ⊓ ι.range) inf_le_left 𝓕 h𝓕 Q r hr hQ
  rw [hunf f hf]
  haveI : Countable ↥(Γ ⊓ ι.range) :=
    (Subgroup.inclusion_injective (inf_le_left : Γ ⊓ ι.range ≤ Γ)).countable
  have hae : ∀ᵐ p ∂(μ₁.map ι), ∃ γ ∈ Γ ⊓ ι.range, γ * p ∈ ι '' 𝓕₁ := by
    refine hme.ae_map_iff.2 (Filter.Eventually.of_forall fun u => ?_)
    obtain ⟨γ, hγ, hγu⟩ := hcov u
    exact ⟨ι γ, ⟨hΓ γ hγ, γ, rfl⟩, γ * u, hγu, map_mul ι γ u⟩
  have hb := hcover (Γ ⊓ ι.range) inf_le_right 𝓕' h𝓕' (ι '' 𝓕₁) (hme.measurableSet_image.2 hm₁) hae f
    (fun _ => 1) hf measurable_const (fun γ hγ x => hinv γ hγ.2 x) hsupp (fun p _ c _ => hf1 _)
  have hS : ∫⁻ p in ι '' 𝓕₁, (1 : ℝ≥0∞) ∂(μ₁.map ι) = μ₁ 𝓕₁ := by
    rw [lintegral_one, Measure.restrict_apply_univ, hme.map_apply,
      Set.preimage_image_eq _ hι.injective]
  rw [hS] at hb
  exact hb.trans_lt (ENNReal.mul_lt_top hK hfin)

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem bc_mem_HR (g : GL (Fin M) E) (hg : g ∈ UJ (σ : E →+* E) J) :
    bc (inclR (F := F) R) g ∈ HR R σ J := by
  have hs : ∀ e : E, sigR R σ (inclR (F := F) R e) = inclR (F := F) R (σ e) := by
    intro e; simp [sigR, inclR]
  have hval : ((bc (inclR (F := F) R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (g : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R) := rfl
  have hc : cT (sigR R σ) ((g : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)) =
      (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)).map (inclR (F := F) R) := by
    ext i j
    simp [cT, hs]
  have hg' : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  show cT (sigR R σ) ((bc (inclR (F := F) R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
    ((bc (inclR (F := F) R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J
  rw [hval, hc]
  unfold JR
  rw [← Matrix.map_mul, ← Matrix.map_mul, hg']

def ratH (g : GL (Fin M) E) (hg : g ∈ UJ (σ : E →+* E) J) : HA R σ J :=
  (⟨bc (inclR (F := F) R) g, bc_mem_HR R σ J g hg⟩ : HR R σ J)

theorem mat_ratH (g : GL (Fin M) E) (hg : g ∈ UJ (σ : E →+* E) J) :
    HA.mat R σ J (ratH R σ J g hg) = bc (inclR (F := F) R) g := rfl

theorem act_rat (γ : HA R σ J) (g : GL (Fin M) E) (hγ : HA.mat R σ J γ = bc (inclR (F := F) R) g) {n : ℕ}
    (X : Fin n → Fin M → E) :
    actW R σ J γ (ratTup R X) = ratTup R (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  funext a i
  simp only [actW, actTup, ratTup, hγ]
  show ∑ j, inclR (F := F) R ((g : Matrix (Fin M) (Fin M) E) i j) * inclR (F := F) R (X a j) =
    inclR (F := F) R (∑ j, (g : Matrix (Fin M) (Fin M) E) i j * X a j)
  simp [map_sum]

end Rat

theorem count_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ t : F, t ≠ 0 → ∀ (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) (𝓕 : Set (HA (AF F) σ (blockOne (algebraMap F E t) J))), IsHaarH F E σ (M + 1) (blockOne (algebraMap F E t) J) μ → IsFDH F E σ (M + 1) (blockOne (algebraMap F E t) J) μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin (M + 1) → AF F ⊗[F] E), IsCompact Ω → cntI σ _ μ 𝓕 {X | gramE σ (blockOne (algebraMap F E t) J) X = fun _ _ => algebraMap F E t} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  intro F E _ _ _ _ _ σ hσ M J hJ hvol t ht μ 𝓕 hμ h𝓕 Ω hΩ
  have hJb : IsHermND σ (blockOne (algebraMap F E t) J) := (GlobalTheory.T.hyperbolic_and_block_one_nondegenerate F E σ hσ M J hJ).2 t ht
  obtain ⟨⟨a1, a2, a3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := a1
  haveI := a2
  haveI := a3
  haveI : T2Space (AF F ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.1
  haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
  haveI : Nontrivial (AF F ⊗[F] E) := inferInstance
  obtain ⟨tg, lc, sc, t2, bs, hact⟩ :=
    GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ (M + 1) (blockOne (algebraMap F E t) J) hJb (AF F)
  obtain ⟨tg₁, lc₁, sc₁, t2₁, bs₁, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := tg
  haveI := lc
  haveI := sc
  haveI := t2
  haveI := bs
  haveI := tg₁
  haveI := lc₁
  haveI := sc₁
  haveI := t2₁
  haveI := bs₁
  obtain ⟨hcont, -, hmul, hgram⟩ := hact 1
  haveI : μ.IsHaarMeasure := hμ

  let e0E : Fin 1 → Fin (M + 1) → E := fun _ => Fin.cons 1 (fun _ => 0)
  let e0 : Fin 1 → Fin (M + 1) → AF F ⊗[F] E := ratTup (AF F) e0E
  have he0 : e0 = fun _ : Fin 1 => Fin.cons 1 (fun _ => 0) := by
    funext a i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e0, e0E, ratTup]
    · simp [e0, e0E, ratTup]
  have hg0 : gramE σ (blockOne (algebraMap F E t) J) e0E = fun _ _ => algebraMap F E t := by
    funext a b
    simp [gramE, hE, hform, e0E, Fin.sum_univ_succ, blockOne]
  have hdet : (gramE σ (blockOne (algebraMap F E t) J) e0E).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    have h00 : gramE σ (blockOne (algebraMap F E t) J) e0E 0 0 = algebraMap F E t :=
      congrFun (congrFun hg0 0) 0
    rw [h00]
    simpa using ht
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) := RingHom.injective _
  have hratinj : Function.Injective
      (ratTup (F := F) (AF F) : (Fin 1 → Fin (M + 1) → E) → (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) := by
    intro X Y h
    funext a i
    exact hinj (congrFun (congrFun h a) i)
  obtain ⟨hgr1, hgr2, -⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hσ (M + 1) (blockOne (algebraMap F E t) J) hJb
  obtain ⟨ι, hιc, hιm, hιs, hιr, -⟩ := GlobalTheory.CompanionTheory.SW.StabFirst.stab_first F E σ hσ M J hJ t ht (AF F)
  have hstab : ∀ h, h ∈ ι.range ↔ actW (AF F) σ (blockOne (algebraMap F E t) J) h e0 = e0 := by
    intro h
    rw [he0]
    exact hιs h

  have hinvact : ∀ (h : HA (AF F) σ (blockOne (algebraMap F E t) J)) (Y Z : Fin 1 → Fin (M + 1) → AF F ⊗[F] E),
      actW (AF F) σ (blockOne (algebraMap F E t) J) h Y = Z →
      actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ Z = Y := by
    intro h Y Z hYZ
    obtain ⟨-, hone, -, -⟩ := hact 1
    rw [← hYZ, ← hmul, inv_mul_cancel, hone]

  let Q : Set (Fin 1 → Fin (M + 1) → E) :=
    {X | gramE σ (blockOne (algebraMap F E t) J) X = fun _ _ => algebraMap F E t}
  have hrep : ∀ q : Q, ∃ g ∈ UJ (σ : E →+* E) (blockOne (algebraMap F E t) J),
      ∀ a, (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) *ᵥ q.1 a = e0E a := by
    intro q
    have hq : gramE σ (blockOne (algebraMap F E t) J) q.1 = gramE σ (blockOne (algebraMap F E t) J) e0E :=
      q.2.trans hg0.symm
    exact GlobalTheory.T.witt_extension_global F E σ hσ (M + 1) _ hJb 1 q.1 e0E hq (hq ▸ hdet)
  choose g hg hgq using hrep
  let r : Q → HA (AF F) σ (blockOne (algebraMap F E t) J) := fun q => ratH (AF F) σ _ (g q) (hg q)
  have hrq : ∀ q : Q, actW (AF F) σ (blockOne (algebraMap F E t) J) (r q) (ratTup (AF F) q.1) = e0 := by
    intro q
    rw [act_rat (AF F) σ _ (r q) (g q) (mat_ratH (AF F) σ _ (g q) (hg q))]
    show ratTup (AF F) _ = ratTup (AF F) e0E
    congr 1
    funext a
    exact hgq q a
  have hrq' : ∀ q : Q, actW (AF F) σ (blockOne (algebraMap F E t) J) (r q)⁻¹ e0 = ratTup (AF F) q.1 :=
    fun q => hinvact _ _ _ (hrq q)

  let f : HA (AF F) σ (blockOne (algebraMap F E t) J) → ℝ≥0∞ := fun h =>
    Set.indicator Ω (fun _ => (1 : ℝ≥0∞)) (actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0)
  have hfm : Measurable f := by
    have hc : Continuous fun h : HA (AF F) σ (blockOne (algebraMap F E t) J) =>
        actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0 :=
      hcont.comp (continuous_inv.prodMk continuous_const)
    have hcl : IsClosed Ω := hΩ.isClosed
    have : f = Set.indicator ((fun h : HA (AF F) σ (blockOne (algebraMap F E t) J) =>
        actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0) ⁻¹' Ω) (fun _ => (1 : ℝ≥0∞)) := by
      funext h
      by_cases hh : actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0 ∈ Ω
      · simp only [f]
        rw [Set.indicator_of_mem hh, Set.indicator_of_mem (show h ∈ ((fun h : HA (AF F) σ (blockOne (algebraMap F E t) J) => actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0) ⁻¹' Ω) from hh)]
      · simp only [f]
        rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (show h ∉ ((fun h : HA (AF F) σ (blockOne (algebraMap F E t) J) => actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0) ⁻¹' Ω) from hh)]
    rw [this]
    exact measurable_const.indicator (hcl.preimage hc).measurableSet
  have hf1 : ∀ x, f x ≤ 1 := by
    intro x
    simp only [f, Set.indicator]
    split_ifs <;> simp
  have hinv : ∀ p ∈ ι.range, ∀ x, f (p * x) = f x := by
    intro p hp x
    have hp' : p⁻¹ ∈ ι.range := ι.range.inv_mem hp
    have : actW (AF F) σ (blockOne (algebraMap F E t) J) (p * x)⁻¹ e0 =
        actW (AF F) σ (blockOne (algebraMap F E t) J) x⁻¹ e0 := by
      rw [mul_inv_rev, hmul, (hstab _).1 hp']
    simp only [f, this]
  obtain ⟨C₀, hC₀, hC₀p⟩ := GlobalTheory.T.gram_orbit_compact_representative F E σ hσ (M + 1) _ hJb 1 e0E hdet Ω hΩ
  have hsupp : ∀ x, f x ≠ 0 → ∃ p ∈ ι.range, ∃ c ∈ C₀⁻¹, x = p * c := by
    intro x hx
    have hxΩ : actW (AF F) σ (blockOne (algebraMap F E t) J) x⁻¹ e0 ∈ Ω := by
      by_contra hn
      exact hx (Set.indicator_of_notMem hn _)
    obtain ⟨c, hc, hce⟩ := hC₀p _ hxΩ (by rw [hgram]; exact hgr2 1 e0E)
    refine ⟨x * c, (hstab _).2 ?_, c⁻¹, Set.inv_mem_inv.2 hc, by group⟩
    rw [hmul]
    show actW (AF F) σ (blockOne (algebraMap F E t) J) x (actW (AF F) σ (blockOne (algebraMap F E t) J) c (ratTup (AF F) e0E)) = e0
    rw [hce, ← hmul, mul_inv_cancel]
    exact (hact 1).2.1 e0

  let Γ : Subgroup (HA (AF F) σ (blockOne (algebraMap F E t) J)) := HFinIn (AF F) σ (blockOne (algebraMap F E t) J)
  let Γ₁ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI : Countable Γ := (GlobalTheory.CompanionTheory.SW.rational_countable_discrete F E σ hσ (M + 1) _ hJb).1
  have hmemΓ : ∀ γ : HA (AF F) σ (blockOne (algebraMap F E t) J),
      γ ∈ Γ ↔ HA.mat (AF F) σ _ γ ∈ HFin (AF F) σ (blockOne (algebraMap F E t) J) := fun γ => Iff.rfl
  have hmemΓ₁ : ∀ γ : HA (AF F) σ J, γ ∈ Γ₁ ↔ HA.mat (AF F) σ _ γ ∈ HFin (AF F) σ J := fun γ => Iff.rfl
  have hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ := fun u hu => (hmemΓ _).2 ((hιr u).2 ((hmemΓ₁ u).1 hu))
  have hr : ∀ q, r q ∈ Γ := fun q => (hmemΓ _).2 (Subgroup.mem_map.2 ⟨g q, hg q, rfl⟩)
  have hQ : ∀ γ ∈ Γ, ∃! q : Q, γ * (r q)⁻¹ ∈ Γ ⊓ ι.range := by
    intro γ hγ
    obtain ⟨g₀, hg₀, hγ₀⟩ := Subgroup.mem_map.1 ((hmemΓ γ).1 hγ)
    have hinvm : HA.mat (AF F) σ _ γ⁻¹ = bc (inclR (F := F) (AF F)) g₀⁻¹ := by
      rw [map_inv, hγ₀]
      rfl
    have hX : actW (AF F) σ (blockOne (algebraMap F E t) J) γ⁻¹ e0 =
        ratTup (AF F) (fun a => ((g₀⁻¹ : GL _ E) : Matrix (Fin (M + 1)) (Fin (M + 1)) E) *ᵥ e0E a) :=
      act_rat (AF F) σ _ γ⁻¹ g₀⁻¹ hinvm e0E
    have hXQ : (fun a => ((g₀⁻¹ : GL _ E) : Matrix (Fin (M + 1)) (Fin (M + 1)) E) *ᵥ e0E a) ∈ Q := by
      show gramE σ _ _ = _
      rw [← hg0]
      have h1 := hgram γ⁻¹ e0
      rw [hX, hgr2] at h1
      have h2 : gramR (AF F) σ (blockOne (algebraMap F E t) J) e0 =
          (gramE σ (blockOne (algebraMap F E t) J) e0E).map (inclR (AF F)) := hgr2 1 e0E
      rw [h2] at h1
      exact Matrix.map_injective hinj h1
    refine ⟨⟨_, hXQ⟩, ?_, ?_⟩
    · refine ⟨Γ.mul_mem hγ (Γ.inv_mem (hr _)), (hstab _).2 ?_⟩
      rw [hmul, hrq', ← hX, ← hmul, mul_inv_cancel]
      exact (hact 1).2.1 e0
    · rintro q ⟨-, hq⟩
      have h1 := (hstab _).1 hq
      rw [hmul, hrq'] at h1
      have h2 := hinvact _ _ _ h1
      rw [hX] at h2
      exact Subtype.ext (hratinj h2).symm

  obtain ⟨⟨μ₁, hμ₁⟩, hall⟩ := hvol
  haveI : μ₁.IsHaarMeasure := hμ₁
  obtain ⟨𝓕₁, hm₁, hFD₁, hcov₁⟩ := ((GlobalTheory.T.haar_fundamental_domain_exists_unitary F E σ hσ M J hJ).2 μ₁ hμ₁).2.1
  have hfin : μ₁ 𝓕₁ < ⊤ := (hall μ₁ hμ₁).2 𝓕₁ hFD₁
  have key := mean_lt_top μ μ₁ ι hιc Γ Γ₁ hΓ 𝓕 h𝓕 𝓕₁ hm₁ hfin
    (fun u => by
      obtain ⟨γ, h1, h2⟩ := hcov₁ u
      exact ⟨γ, (hmemΓ₁ γ).2 h1, h2⟩)
    Q r hr hQ f hfm hf1 hinv C₀⁻¹ hC₀.inv hsupp
  have hrew : ∀ (h : HA (AF F) σ (blockOne (algebraMap F E t) J)) (q : Q), f (r q * h) =
      Set.indicator Ω (fun _ => (1 : ℝ≥0∞))
        (actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ (ratTup (AF F) q.1)) := by
    intro h q
    simp only [f]
    rw [mul_inv_rev, hmul, hrq']
  unfold cntI
  simp only [← hrew]
  exact key

end GlobalTheory.CompanionTheory.SW.Aniso
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_volume_block_one_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ t : F, t ≠ 0 → ∀ (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) (𝓕 : Set (HA (AF F) σ (blockOne (algebraMap F E t) J))), IsHaarH F E σ (M + 1) (blockOne (algebraMap F E t) J) μ → IsFDH F E σ (M + 1) (blockOne (algebraMap F E t) J) μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin (M + 1) → AF F ⊗[F] E), IsCompact Ω → cntI σ _ μ 𝓕 {X | gramE σ (blockOne (algebraMap F E t) J) X = fun _ _ => algebraMap F E t} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.Aniso.count_lt_top
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CountGen

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_eq_dot (σ : E →ₐ[F] E) {M : ℕ} (A : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hE σ A x y = ((σ : E →+* E) ∘ x) ⬝ᵥ (A *ᵥ y) := by
  simp [hE, hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hE_mulVec (σ : E →ₐ[F] E) {M : ℕ} (J g : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hE σ J (g *ᵥ x) (g *ᵥ y) = hE σ (cT (σ : E →+* E) g * J * g) x y := by
  have h1 : ((σ : E →+* E) ∘ (g *ᵥ x)) = (g.map (σ : E →+* E)) *ᵥ ((σ : E →+* E) ∘ x) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) g x i
  rw [hE_eq_dot, hE_eq_dot, h1, ← Matrix.mulVec_mulVec y (cT (σ : E →+* E) g * J) g,
    ← Matrix.mulVec_mulVec _ (cT (σ : E →+* E) g) J,
    Matrix.dotProduct_mulVec ((σ : E →+* E) ∘ x) (cT (σ : E →+* E) g) _]
  simp only [cT, Matrix.vecMul_transpose]

theorem gramE_mulVec (σ : E →ₐ[F] E) {M n : ℕ} (J g : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) :
    gramE σ J (fun a => g *ᵥ X a) = gramE σ (cT (σ : E →+* E) g * J * g) X := by
  funext a b
  exact hE_mulVec σ J g (X a) (X b)

end Alg

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem continuous_actTup (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    Continuous (actTup R g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actTup, Matrix.mulVec, dotProduct]
  exact continuous_finset_sum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

theorem isCompact_preimage_actTup (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E))
    {Ω : Set (Fin n → Fin M → R ⊗[F] E)} (hΩ : IsCompact Ω) :
    IsCompact (actTup R g ⁻¹' Ω) := by
  have h : actTup R g ⁻¹' Ω = actTup R g⁻¹ '' Ω := by
    ext X
    constructor
    · intro hX
      refine ⟨actTup R g X, hX, ?_⟩
      funext a
      simp [actTup, Matrix.mulVec_mulVec]
    · rintro ⟨Y, hY, rfl⟩
      have : actTup R g (actTup R g⁻¹ Y) = Y := by
        funext a
        simp [actTup, Matrix.mulVec_mulVec]
      simpa [Set.mem_preimage, this] using hY
  rw [h]
  exact hΩ.image (continuous_actTup R g⁻¹)

end Top

theorem finite_count : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ (M' : ℕ), M' < M → ∀ J' : Matrix (Fin M') (Fin M') E, IsHermND σ J' → FinVol F E σ M' J') → ∀ t : F, t ≠ 0 → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω → cntI σ J μ 𝓕 {X | gramE σ J X = fun _ _ => algebraMap F E t} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ hvol t ht μ 𝓕 hμ h𝓕 Ω hΩ
  by_cases hS : ∃ X : Fin 1 → Fin M → E, gramE σ J X = fun _ _ => algebraMap F E t
  · obtain ⟨X₀, hX₀⟩ := hS
    have hx : hE σ J (X₀ 0) (X₀ 0) = algebraMap F E t := congrFun (congrFun hX₀ 0) 0
    cases M with
    | zero =>
      exfalso
      have h0 : hE σ J (X₀ 0) (X₀ 0) = 0 := by simp [hE, hform]
      rw [h0] at hx
      exact ht ((map_eq_zero (algebraMap F E)).1 hx.symm)
    | succ M₁ =>
      obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
      have htop := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).1
      obtain ⟨g, J₁, hJ₁, hblock, -⟩ :=
        GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hcm M₁ J hJ t (X₀ 0) ht hx
      obtain ⟨μ', 𝓕', hμ', h𝓕', -, hcnt⟩ :=
        GlobalTheory.T.fundamental_domain_transport_congruent_form F E σ hcm (M₁ + 1) J hJ g _ hblock μ 𝓕 hμ h𝓕
      rw [hcnt 1 _ _]
      have hset : {X : Fin 1 → Fin (M₁ + 1) → E |
          (fun a => (g : Matrix (Fin (M₁ + 1)) (Fin (M₁ + 1)) E) *ᵥ X a) ∈
            {X : Fin 1 → Fin (M₁ + 1) → E | gramE σ J X = fun _ _ => algebraMap F E t}} =
          {X | gramE σ (blockOne (algebraMap F E t) J₁) X = fun _ _ => algebraMap F E t} := by
        ext X
        simp only [Set.mem_setOf_eq, gramE_mulVec, hblock]
      have hfun : (fun Y : Fin 1 → Fin (M₁ + 1) → AF F ⊗[F] E =>
          Set.indicator Ω (fun _ => (1 : ℝ≥0∞)) (actTup (AF F) (bc (inclR (AF F)) g) Y)) =
          Set.indicator (actTup (AF F) (bc (inclR (AF F)) g) ⁻¹' Ω) (fun _ => (1 : ℝ≥0∞)) := by
        funext Y
        by_cases hY : actTup (AF F) (bc (inclR (AF F)) g) Y ∈ Ω
        · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (Set.mem_preimage.2 hY)]
        · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (Set.mem_preimage.1 h))]
      rw [hset, hfun]
      exact GlobalTheory.T.finite_volume_block_one_extension F E σ hcm M₁ J₁ hJ₁ (hvol M₁ (Nat.lt_succ_self M₁) J₁ hJ₁) t ht μ' 𝓕' hμ' h𝓕' _
        (isCompact_preimage_actTup (AF F) _ hΩ)
  · have hemp : {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E t} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hS ⟨X, h⟩
    rw [hemp]
    simp [cntI]

end GlobalTheory.CompanionTheory.SW.CountGen
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_volume_induction_compact_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ (M' : ℕ), M' < M → ∀ J' : Matrix (Fin M') (Fin M') E, IsHermND σ J' → FinVol F E σ M' J') → ∀ t : F, t ≠ 0 → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω → cntI σ J μ 𝓕 {X | gramE σ J X = fun _ _ => algebraMap F E t} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SW.CountGen.finite_count | exact GlobalTheory.CompanionTheory.SW.CountGen.finite_count | (intros; apply GlobalTheory.CompanionTheory.SW.CountGen.finite_count <;> assumption)
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CntFin

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
  {μ : Measure (HA (AF F) σ J)} {𝓕 : Set (HA (AF F) σ J)}

theorem cntI_mono_fun {S : Set (Fin n → Fin M → E)}
    {Φ Ψ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞} (h : ∀ Y, Φ Y ≤ Ψ Y) :
    cntI σ J μ 𝓕 S Φ ≤ cntI σ J μ 𝓕 S Ψ :=
  lintegral_mono fun _ => ENNReal.tsum_le_tsum fun _ => h _

theorem cntI_le_of_contrib {S S' : Set (Fin n → Fin M → E)}
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞}
    (h : ∀ (g : HA (AF F) σ J) (X : Fin n → Fin M → E), X ∈ S →
      Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ≠ 0 → X ∈ S') :
    cntI σ J μ 𝓕 S Φ ≤ cntI σ J μ 𝓕 S' Φ := by
  refine lintegral_mono fun g => ?_
  rw [tsum_subtype S (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))),
    tsum_subtype S' (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)))]
  refine ENNReal.tsum_le_tsum fun X => ?_
  by_cases hX : X ∈ S
  · by_cases h0 : Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) = 0
    · simp [Set.indicator, h0]
    · simp [Set.indicator, hX, h g X hX h0]
  · simp [Set.indicator, hX]

theorem cntI_union_le [Countable E] {S S' : Set (Fin n → Fin M → E)}
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞}
    (hm : ∀ X : Fin n → Fin M → E,
      Measurable fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) :
    cntI σ J μ 𝓕 (S ∪ S') Φ ≤ cntI σ J μ 𝓕 S Φ + cntI σ J μ 𝓕 S' Φ := by
  unfold cntI
  rw [← lintegral_add_left (Measurable.ennreal_tsum fun X : S => hm X)]
  exact lintegral_mono fun g => ENNReal.tsum_union_le
    (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) S S'

end SlopeTestRemainingChoices

theorem cntI_nonzero_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M →
    ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 →
    ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω →
      cntI σ J μ 𝓕 {X | X ≠ 0} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM μ 𝓕 hH hFD Ω hΩ
  classical
  obtain ⟨⟨hAlc, hAsc, hAt2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hAlc
  haveI := hAsc
  haveI := hAt2
  obtain ⟨hTG, -, -, -, hBor, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := hTG
  haveI := hBor
  obtain ⟨-, -, -, hKt2, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hKt2
  haveI : Countable E :=
    ((Module.finBasis ℚ E).equivFun.toEquiv).injective.countable
  haveI : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hcl : IsClosed Ω := hΩ.isClosed
  set Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞ := Set.indicator Ω (fun _ => (1 : ℝ≥0∞)) with hΦ

  have hm : ∀ X : Fin 1 → Fin M → E,
      Measurable fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) := by
    intro X
    have hc : Continuous fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X) :=
      (hact 1).1.comp (continuous_inv.prodMk continuous_const)
    have hs : MeasurableSet ((fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ⁻¹' Ω) :=
      (hcl.preimage hc).measurableSet
    have he : (fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) =
        Set.indicator ((fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ⁻¹' Ω)
          (fun _ => (1 : ℝ≥0∞)) := by
      funext g
      by_cases hg : actW (AF F) σ J g⁻¹ (ratTup (AF F) X) ∈ Ω <;> simp [hΦ, Set.indicator, hg]
    rw [he]
    exact measurable_const.indicator hs

  have hzero : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} Φ < ⊤ := by
    obtain ⟨-, hbox, -⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM _ (Module.finBasis F E) 1 M
    obtain ⟨N, r, hN, hr, hsub⟩ := hbox Ω hΩ
    obtain ⟨C, hC⟩ := GlobalTheory.T.isotropic_vector_count_box_bound F E σ hCM M J hJ hM μ 𝓕 hH hFD _ (Module.finBasis F E) N hN
    refine lt_of_le_of_lt (le_trans (cntI_mono_fun fun Y => ?_) (hC r hr)) ENNReal.ofReal_lt_top
    exact Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le) Y

  have hlen : ∀ t : F, t ≠ 0 →
      cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E t} Φ < ⊤ := by
    intro t ht
    exact GlobalTheory.T.finite_volume_induction_compact_sum F E σ hCM M J hJ
      (fun M' _ J' hJ' => GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M' J' hJ') t ht μ 𝓕 hH hFD Ω hΩ

  have hfinset : ∀ T : Finset F, (∀ t ∈ T, t ≠ 0) →
      cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
        ∃ t ∈ T, gramE σ J X = fun _ _ => algebraMap F E t} Φ < ⊤ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      simpa using hzero
    | insert a T _ ih =>
      intro hT
      have hsub : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
          ∃ t ∈ insert a T, gramE σ J X = fun _ _ => algebraMap F E t} Φ ≤
          cntI σ J μ 𝓕 ({X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E a} ∪
            {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
              ∃ t ∈ T, gramE σ J X = fun _ _ => algebraMap F E t}) Φ := by
        refine cntI_le_of_contrib fun g X hX _ => ?_
        rcases hX with hX | ⟨t, ht, hX⟩
        · exact Or.inr (Or.inl hX)
        · rcases Finset.mem_insert.1 ht with rfl | ht'
          · exact Or.inl hX
          · exact Or.inr (Or.inr ⟨t, ht', hX⟩)
      refine lt_of_le_of_lt (hsub.trans (cntI_union_le hm)) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
      · exact hlen a (hT a (Finset.mem_insert_self a T))
      · exact ih fun t ht => hT t (Finset.mem_insert_of_mem ht)
  obtain ⟨hlenQ, hgram, hfin⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hCM M J hJ
  refine lt_of_le_of_lt ?_ (hfinset ((hfin Ω hΩ).toFinset.erase 0)
    fun t ht => (Finset.mem_erase.1 ht).1)
  refine cntI_le_of_contrib fun g X hX hne => ?_
  have hY : actW (AF F) σ J g⁻¹ (ratTup (AF F) X) ∈ Ω := by
    by_contra hY
    exact hne (by simp [hΦ, Set.indicator, hY])
  obtain ⟨t, ht⟩ := hlenQ X
  by_cases h0 : t = 0
  · refine Or.inl ⟨hX, ?_⟩
    rw [ht, h0]
    funext a b
    simp
  · refine Or.inr ⟨t, Finset.mem_erase.2 ⟨h0, ?_⟩, ht⟩
    refine (Set.Finite.mem_toFinset _).2 ⟨_, hY, ?_⟩
    rw [((hact 1).2.2.2 g⁻¹ (ratTup (AF F) X)), hgram 1 X, ht]
    funext a b
    rfl

end GlobalTheory.CompanionTheory.SW.CntFin
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_count_compact_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω → cntI σ J μ 𝓕 {X | X ≠ 0} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.CntFin.cntI_nonzero_lt_top
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CntLarge

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def orbitHom (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) :
    (Fin 1 → Fin M → E) →+ (Fin 1 → Fin M → AF F ⊗[F] E) where
  toFun X := actW (AF F) σ J h (ratTup (AF F) X)
  map_zero' := by
    funext a i
    simp [actW, actTup, ratTup, inclR, Matrix.mulVec, dotProduct]
  map_add' X Y := by
    funext a i
    simp [actW, actTup, ratTup, inclR, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib,
      TensorProduct.tmul_add]

theorem count_le (hpack : ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (Λ : Type) [AddCommGroup Λ]
      (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤
        ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) *
          ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l))
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) {r₀ r : ℝ} (h0 : 0 < r₀) (hr : r₀ ≤ r) :
    ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
        (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)))
          (actW (AF F) σ J h (ratTup (AF F) (X : Fin 1 → Fin M → E))) ≤
      ENNReal.ofReal ((5 * r / r₀) ^ (2 * Module.finrank ℚ F * M)) *
        (1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
          (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞)))
            (actW (AF F) σ J h (ratTup (AF F) (X : Fin 1 → Fin M → E)))) := by
  classical
  set e := orbitHom σ J h with he
  have key := hpack d b M (Fin 1 → Fin M → E) e N r₀ r h0 hr
  have hsplit : ∑' X : Fin 1 → Fin M → E, (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X) ≤
      1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
        (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X) := by
    rw [ENNReal.tsum_eq_add_tsum_ite (0 : Fin 1 → Fin M → E)]
    refine add_le_add (by rw [Set.indicator_apply]; split_ifs <;> simp) ?_
    rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
      (fun X => (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X))]
    refine le_of_eq (tsum_congr fun X => ?_)
    by_cases hX : X = 0 <;> simp [hX]
  have hle : ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
      (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X) ≤
      ∑' X : Fin 1 → Fin M → E, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X) := by
    rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
      (fun X => (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X))]
    exact ENNReal.tsum_le_tsum fun X => Set.indicator_le_self _ _ _
  exact hle.trans (key.trans (mul_le_mul_right hsplit _))

theorem cnt_large : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ) (r₀ : ℝ), 0 < N → 0 < r₀ → ∃ C : ℝ, ∀ r : ℝ, r₀ ≤ r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * M)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM μ 𝓕 hμ h𝓕 d b N r₀ hN h0
  have hvol : μ 𝓕 < ⊤ := ((finVol_unitaryGroup F E σ hσ M J hJ).2 μ hμ).2 𝓕 h𝓕
  have hcomp : IsCompact (box b N r₀ : Set (Fin 1 → Fin M → AF F ⊗[F] E)) :=
    (GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hσ d b 1 M).1 N r₀ hN
  have hcnt := GlobalTheory.T.theta_count_compact_finite F E σ hσ M J hJ hM μ 𝓕 hμ h𝓕 _ hcomp
  set B : ℝ≥0∞ := μ 𝓕 + cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
    (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) with hB
  have hBtop : B ≠ ⊤ := (ENNReal.add_lt_top.2 ⟨hvol, hcnt⟩).ne
  set k := 2 * Module.finrank ℚ F * M with hk
  refine ⟨(5 / r₀) ^ k * B.toReal, fun r hr => ?_⟩
  have hpt : ∀ h : HA (AF F) σ J, _ := fun h => count_le (fun d b M Λ _ e N r R => GlobalTheory.T.adelic_box_lattice_count_ratio F E σ hσ d b M Λ e N r R)
    σ J h⁻¹ b N h0 hr
  have hr0 : 0 ≤ r := h0.le.trans hr
  calc cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)))
      ≤ ∫⁻ h in 𝓕, ENNReal.ofReal ((5 * r / r₀) ^ k) *
          (1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
            (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞)))
              (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E)))) ∂μ :=
        lintegral_mono fun h => hpt h
    _ = ENNReal.ofReal ((5 * r / r₀) ^ k) * B := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const]
        simp [hB, cntI]
    _ = ENNReal.ofReal ((5 / r₀) ^ k * B.toReal * r ^ k) := by
        have : (5 / r₀) ^ k * B.toReal * r ^ k = (5 * r / r₀) ^ k * B.toReal := by
          rw [show 5 * r / r₀ = 5 / r₀ * r by ring, mul_pow]; ring
        rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hBtop]

end GlobalTheory.CompanionTheory.SW.CntLarge
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counting_vectors_bounded_large_radius : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ) (r₀ : ℝ), 0 < N → 0 < r₀ → ∃ C : ℝ, ∀ r : ℝ, r₀ ≤ r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * M)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.CntLarge.cnt_large
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_integral_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ Y, Φ Y ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * cntI σ J μ 𝓕 S Φ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaCnt.lintegral_thetaMeas | exact GlobalTheory.CompanionTheory.SW.ThetaCnt.lintegral_thetaMeas | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaCnt.lintegral_thetaMeas <;> assumption)
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MeanCount

theorem box_mono {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (N : ℕ) {r r' : ℝ} (h : r ≤ r') :
    (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆ box b N r' :=
  fun _ hX => ⟨hX.1, hX.2.trans h⟩

theorem real_bound {C₁ C₂ x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hxy : x ≤ y) :
    C₁ * x ≤ (|C₁| + |C₂|) * (y + z) := by
  have h1 := abs_nonneg C₁
  have h2 := abs_nonneg C₂
  calc C₁ * x ≤ |C₁| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx
    _ ≤ |C₁| * y := mul_le_mul_of_nonneg_left hxy h1
    _ ≤ (|C₁| + |C₂|) * (y + z) :=
        mul_le_mul (by linarith) (by linarith) hy (by linarith)

theorem mean_count_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r} ≤ ENNReal.ofReal (C * (r ^ (Module.finrank ℚ F * M) + r ^ (2 * Module.finrank ℚ F * M))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b μ 𝓕 hμ h𝓕 N hN
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  haveI := lcA
  haveI := scA
  haveI := t2A
  obtain ⟨-, -, -, t2K, -, -, -, borelK, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := t2K
  haveI := borelK 1 M
  have hact := (GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F))
  have hgram : ∀ (h : HA (AF F) σ J) (X : Fin 1 → Fin M → AF F ⊗[F] E),
      gramR (AF F) σ J (actW (AF F) σ J h X) = gramR (AF F) σ J X :=
    (hact.2.2.2.2.2 1).2.2.2
  obtain ⟨hfin1, hfin2, -⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hCM M J hJ
  have h0 : μ 𝓕 ≠ 0 := ((GlobalTheory.T.haar_fundamental_domain_exists_unitary F E σ hCM M J hJ).2 μ hμ).2.2 𝓕 h𝓕
  have hc : (μ 𝓕)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  obtain ⟨r₀, hr₀, hsmall⟩ := GlobalTheory.T.small_box_gram_scalar_zero F E σ hCM M J hJ d b N hN
  have hr₁ : 0 < min r₀ 1 := lt_min hr₀ one_pos
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.isotropic_vector_count_box_bound F E σ hCM M J hJ hM μ 𝓕 hμ h𝓕 d b N hN
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.counting_vectors_bounded_large_radius F E σ hCM M J hJ hM μ 𝓕 hμ h𝓕 d b N (min r₀ 1) hN hr₁
  refine ⟨((μ 𝓕)⁻¹).toReal * (|C₁| + |C₂|), fun r hr => ?_⟩
  change thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (box b N r) ≤ _
  have hmeas : MeasurableSet (box b N r : Set (Fin 1 → Fin M → AF F ⊗[F] E)) :=
    ((GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM d b 1 M).1 N r hN).measurableSet
  have hval : thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (box b N r) =
      (μ 𝓕)⁻¹ * cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
        (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) := by
    have h := GlobalTheory.T.theta_measure_integral_formula F E σ hCM M J hJ μ 𝓕 hμ h𝓕 1 {X : Fin 1 → Fin M → E | X ≠ 0}
      (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hmeas)
    rw [lintegral_indicator_const hmeas, one_mul] at h
    exact h
  have hx : 0 ≤ r ^ (Module.finrank ℚ F * M) := by positivity
  have hy : 0 ≤ r ^ (2 * Module.finrank ℚ F * M) := by positivity
  have hbound : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
      (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤
      ENNReal.ofReal ((|C₁| + |C₂|) * (r ^ (Module.finrank ℚ F * M) +
        r ^ (2 * Module.finrank ℚ F * M))) := by
    rcases le_total r (min r₀ 1) with hle | hle
    · have hrr₀ : r ≤ r₀ := hle.trans (min_le_left _ _)
      have hr1 : r ≤ 1 := hle.trans (min_le_right _ _)
      have hiso : ∀ (h : HA (AF F) σ J) (X : Fin 1 → Fin M → E),
          actW (AF F) σ J h⁻¹ (ratTup (AF F) X) ∈ (box b N r : Set (Fin 1 → Fin M → AF F ⊗[F] E)) →
          gramE σ J X = 0 := by
        intro h X hX
        obtain ⟨t, ht⟩ := hfin1 X
        have hY : gramR (AF F) σ J (actW (AF F) σ J h⁻¹ (ratTup (AF F) X)) =
            fun _ _ => inclR (AF F) (algebraMap F E t) := by
          rw [hgram, hfin2, ht]
          rfl
        have ht0 : t = 0 := hsmall t _ (box_mono b N hrr₀ hX) hY
        rw [ht, ht0]
        funext a c
        simp
      have heq : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
            (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) =
          cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0}
            (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) := by
        unfold cntI
        refine lintegral_congr fun h => ?_
        rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
            (fun X => Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))
              (actW (AF F) σ J h⁻¹ (ratTup (AF F) X))),
          tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0}
            (fun X => Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))
              (actW (AF F) σ J h⁻¹ (ratTup (AF F) X)))]
        congr 1
        funext X
        by_cases hB : actW (AF F) σ J h⁻¹ (ratTup (AF F) X) ∈
            (box b N r : Set (Fin 1 → Fin M → AF F ⊗[F] E))
        · have hg := hiso h X hB
          by_cases hX : X ≠ 0
          · rw [Set.indicator_of_mem (show X ∈ {X : Fin 1 → Fin M → E | X ≠ 0} from hX),
              Set.indicator_of_mem
                (show X ∈ {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} from ⟨hX, hg⟩)]
          · rw [Set.indicator_of_notMem (show X ∉ {X : Fin 1 → Fin M → E | X ≠ 0} from hX),
              Set.indicator_of_notMem
                (show X ∉ {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} from fun h' => hX h'.1)]
        · simp only [Set.indicator, hB, if_false, ite_self]
      rw [heq]
      refine (hC₁ r hr).trans (ENNReal.ofReal_le_ofReal ?_)
      have hexp : Module.finrank ℚ F * M ≤ 2 * Module.finrank ℚ F * (M - 1) := by
        have h2 : M ≤ 2 * (M - 1) := by omega
        calc Module.finrank ℚ F * M ≤ Module.finrank ℚ F * (2 * (M - 1)) :=
              Nat.mul_le_mul_left _ h2
          _ = 2 * Module.finrank ℚ F * (M - 1) := by ring
      exact real_bound (by positivity) hx hy (pow_le_pow_of_le_one hr.le hr1 hexp)
    · refine (hC₂ r hle).trans (ENNReal.ofReal_le_ofReal ?_)
      have := real_bound (C₁ := C₂) (C₂ := C₁) hy hy hx le_rfl
      rw [add_comm |C₂|, add_comm (r ^ (2 * Module.finrank ℚ F * M))] at this
      exact this
  rw [hval, mul_assoc, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]
  exact mul_le_mul_right hbound _

end GlobalTheory.CompanionTheory.SW.MeanCount
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_nonzero_vectors_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r} ≤ ENNReal.ofReal (C * (r ^ (Module.finrank ℚ F * M) + r ^ (2 * Module.finrank ℚ F * M))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.MeanCount.mean_count_box
end
