import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsSatFlagOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryIwasawaIntegrationFormulaRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIntegralPointsCovolume
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSaturatedIsotropicFlagOfAdaptedBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTotallyIsotropicFlagComplexifiedSaturatedFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGaugeMeasuresIsotropicFlagParabolicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorIntegralModIntegralPointsLe
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_unitary_isotropicFlag : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∀ g : Formalism.REAL.UJ ε, ∃ u ∈ flagN ε W, ∃ m ∈ flagM ε W, ∃ k ∈ maxK ε, g = u * m * k) ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, u * m ∈ maxK ε → u = 1 := by
  first | exact @GlobalTheory.RealIwasawa.iwasawa | exact GlobalTheory.RealIwasawa.iwasawa | (intros; apply GlobalTheory.RealIwasawa.iwasawa <;> assumption)
end

section
section
open MeasureTheory

namespace GlobalTheory

open Filter Topology

theorem exists_measurable_invariant_index {G : Type} [Group G] [MetricSpace G]
    [ContinuousMul G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G) (y : ℕ → G)
    (r : ℝ) (Q : ℕ → G → Prop) (hQm : ∀ n, MeasurableSet {x | Q n x})
    (hQi : ∀ n, ∀ l ∈ L, ∀ x, Q n (l * x) ↔ Q n x)
    (hex : ∀ x, ∃ n, (∃ l ∈ L, dist (y n) (l * x) < r) ∧ Q n x) :
    ∃ s : G → ℕ, Measurable s ∧ (∀ x, ∃ l ∈ L, dist (y (s x)) (l * x) < r) ∧
      (∀ l ∈ L, ∀ x, s (l * x) = s x) ∧ ∀ x, Q (s x) x := by
  classical
  have hPm : ∀ n, MeasurableSet {x : G | (∃ l ∈ L, dist (y n) (l * x) < r) ∧ Q n x} := by
    intro n
    have hset : {x : G | ∃ l ∈ L, dist (y n) (l * x) < r} =
        ⋃ l : L, {x : G | dist (y n) ((l : G) * x) < r} := by
      ext x; simp
    have hopen : IsOpen {x : G | ∃ l ∈ L, dist (y n) (l * x) < r} := by
      rw [hset]
      exact isOpen_iUnion fun l =>
        isOpen_lt (continuous_const.dist (continuous_const.mul continuous_id)) continuous_const
    exact hopen.measurableSet.inter (hQm n)
  have hinv : ∀ l ∈ L, ∀ x n, ((∃ l' ∈ L, dist (y n) (l' * (l * x)) < r) ∧ Q n (l * x)) ↔
      ((∃ l' ∈ L, dist (y n) (l' * x) < r) ∧ Q n x) := by
    intro l hl x n
    refine and_congr ⟨?_, ?_⟩ (hQi n l hl x)
    · rintro ⟨m, hm, hd⟩
      exact ⟨m * l, L.mul_mem hm hl, by rwa [mul_assoc]⟩
    · rintro ⟨m, hm, hd⟩
      refine ⟨m * l⁻¹, L.mul_mem hm (L.inv_mem hl), ?_⟩
      simpa [mul_assoc] using hd
  refine ⟨fun x => Nat.find (hex x), measurable_find hex hPm, fun x => (Nat.find_spec (hex x)).1,
    fun l hl x => ?_, fun x => (Nat.find_spec (hex x)).2⟩
  exact le_antisymm (Nat.find_min' _ ((hinv l hl x _).2 (Nat.find_spec (hex x))))
    (Nat.find_min' _ ((hinv l hl x _).1 (Nat.find_spec (hex (l * x)))))

theorem exists_measurable_coset_section_metric {G : Type} [Group G] [MetricSpace G]
    [CompleteSpace G] [SecondCountableTopology G]
    [ContinuousMul G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : ℕ → G, DenseRange y := TopologicalSpace.exists_dense_seq G
  let S : ℕ → Type := fun k => {s : G → ℕ // Measurable s ∧ (∀ l ∈ L, ∀ x, s (l * x) = s x) ∧
    ∀ x, ∃ l ∈ L, dist (y (s x)) (l * x) < (1 / 2 : ℝ) ^ k}
  have hy_meas : ∀ s : G → ℕ, Measurable s → Measurable (fun x => y (s x)) :=
    fun s hs => measurable_from_nat.comp hs

  have h0 : Nonempty (S 0) := by
    obtain ⟨s, hs, hclose, hinv, -⟩ := exists_measurable_invariant_index L y 1 (fun _ _ => True)
      (fun _ => MeasurableSet.univ) (fun _ _ _ _ => Iff.rfl) (fun x => by
        obtain ⟨n, hn⟩ := hy.exists_dist_lt x one_pos
        exact ⟨n, ⟨1, L.one_mem, by rw [one_mul, dist_comm]; exact hn⟩, trivial⟩)
    exact ⟨⟨s, hs, hinv, fun x => by simpa using hclose x⟩⟩

  have hstep : ∀ k (s : S k), ∃ s' : S (k + 1),
      ∀ x, dist (y (s'.1 x)) (y (s.1 x)) < 2 * (1 / 2 : ℝ) ^ k := by
    intro k s
    obtain ⟨s, hsm, hsi, hsc⟩ := s
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 1) := by positivity
    have hhalf : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2 := by ring
    obtain ⟨s', hs'm, hclose, hinv, hQ⟩ := exists_measurable_invariant_index L y ((1 / 2 : ℝ) ^ (k + 1))
      (fun n x => dist (y n) (y (s x)) < 2 * (1 / 2 : ℝ) ^ k)
      (fun n => measurableSet_lt (measurable_const.dist (hy_meas s hsm)) measurable_const)
      (fun n l hl x => by simp only [hsi l hl x])
      (fun x => by
        obtain ⟨l, hl, hd⟩ := hsc x
        obtain ⟨n, hn⟩ := hy.exists_dist_lt (l * x) hpos
        refine ⟨n, ⟨l, hl, by rw [dist_comm]; exact hn⟩, ?_⟩
        have hk : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
        calc dist (y n) (y (s x)) ≤ dist (y n) (l * x) + dist (l * x) (y (s x)) := dist_triangle _ _ _
          _ < 2 * (1 / 2 : ℝ) ^ k := by
            rw [hhalf] at hn
            have e1 := dist_comm (y n) (l * x)
            have e2 := dist_comm (l * x) (y (s x))
            linarith)
    exact ⟨⟨s', hs'm, hinv, hclose⟩, hQ⟩
  choose step hstep using hstep
  let seq : (k : ℕ) → S k := fun k => Nat.rec (motive := S) h0.some (fun k s => step k s) k
  let f : ℕ → G → G := fun k x => y ((seq k).1 x)
  have hf_succ : ∀ k x, dist (f k x) (f (k + 1) x) ≤ 2 * (1 / 2 : ℝ) ^ k := fun k x => by
    rw [dist_comm]; exact (hstep k (seq k) x).le
  have hcauchy : ∀ x, CauchySeq (fun k => f k x) := fun x =>
    cauchySeq_of_le_geometric (1 / 2 : ℝ) 2 (by norm_num) (hf_succ · x)
  choose σ hσ using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨σ, ?_, ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable (fun k => hy_meas _ (seq k).2.1) (tendsto_pi_nhds.2 hσ)
  · intro x
    have hC : IsClosed {z : G | z * x⁻¹ ∈ L} := hL.preimage (continuous_id.mul continuous_const)
    suffices h : σ x ∈ closure {z : G | z * x⁻¹ ∈ L} by rwa [hC.closure_eq] at h
    rw [Metric.mem_closure_iff]
    intro ε hε
    have h1 : ∀ᶠ k in atTop, dist (f k x) (σ x) < ε / 2 :=
      (hσ x).eventually (Metric.ball_mem_nhds _ (half_pos hε))
    have h2 : ∀ᶠ k in atTop, (1 / 2 : ℝ) ^ k < ε / 2 :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
        (gt_mem_nhds (half_pos hε))
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    obtain ⟨l, hl, hd⟩ := (seq k).2.2.2 x
    refine ⟨l * x, by simpa using hl, ?_⟩
    calc dist (σ x) (l * x) ≤ dist (σ x) (f k x) + dist (f k x) (l * x) := dist_triangle _ _ _
      _ < ε := by rw [dist_comm] at hk1; change dist (f k x) (l * x) < _ at hd; linarith
  · intro l hl x
    have hfx : (fun k => f k (l * x)) = fun k => f k x := by
      funext k; simp only [f, (seq k).2.2.1 l hl x]
    have := hσ (l * x)
    rw [hfx] at this
    exact tendsto_nhds_unique this (hσ x)

theorem exists_measurable_coset_section (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable G
  exact exists_measurable_coset_section_metric L hL

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_coset_section' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G), IsClosed (L : Set G) → ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  atlas_forward_decl GlobalTheory.exists_measurable_coset_section
end

section
section
open MeasureTheory

namespace GlobalTheory

theorem exists_measurableSet_slice_of_transversal
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (σ : G → G)
    (hN : MeasurableSet (N : Set G)) (hM : MeasurableSet (M : Set G))
    (hK : MeasurableSet (K : Set G)) (hσ : Measurable σ)
    (h1 : ∀ x, σ x * x⁻¹ ∈ K ⊓ M) (h2 : ∀ l ∈ K ⊓ M, ∀ x, σ (l * x) = σ x)
    (h3 : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N)
    (h4 : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1)
    (DN DM : Set G) (hDN : MeasurableSet DN) (hDM : MeasurableSet DM) :
    ∃ D : Set G, MeasurableSet D ∧ ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K,
      (u * m * k ∈ D ↔ u ∈ DN ∧ m * (k * (σ k)⁻¹) ∈ DM) := by
  have uniq : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, σ k = k → ∀ u' ∈ N, ∀ m' ∈ M, ∀ k' ∈ K, σ k' = k' →
      u * m * k = u' * m' * k' → u = u' ∧ m = m' ∧ k = k' := by
    intro u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h
    have e : k = m⁻¹ * u⁻¹ * (u' * m' * k') := by rw [← h]; group
    have e1 : (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * (m⁻¹ * m') = k * k'⁻¹ := by rw [e]; group
    have hkk : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
    have hmm : m⁻¹ * m' ∈ M := M.mul_mem (M.inv_mem hm) hm'
    have e2 := h4 _ (h3 _ (M.inv_mem hm) _ (N.mul_mem (N.inv_mem hu) hu')) _ hmm (e1 ▸ hkk)
    have huu : u = u' := by
      have : u' = u * (m * (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * m⁻¹) := by group
      rw [this, e2]; group
    rw [e2, one_mul] at e1
    have e3 := h2 (k * k'⁻¹) ⟨hkk, e1 ▸ hmm⟩ k'
    rw [inv_mul_cancel_right, hs, hs'] at e3
    subst huu e3
    exact ⟨rfl, mul_left_cancel (mul_right_cancel h), rfl⟩
  let X : Set (G × G × G) := (DN ∩ N) ×ˢ ((DM ∩ M) ×ˢ ((K : Set G) ∩ {k | σ k = k}))
  have hX : MeasurableSet X :=
    (hDN.inter hN).prod ((hDM.inter hM).prod
      (hK.inter (measurableSet_eq_fun hσ measurable_id)))
  let f : G × G × G → G := fun p => p.1 * p.2.1 * p.2.2
  have hf : Continuous f := by fun_prop
  have hinj : Set.InjOn f X := by
    rintro ⟨u, m, k⟩ ⟨⟨_, hu⟩, ⟨_, hm⟩, hk, hs⟩ ⟨u', m', k'⟩ ⟨⟨_, hu'⟩, ⟨_, hm'⟩, hk', hs'⟩ h
    obtain ⟨a, b, c⟩ := uniq u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h
    rw [a, b, c]
  refine ⟨f '' X, hX.image_of_continuousOn_injOn hf.continuousOn hinj, ?_⟩
  intro u hu m hm k hk
  have hl := h1 k
  have hl' : k * (σ k)⁻¹ ∈ K ⊓ M := by
    have := (K ⊓ M).inv_mem hl
    simpa using this
  have hσK : σ k ∈ K := by
    have := K.mul_mem hl.1 hk
    simpa using this
  have hσσ : σ (σ k) = σ k := by
    have := h2 _ hl k
    simpa using this
  have hm2 : m * (k * (σ k)⁻¹) ∈ M := M.mul_mem hm hl'.2
  have e : u * m * k = u * (m * (k * (σ k)⁻¹)) * σ k := by group
  constructor
  · rintro ⟨⟨u', m', k'⟩, ⟨⟨hdu, hu'⟩, ⟨hdm, hm'⟩, hk', hs'⟩, h⟩
    obtain ⟨a, b, _⟩ := uniq u hu _ hm2 _ hσK hσσ u' hu' m' hm' k' hk' hs' (e.symm.trans h.symm)
    rw [b, a]
    exact ⟨hdu, hdm⟩
  · rintro ⟨hdu, hdm⟩
    exact ⟨(u, m * (k * (σ k)⁻¹), σ k), ⟨⟨hdu, hu⟩, ⟨hdm, hm2⟩, hσK, hσσ⟩, e.symm⟩

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_iwasawa_slice_of_transversal : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (σ : G → G), MeasurableSet (N : Set G) → MeasurableSet (M : Set G) → MeasurableSet (K : Set G) → Measurable σ → (∀ x, σ x * x⁻¹ ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, ∀ x, σ (l * x) = σ x) → (∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N) → (∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1) → ∀ DN DM : Set G, MeasurableSet DN → MeasurableSet DM → ∃ D : Set G, MeasurableSet D ∧ ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, (u * m * k ∈ D ↔ u ∈ DN ∧ m * (k * (σ k)⁻¹) ∈ DM) := by
  atlas_forward_decl GlobalTheory.exists_measurableSet_slice_of_transversal
end

section
section
open MeasureTheory

namespace GlobalTheory

theorem iwasawa_slice_lintegral_le :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (N M K : Subgroup G) (μN μM μK : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] (δ : G → ENNReal) (κ : G → G) (D DN DM : Set G), Measurable δ → Measurable κ → MeasurableSet DN → MeasurableSet DM → μN (N : Set G)ᶜ = 0 → μM (M : Set G)ᶜ = 0 → μK (K : Set G)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ K, κ k ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, μM.map (fun g => g * l) = μM) → (∀ l ∈ K ⊓ M, ∀ m ∈ M, δ (m * l) = δ m) → (∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, u * m * k ∈ D → u ∈ DN ∧ m * κ k ∈ DM) → ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM ∂μN ≤ μN DN * ∫⁻ m in DM, δ m ∂μM := by
  intro G _ _ _ N M K μN μM μK _ _ _ δ κ D DN DM hδ hκ hDN hDM hN hM hK hK1 hκK hinv hδinv hD
  have aeM : ∀ᵐ m ∂μM, m ∈ (M : Set G) := mem_ae_iff.2 hM
  have aeK : ∀ᵐ k ∂μK, k ∈ (K : Set G) := mem_ae_iff.2 hK
  have aeN : ∀ᵐ u ∂μN, u ∈ (N : Set G) := mem_ae_iff.2 hN

  have htrans : ∀ l ∈ K ⊓ M,
      ∫⁻ m, δ m * DM.indicator (1 : G → ENNReal) (m * l) ∂μM = ∫⁻ m in DM, δ m ∂μM := by
    intro l hl
    have hfun : (fun m => δ m * DM.indicator (1 : G → ENNReal) (m * l))
        =ᵐ[μM] fun m => DM.indicator δ (m * l) := by
      filter_upwards [aeM] with m hm
      have hδml := hδinv l hl m hm
      by_cases hml : m * l ∈ DM
      · simp [hml, hδml]
      · simp [hml]
    rw [lintegral_congr_ae hfun, ← lintegral_map (hδ.indicator hDM) (measurable_mul_const l),
      hinv l hl, lintegral_indicator hDM]

  have hF : Measurable (Function.uncurry
      (fun (m k : G) => δ m * DM.indicator (1 : G → ENNReal) (m * κ k))) :=
    (hδ.comp measurable_fst).mul
      ((measurable_one.indicator hDM).comp (measurable_fst.mul (hκ.comp measurable_snd)))

  have hinner : ∀ u ∈ (N : Set G),
      ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
        ≤ DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u := by
    intro u hu
    by_cases huD : u ∈ DN
    · rw [Set.indicator_of_mem huD]
      calc ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
          ≤ ∫⁻ m, δ m * ∫⁻ k, DM.indicator (1 : G → ENNReal) (m * κ k) ∂μK ∂μM := by
            apply lintegral_mono_ae
            filter_upwards [aeM] with m hm
            gcongr δ m * ?_
            apply lintegral_mono_ae
            filter_upwards [aeK] with k hk
            by_cases hmem : u * m * k ∈ D
            · have h2 := (hD u hu m hm k hk hmem).2
              simp [hmem, h2]
            · simp [hmem]
        _ = ∫⁻ m, ∫⁻ k, δ m * DM.indicator (1 : G → ENNReal) (m * κ k) ∂μK ∂μM := by
            apply lintegral_congr
            intro m
            have hmeas : Measurable (fun k => DM.indicator (1 : G → ENNReal) (m * κ k)) :=
              (measurable_one.indicator hDM).comp (measurable_const.mul hκ)
            exact (lintegral_const_mul (δ m) hmeas).symm
        _ = ∫⁻ k, ∫⁻ m, δ m * DM.indicator (1 : G → ENNReal) (m * κ k) ∂μM ∂μK :=
            lintegral_lintegral_swap hF.aemeasurable
        _ = ∫⁻ _k, ∫⁻ m in DM, δ m ∂μM ∂μK := by
            apply lintegral_congr_ae
            filter_upwards [aeK] with k hk
            exact htrans (κ k) (hκK k hk)
        _ = ∫⁻ m in DM, δ m ∂μM := by
            rw [lintegral_const, hK1, mul_one]
    · have hind : DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u = 0 := by
        simp [huD]
      rw [hind]
      calc ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
          ≤ ∫⁻ _m, (0 : ENNReal) ∂μM := by
            apply lintegral_mono_ae
            filter_upwards [aeM] with m hm
            have hae : (fun k => D.indicator (1 : G → ENNReal) (u * m * k))
                =ᵐ[μK] fun _ => (0 : ENNReal) := by
              filter_upwards [aeK] with k hk
              have hmem : u * m * k ∉ D := fun h => huD (hD u hu m hm k hk h).1
              simp [hmem]
            rw [lintegral_congr_ae hae, lintegral_zero, mul_zero]
        _ = 0 := lintegral_zero
  calc ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM ∂μN
      ≤ ∫⁻ u, DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u ∂μN := by
        apply lintegral_mono_ae
        filter_upwards [aeN] with u hu
        exact hinner u hu
    _ = μN DN * ∫⁻ m in DM, δ m ∂μM := by
        rw [lintegral_indicator hDN, setLIntegral_const]
        exact mul_comm _ _

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_slice_indicator_lintegral_le : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (N M K : Subgroup G) (μN μM μK : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] (δ : G → ENNReal) (κ : G → G) (D DN DM : Set G), Measurable δ → Measurable κ → MeasurableSet DN → MeasurableSet DM → μN (N : Set G)ᶜ = 0 → μM (M : Set G)ᶜ = 0 → μK (K : Set G)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ K, κ k ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, μM.map (fun g => g * l) = μM) → (∀ l ∈ K ⊓ M, ∀ m ∈ M, δ (m * l) = δ m) → (∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, u * m * k ∈ D → u ∈ DN ∧ m * κ k ∈ DM) → ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM ∂μN ≤ μN DN * ∫⁻ m in DM, δ m ∂μM := by
  atlas_forward_decl GlobalTheory.iwasawa_slice_lintegral_le
end

section
section
open MeasureTheory

namespace GlobalTheory.NMKProd

theorem lintegral_nmk {H : Type} [Mul H] [MeasurableSpace H] [MeasurableMul₂ H]
    (a b k : Measure H) [SFinite a] [SFinite b] [SFinite k] (d : H → ENNReal) (hd : Measurable d)
    (φ : H → ENNReal) (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂(((a.prod (b.prod k)).withDensity fun x => d x.2.1).map
        fun x : H × H × H => x.1 * x.2.1 * x.2.2) =
      ∫⁻ u, ∫⁻ m, d m * ∫⁻ z, φ (u * m * z) ∂k ∂b ∂a := by
  have hmul : Measurable (fun x : H × H × H => x.1 * x.2.1 * x.2.2) :=
    (measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd
  have hD : Measurable (fun x : H × H × H => d x.2.1) := hd.comp measurable_snd.fst
  have hφm : Measurable (fun x : H × H × H => φ (x.1 * x.2.1 * x.2.2)) := hφ.comp hmul
  rw [lintegral_map hφ hmul, lintegral_withDensity_eq_lintegral_mul _ hD hφm,
    lintegral_prod _ (hD.mul hφm).aemeasurable]
  refine lintegral_congr fun u => ?_
  have hin : Measurable (fun y : H × H => d y.1 * φ (u * y.1 * y.2)) :=
    (hd.comp measurable_fst).mul (hφ.comp ((measurable_const.mul measurable_fst).mul measurable_snd))
  simp only [Pi.mul_apply]
  rw [lintegral_prod _ hin.aemeasurable]
  refine lintegral_congr fun m => ?_
  have hz : Measurable (fun z : H => φ (u * m * z)) := hφ.comp (measurable_id.const_mul (u * m))
  exact lintegral_const_mul (d m) hz

private lemma indicator_pi_univ_eq_prod {ι : Type} [Fintype ι] {G : ι → Type} (s : ∀ i, Set (G i))
    (x : ∀ i, G i) :
    (Set.univ.pi s).indicator (1 : (∀ i, G i) → ENNReal) x =
      ∏ i, (s i).indicator (1 : G i → ENNReal) (x i) := by
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    rw [Set.mem_univ_pi] at hx
    simp [Set.indicator_of_mem (hx _)]
  · rw [Set.indicator_of_notMem hx]
    rw [Set.mem_univ_pi, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem prod_formula : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul₂ (G i)] (μ μN μM μK : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μN i)] [∀ i, SigmaFinite (μM i)] [∀ i, SigmaFinite (μK i)] (C c : ι → ENNReal) (δ : ∀ i, G i → ENNReal), (∀ i, C i ≠ 0) → (∀ i, C i ≠ ⊤) → (∀ i, Measurable (δ i)) → (∀ i, ∀ φ : G i → ENNReal, Measurable φ → C i * ∫⁻ g, φ g ∂(μ i) = c i * ∫⁻ u, ∫⁻ m, δ i m * ∫⁻ k, φ (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i)) → ∀ φ : (∀ i, G i) → ENNReal, Measurable φ → (∏ i, C i) * ∫⁻ g, φ g ∂(Measure.pi μ) = (∏ i, c i) * ∫⁻ u, ∫⁻ m, (∏ i, δ i (m i)) * ∫⁻ k, φ (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) ∂(Measure.pi μN) := by
  intro ι _ G _ _ _ μ μN μM μK _ _ _ _ C c δ hC0 hCt hδ hrel φ hφ
  have hD : Measurable (fun m : ∀ i, G i => ∏ i, δ i (m i)) :=
    Finset.measurable_prod _ (fun i _ => (hδ i).comp (measurable_pi_apply i))
  have key := fun (ψ : (∀ i, G i) → ENNReal) (hψ : Measurable ψ) =>
    lintegral_nmk (Measure.pi μN) (Measure.pi μM) (Measure.pi μK)
      (fun m : ∀ i, G i => ∏ i, δ i (m i)) hD ψ hψ
  set R0 := (((Measure.pi μN).prod ((Measure.pi μM).prod (Measure.pi μK))).withDensity
      fun x => ∏ i, δ i (x.2.1 i)).map
    (fun x : (∀ i, G i) × (∀ i, G i) × (∀ i, G i) => x.1 * x.2.1 * x.2.2) with hR0
  have hC0' : (∏ i, C i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hC0 i
  have hCt' : (∏ i, C i) ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hCt i
  have hpi : Measure.pi μ = (∏ i, C i)⁻¹ • ((∏ i, c i) • R0) := by
    refine Measure.pi_eq fun s hs => ?_
    have hX : ∀ i, C i * μ i (s i) = c i * ∫⁻ u, ∫⁻ m, δ i m *
        ∫⁻ k, (s i).indicator 1 (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i) := by
      intro i
      have h := hrel i ((s i).indicator 1) (measurable_one.indicator (hs i))
      rwa [lintegral_indicator_one (hs i)] at h
    have hbox : R0 (Set.univ.pi s) = ∏ i, ∫⁻ u, ∫⁻ m, δ i m *
        ∫⁻ k, (s i).indicator 1 (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i) := by
      rw [← lintegral_indicator_one (MeasurableSet.univ_pi hs),
        key _ (measurable_one.indicator (MeasurableSet.univ_pi hs))]
      have hK : ∀ u m : ∀ i, G i, ∫⁻ k, (Set.univ.pi s).indicator 1 (u * m * k) ∂(Measure.pi μK) =
          ∏ i, ∫⁻ k, (s i).indicator 1 (u i * m i * k) ∂(μK i) := by
        intro u m
        simp_rw [indicator_pi_univ_eq_prod]
        exact GlobalTheory.SnMass.Push.lintegral_fintype_prod (fun i k => (s i).indicator 1 (u i * m i * k))
          (fun i => (measurable_one.indicator (hs i)).comp (measurable_const.mul measurable_id))
      have hA : ∀ i (u' : G i), Measurable (fun m' : G i =>
          δ i m' * ∫⁻ k, (s i).indicator 1 (u' * m' * k) ∂(μK i)) := by
        intro i u'
        refine (hδ i).mul ?_
        exact Measurable.lintegral_prod_right' (f := fun y : G i × G i => (s i).indicator 1 (u' * y.1 * y.2))
          ((measurable_one.indicator (hs i)).comp ((measurable_const.mul measurable_fst).mul measurable_snd))
      have hB : ∀ i, Measurable (fun u' : G i => ∫⁻ m', δ i m' *
          ∫⁻ k, (s i).indicator 1 (u' * m' * k) ∂(μK i) ∂(μM i)) := by
        intro i
        refine Measurable.lintegral_prod_right' (f := fun y : G i × G i =>
          δ i y.2 * ∫⁻ k, (s i).indicator 1 (y.1 * y.2 * k) ∂(μK i)) ?_
        refine ((hδ i).comp measurable_snd).mul ?_
        exact Measurable.lintegral_prod_right' (f := fun z : (G i × G i) × G i =>
            (s i).indicator 1 (z.1.1 * z.1.2 * z.2))
          ((measurable_one.indicator (hs i)).comp
            ((measurable_fst.fst.mul measurable_fst.snd).mul measurable_snd))
      have hM : ∀ u : ∀ i, G i, ∫⁻ m, (∏ i, δ i (m i)) *
          ∫⁻ k, (Set.univ.pi s).indicator 1 (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) =
          ∏ i, ∫⁻ m', δ i m' * ∫⁻ k, (s i).indicator 1 (u i * m' * k) ∂(μK i) ∂(μM i) := by
        intro u
        simp_rw [hK u, ← Finset.prod_mul_distrib]
        exact GlobalTheory.SnMass.Push.lintegral_fintype_prod
          (fun i m' => δ i m' * ∫⁻ k, (s i).indicator 1 (u i * m' * k) ∂(μK i)) (fun i => hA i (u i))
      simp_rw [hM]
      exact GlobalTheory.SnMass.Push.lintegral_fintype_prod _ hB
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [hbox, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ => (hX i).symm,
      Finset.prod_mul_distrib, ← mul_assoc, ENNReal.inv_mul_cancel hC0' hCt', one_mul]
  rw [hpi, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hC0' hCt', one_mul, hR0]
  exact congrArg ((∏ i, c i) * ·) (key φ hφ)

end GlobalTheory.NMKProd
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawaNMKIntegration_pi_product : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul₂ (G i)] (μ μN μM μK : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μN i)] [∀ i, SigmaFinite (μM i)] [∀ i, SigmaFinite (μK i)] (C c : ι → ENNReal) (δ : ∀ i, G i → ENNReal), (∀ i, C i ≠ 0) → (∀ i, C i ≠ ⊤) → (∀ i, Measurable (δ i)) → (∀ i, ∀ φ : G i → ENNReal, Measurable φ → C i * ∫⁻ g, φ g ∂(μ i) = c i * ∫⁻ u, ∫⁻ m, δ i m * ∫⁻ k, φ (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i)) → ∀ φ : (∀ i, G i) → ENNReal, Measurable φ → (∏ i, C i) * ∫⁻ g, φ g ∂(Measure.pi μ) = (∏ i, c i) * ∫⁻ u, ∫⁻ m, (∏ i, δ i (m i)) * ∫⁻ k, φ (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) ∂(Measure.pi μN) := by
  atlas_forward_decl GlobalTheory.NMKProd.prod_formula
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_flagLocalSizes_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (i : Fin a), Measurable fun g : Formalism.REAL.UJ ε => locSize j W (uMat g) i := by
  first | exact @GlobalTheory.FlagMeas.measurable_locSize_uMat | exact GlobalTheory.FlagMeas.measurable_locSize_uMat | (intros; apply GlobalTheory.FlagMeas.measurable_locSize_uMat <;> assumption)
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRiemannianHaarOnSubgroup_map_mul_right_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (M : Set (Formalism.REAL.UJ ε)) → IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ → ∀ l ∈ M, l ∈ maxK ε → μ.map (fun g => g * l) = μ := by
  first | exact @GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right | exact GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right | (intros; apply GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right <;> assumption)
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagUnipotentRadical_closed_subgroup_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∃ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = flagN ε W) ∧ IsClosed (flagN ε W) ∧ ∀ u ∈ flagN ε W, ∀ i, ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  first | exact @GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps | exact GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps | (intros; apply GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps <;> assumption)
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagLevi_maxCompact_closed_subgroups : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∃ M : Subgroup (Formalism.REAL.UJ ε), (M : Set (Formalism.REAL.UJ ε)) = flagM ε W) ∧ IsClosed (flagM ε W) ∧ (∃ K : Subgroup (Formalism.REAL.UJ ε), (K : Set (Formalism.REAL.UJ ε)) = maxK ε) ∧ IsClosed (maxK ε) ∧ ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W := by
  first | exact @GlobalTheory.FlagLeviGroup.levi_compact_subgroups | exact GlobalTheory.FlagLeviGroup.levi_compact_subgroups | (intros; apply GlobalTheory.FlagLeviGroup.levi_compact_subgroups <;> assumption)
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagSizeInv

open GlobalTheory.PointEquivariance

theorem mem_span_of_image {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (s : Set (Fin n → E)) (z : Fin n → E)
    (h : (fun l => φ (z l)) ∈ Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s)) :
    z ∈ Submodule.span E s := by
  by_contra hz
  obtain ⟨f, hfz, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
  have hf0 : ∀ y ∈ s, f y = 0 := fun y hy => by
    have hm : f y ∈ (Submodule.span E s).map f := Submodule.mem_map_of_mem (Submodule.subset_span hy)
    rw [hf] at hm
    simpa using hm
  have hfx : ∀ y : Fin n → E, f y = ∑ l, y l * f (fun j => if l = j then 1 else 0) := fun y => by
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    simp only [smul_eq_mul]
  let F : (Fin n → ℂ) →ₗ[ℂ] ℂ := ∑ l, φ (f (fun j => if l = j then 1 else 0)) • LinearMap.proj l
  have hF : ∀ y : Fin n → E, F (fun l => φ (y l)) = φ (f y) := fun y => by
    rw [hfx y, map_sum]
    simp only [F, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.coe_proj,
      Function.eval, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hle : Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s) ≤ LinearMap.ker F := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show F _ = 0
    rw [hF, hf0 y hy, map_zero]
  have h0 : φ (f z) = 0 := by
    rw [← hF]
    exact LinearMap.mem_ker.1 (hle h)
  exact hfz ((map_eq_zero_iff φ φ.injective).1 h0)

theorem mulVec_mem_span (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (v : InfinitePlace I.F) (k : Fin (a + 1)) (γ : Matrix (Fin I.n) (Fin I.n) I.E)
    (h : ∀ y ∈ flagAt I S v k, ((I.P v)⁻¹ * γ.map (I.φ v) * I.P v) *ᵥ y ∈ flagAt I S v k)
    (y : Fin I.n → I.E) (hy : y ∈ S k) : γ *ᵥ y ∈ Submodule.span I.E (S k : Set (Fin I.n → I.E)) := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hmem : (I.P v)⁻¹ *ᵥ (fun l => I.φ v (y l)) ∈ flagAt I S v k := by
    unfold flagAt
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  have h1 := h _ hmem
  have hcomp : ((I.P v)⁻¹ * γ.map (I.φ v) * I.P v) *ᵥ ((I.P v)⁻¹ *ᵥ (fun l => I.φ v (y l))) =
      (I.P v)⁻¹ *ᵥ (fun l => I.φ v ((γ *ᵥ y) l)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
    congr 1
    funext l
    exact (RingHom.map_mulVec (I.φ v) γ y l).symm
  rw [hcomp] at h1
  unfold flagAt at h1
  have h2 := Submodule.mem_map_of_mem (f := Matrix.toLin' (I.P v)) h1
  rw [Submodule.map_span, Set.image_image] at h2
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP,
    Matrix.one_mulVec] at h2
  exact mem_span_of_image (I.φ v) _ _ h2

theorem ratIso_eq (I : AutInst) (γ : GL (Fin I.n) I.E) (Λ N : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hΛ : ratIso I γ Λ = Λ) (hN : ∀ y, y ∈ N ↔ y ∈ Λ ∧ y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E)))
    (h : ∀ y ∈ N, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E))) :
    ratIso I γ N = N := by
  rw [ratIso_apply] at hΛ ⊢
  have hinj : Function.Injective (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) := by
    intro y y' hyy
    have hc := congrArg (Matrix.toLin' ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)) hyy
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hc
  have hWle : (Submodule.span I.E (N : Set (Fin I.n → I.E))).map
      (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) ≤ Submodule.span I.E (N : Set (Fin I.n → I.E)) := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro y hy
    exact h y hy
  have hW : (Submodule.span I.E (N : Set (Fin I.n → I.E))).map
      (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) = Submodule.span I.E (N : Set (Fin I.n → I.E)) := by
    refine Submodule.eq_of_le_of_finrank_eq hWle ?_
    have e := LinearEquiv.finrank_map_eq (ratEquiv I γ) (Submodule.span I.E (N : Set (Fin I.n → I.E)))
    exact e
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply]
    have hy' := (hN y).1 hy
    refine (hN _).2 ⟨?_, h y hy⟩
    rw [← hΛ]
    exact ⟨y, hy'.1, by simp⟩
  · intro y hy
    obtain ⟨hyΛ, hyW⟩ := (hN y).1 hy
    rw [← hΛ] at hyΛ
    obtain ⟨y', hy'Λ, hy'⟩ := hyΛ
    rw [← hW] at hyW
    obtain ⟨y'', hy''W, hy''⟩ := hyW
    have hyy : y'' = y' := hinj (by rw [hy'', ← hy']; rfl)
    subst hyy
    exact ⟨y'', (hN y'').2 ⟨hy'Λ, hy''W⟩, hy'⟩

theorem sizesAt_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S →
    ∀ γ ∈ flagGroup I xf S, ∀ g : I.Ginf, sizesAt I xf S (γ * g) = sizesAt I xf S g := by
  intro I xf a j S hS γ hγ g
  obtain ⟨⟨δ, hδ, hδ1, hδK⟩, hkeep⟩ := hγ
  obtain ⟨c, -, hc1, hc2⟩ := hδ
  unfold IsSatFlag at hS
  obtain ⟨-, -, -, hsat, -⟩ := hS
  have hL : lamX I (δ * (1, xf)) = lamX I (1, xf) := by
    have hk := (lamX_mul_eq_iff I (1, xf) (1, xf⁻¹ * δ.2 * xf)).1 hδK
    have h2 : (δ * (1, xf)).2 = ((1, xf) * (1, xf⁻¹ * δ.2 * xf) : I.GA).2 := by
      simp [mul_assoc]
    rw [← hk, lamX_eq, lamX_eq, h2]
  have hlat : ratIso I c (lamX I (1, xf)) = lamX I (1, xf) := by
    rw [← lamX_rat I (1, xf) δ c hc2, hL]
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  have hfix : ∀ k, ratIso I c (S k) = S k := fun k =>
    ratIso_eq I c _ (S k) hlat (hsat k) fun y hy =>
      mulVec_mem_span I S v₀ k (c : Matrix (Fin I.n) (Fin I.n) I.E)
        (fun x hx => by rw [← hc1 v₀, hδ1]; exact hkeep v₀ k x hx) y hy
  have hcond : ∀ v, uMat (((γ, 1) : I.GA).1 v) =
      (I.P v)⁻¹ * (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := fun v => by
    show uMat (γ v) = _
    rw [← hδ1]
    exact hc1 v
  have hax : ((γ, 1) : I.GA) * (g, xf) = (γ * g, xf) := by simp
  unfold sizesAt
  funext i
  have key := sizeQ_eq (bas I) (frm I (g, xf)) (frm I (γ * g, xf)) (ratIso I c)
    (fun N => by rw [← hax]; exact zl_ratIso I (g, xf) (γ, 1) c hcond N) (rkK_ratIso I c)
    (S i.succ) (S i.castSucc)
  rw [hfix, hfix] at key
  exact key

end GlobalTheory.FlagSizeInv
end
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagGradedPieceSizes_stabiliser_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ γ ∈ flagGroup I xf S, ∀ g : I.Ginf, sizesAt I xf S (γ * g) = sizesAt I xf S g := by
  atlas_forward_decl GlobalTheory.FlagSizeInv.sizesAt_mul
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagStabMul

theorem latGroup_mul (I : AutInst) (xf : I.Gf) {x y : I.Ginf} (hx : x ∈ latGroup I xf)
    (hy : y ∈ latGroup I xf) : x * y ∈ latGroup I xf := by
  obtain ⟨γ, hγ, rfl, hk⟩ := hx
  obtain ⟨δ, hδ, rfl, hl⟩ := hy
  refine ⟨γ * δ, (GlobalTheory.RatDiscrete.ratSub I).mul_mem hγ hδ, rfl, ?_⟩
  have h : xf⁻¹ * (γ * δ).2 * xf = (xf⁻¹ * γ.2 * xf) * (xf⁻¹ * δ.2 * xf) := by
    rw [Prod.snd_mul]; group
  rw [h]
  exact (Formalism.UG.stabGL I.Lf).mul_mem hk hl

theorem flagGroup_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), ∀ x ∈ flagGroup I xf S, ∀ y ∈ flagGroup I xf S, x * y ∈ flagGroup I xf S := by
  intro I xf a S x hx y hy
  refine ⟨latGroup_mul I xf hx.1 hy.1, fun v k z hz => ?_⟩
  have h : uMat ((x * y) v) = uMat (x v) * uMat (y v) := rfl
  rw [h, ← Matrix.mulVec_mulVec]
  exact hx.2 v k _ (hy.2 v k z hz)

end GlobalTheory.FlagStabMul
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagLatticeStabiliserRealGroup_mul_mem : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), ∀ x ∈ flagGroup I xf S, ∀ y ∈ flagGroup I xf S, x * y ∈ flagGroup I xf S := by
  atlas_forward_decl GlobalTheory.FlagStabMul.flagGroup_mul
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem layerProd_eq_pow (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) :
    layerProd n f j τ id = layerProd n 1 j (fun i => τ i ^ f) id := by
  unfold layerProd
  simp only [id, mul_one]
  congr 1
  · refine prod_congr rfl fun i _ => prod_congr rfl fun k _ => ?_
    ring
  · refine prod_congr rfl fun i _ => ?_
    ring

noncomputable def layerHom (n : ℕ) {a : ℕ} (j : Fin a → ℕ) : (Fin a → ℝ) →* ℝ where
  toFun τ := layerProd n 1 j τ id
  map_one' := by simp [layerProd]
  map_mul' σ τ := by
    unfold layerProd
    simp only [id, Pi.mul_apply]
    rw [mul_mul_mul_comm]
    refine congrArg₂ (· * ·) ?_ ?_
    · rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun k _ => ?_
      rw [mul_div_mul_comm, mul_mul_mul_comm (σ i) (τ i), mul_pow (σ i / σ k), mul_pow (σ i * σ k)]
      ring
    · rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [mul_pow (σ i) (τ i) 2, mul_pow (σ i), mul_pow (σ i ^ 2)]
      ring

theorem layerProd_mul_prod : ∀ (ι : Type) [Fintype ι] (n f a : ℕ) (j : Fin a → ℕ) (s s₁ : Fin a → ℝ)
    (loc : ι → Fin a → ℝ), (∀ i, s i ^ f = s₁ i ^ f * ∏ v, loc v i) →
    layerProd n f j s id = layerProd n f j s₁ id * ∏ v, layerProd n 1 j (loc v) id := by
  intro ι _ n f a j s s₁ loc h

  have hs : (fun i => s i ^ f) = (fun i => s₁ i ^ f) * ∏ v, loc v := by
    funext i
    rw [h i, Pi.mul_apply, Finset.prod_apply]
  have key : ∀ τ : Fin a → ℝ, layerHom n j τ = layerProd n 1 j τ id := fun τ => rfl
  rw [layerProd_eq_pow, layerProd_eq_pow n f j s₁, ← key, ← key, hs, map_mul, map_prod]
  simp only [key]

end GlobalTheory.FlagMeas
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagLayerProductMeasure_mul_prod_local : ∀ (ι : Type) [Fintype ι] (n f a : ℕ) (j : Fin a → ℕ) (s s₁ : Fin a → ℝ) (loc : ι → Fin a → ℝ), (∀ i, s i ^ f = s₁ i ^ f * ∏ v, loc v i) → layerProd n f j s id = layerProd n f j s₁ id * ∏ v, layerProd n 1 j (loc v) id := by
  atlas_forward_decl GlobalTheory.FlagMeas.layerProd_mul_prod
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.OneClass

theorem covol_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (hN : IsClosed (N : Set G)) (hM : IsClosed (M : Set G))
    (hK : IsClosed (K : Set G)) (hnorm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N)
    (huniq : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1) (hdec : ∀ g, ∃ u ∈ N, ∃ m ∈ M, ∃ k ∈ K, g = u * m * k)
    (μ μN μM μK : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] (δ w : G → ENNReal) (hδ : Measurable δ)
    (h1 : μN (N : Set G)ᶜ = 0) (h2 : μM (M : Set G)ᶜ = 0) (h3 : μK (K : Set G)ᶜ = 0) (h4 : μK Set.univ = 1)
    (hr : ∀ l ∈ K ⊓ M, μM.map (fun g => g * l) = μM) (hδr : ∀ l ∈ K ⊓ M, ∀ m ∈ M, δ (m * l) = δ m)
    (C c R t : ENNReal) (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hR0 : R ≠ 0) (hR : R ≠ ⊤) (ht0 : t ≠ 0) (ht : t ≠ ⊤)
    (hform : ∀ φ : G → ENNReal, Measurable φ →
      C * ∫⁻ g, φ g ∂μ = c * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN)
    (Γ ΓN ΓM A Z : Set G) (hZ : MeasurableSet Z) (hmul : ∀ x ∈ Γ, ∀ y ∈ Γ, x * y ∈ Γ)
    (hΓN : ∀ x ∈ ΓN, x ∈ Γ) (hΓM : ∀ m ∈ ΓM, m ∈ M ∧ ∃ g ∈ Γ, ∃ u ∈ N, g = u * m)
    (hΓN' : ∀ x ∈ ΓN, x ∈ N)
    (hA : ∀ γ ∈ Γ, ∀ g ∈ A, γ * g ∈ A) (hAZ : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, u * m * k ∈ A → m ∈ Z)
    (hw : ∀ m ∈ M, m ∈ Z → t * δ m ≤ w m) (hcN : covol ΓN μN N ≤ R * t) :
    C * covol Γ μ A ≤ c * R * covol ΓM (μM.withDensity w) M := by
  obtain ⟨σ, hσ, hσ1, hσ2⟩ := GlobalTheory.T.exists_measurable_coset_section' G (K ⊓ M) (by rw [Subgroup.coe_inf]; exact hK.inter hM)
  have hκ : ∀ k, k * (σ k)⁻¹ ∈ K ⊓ M := fun k => by simpa using (K ⊓ M).inv_mem (hσ1 k)
  have key : ∀ DN DM : Set G, MeasurableSet DN → MeasurableSet DM → (∀ x ∈ (N : Set G), ∃ γ ∈ ΓN, γ * x ∈ DN) →
      (∀ x ∈ (M : Set G), ∃ γ ∈ ΓM, γ * x ∈ DM) → C * covol Γ μ A ≤ c * (μN DN * ∫⁻ m in DM ∩ Z, δ m ∂μM) := by
    intro DN DM hDN hDM cN cM
    obtain ⟨D, hD, hiff⟩ := GlobalTheory.T.measurableSet_iwasawa_slice_of_transversal G N M K σ hN.measurableSet hM.measurableSet hK.measurableSet hσ hσ1 hσ2
      hnorm huniq DN (DM ∩ Z) hDN (hDM.inter hZ)
    have hcov : ∀ x ∈ A, ∃ γ ∈ Γ, γ * x ∈ D := by
      intro x hx
      obtain ⟨u, hu, m, hm, k, hk, rfl⟩ := hdec x
      obtain ⟨γM, hγM, hγD⟩ := cM (m * (k * (σ k)⁻¹)) (M.mul_mem hm (hκ k).2)
      obtain ⟨hγM', γ, hγ, u₀, hu₀, rfl⟩ := hΓM γM hγM
      have hu' : u₀ * (γM * u * γM⁻¹) ∈ N := N.mul_mem hu₀ (hnorm _ hγM' _ hu)
      obtain ⟨γN, hγN, hγD'⟩ := cN _ hu'
      have hγ' := hmul _ (hΓN _ hγN) _ hγ
      refine ⟨_, hγ', ?_⟩
      have e : γN * (u₀ * γM) * (u * m * k) = γN * (u₀ * (γM * u * γM⁻¹)) * (γM * m) * k := by group
      have e' : γN * (u₀ * γM) * (u * m * k) =
          γN * (u₀ * (γM * u * γM⁻¹)) * (γM * m * (k * (σ k)⁻¹)) * σ k := by group
      have hσK : σ k ∈ K := by simpa using K.mul_mem (hσ1 k).1 hk
      have hZ' := hA _ hγ' _ hx
      rw [e'] at hZ'
      have hN' := N.mul_mem (hΓN' _ hγN) hu'
      have hM' := M.mul_mem hγM' hm
      rw [e, hiff _ hN' _ hM' _ hk]
      exact ⟨hγD', by rwa [mul_assoc], hAZ _ hN' _ (M.mul_mem hM' (hκ k).2) _ hσK hZ'⟩
    calc C * covol Γ μ A ≤ C * μ D := by
          gcongr
          exact iInf_le_of_le D (iInf_le_of_le hD (iInf_le _ hcov))
      _ = C * ∫⁻ g, D.indicator 1 g ∂μ := by rw [lintegral_indicator_one hD]
      _ ≤ _ := by
          rw [hform _ (measurable_one.indicator hD)]
          gcongr
          exact GlobalTheory.T.iwasawa_slice_indicator_lintegral_le G N M K μN μM μK δ (fun k => k * (σ k)⁻¹) D DN (DM ∩ Z) hδ
            (measurable_id.mul hσ.inv) hDN (hDM.inter hZ) h1 h2 h3 h4 (fun k _ => hκ k) hr hδr
            (fun u hu m hm k hk h => (hiff u hu m hm k hk).1 h)
  have hcR0 : c * R ≠ 0 := mul_ne_zero hc0 hR0
  have hcR : c * R ≠ ⊤ := ENNReal.mul_ne_top hc hR
  rw [show covol ΓM (μM.withDensity w) M = ⨅ (D : Set G) (_ : MeasurableSet D)
    (_ : ∀ x ∈ (M : Set G), ∃ γ ∈ ΓM, γ * x ∈ D), μM.withDensity w D from rfl]
  simp only [ENNReal.mul_iInf_of_ne hcR0 hcR, le_iInf_iff]
  intro DM hDM cM
  have hX : t * ∫⁻ m in DM ∩ Z, δ m ∂μM ≤ μM.withDensity w DM := by
    rw [withDensity_apply _ hDM, ← lintegral_const_mul _ hδ]
    refine le_trans (lintegral_mono_ae ?_) (lintegral_mono_set (μ := μM) (f := w) (Set.inter_subset_left (t := Z)))
    filter_upwards [ae_restrict_mem (hDM.inter hZ), ae_restrict_of_ae (mem_ae_iff.2 h2)] with m hm hm'
    exact hw m hm' hm.2
  by_cases hT : ∫⁻ m in DM ∩ Z, δ m ∂μM = ⊤
  · rw [hT, ENNReal.mul_top ht0, top_le_iff] at hX
    rw [hX, ENNReal.mul_top hcR0]
    exact le_top
  by_cases h0 : ∫⁻ m in DM ∩ Z, δ m ∂μM = 0
  · have hne : covol ΓN μN N ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hR ht) hcN
    have hlt := hne.lt_top
    simp only [covol, iInf_lt_iff] at hlt
    obtain ⟨DN, hDN, cN, -⟩ := hlt
    have := key DN DM hDN hDM cN cM
    rw [h0, mul_zero, mul_zero] at this
    exact this.trans (zero_le)
  calc C * covol Γ μ A ≤ (c * ∫⁻ m in DM ∩ Z, δ m ∂μM) * covol ΓN μN N := by
        rw [show covol ΓN μN N = ⨅ (D : Set G) (_ : MeasurableSet D)
          (_ : ∀ x ∈ (N : Set G), ∃ γ ∈ ΓN, γ * x ∈ D), μN D from rfl]
        simp only [ENNReal.mul_iInf_of_ne (mul_ne_zero hc0 h0) (ENNReal.mul_ne_top hc hT), le_iInf_iff]
        intro DN hDN cN
        refine (key DN DM hDN hDM cN cM).trans_eq (by ring)
    _ ≤ (c * ∫⁻ m in DM ∩ Z, δ m ∂μM) * (R * t) := by gcongr
    _ = c * R * (t * ∫⁻ m in DM ∩ Z, δ m ∂μM) := by ring
    _ ≤ _ := by gcongr

theorem size_nonneg (I : AutInst) (x : I.GA) (A B : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    0 ≤ Formalism.HN.sizeQ (bas I) (frm I x) A B := by
  unfold Formalism.HN.sizeQ Formalism.HN.htQ Formalism.F.covol
  refine Real.rpow_nonneg ?_ _
  split_ifs <;> positivity

theorem gauge_pos {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  have hp : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  obtain ⟨r, hr, hr0⟩ := ((h.eventually (lt_mem_nhds hp)).and self_mem_nhdsWithin).exists
  by_contra hc
  exact absurd hr (not_lt.2 (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) ENNReal.toReal_nonneg) (pow_nonneg (le_of_lt hr0) _)))

theorem layerProd_pos (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) {τ : Fin a → ℝ} (h : ∀ i, 0 < τ i) :
    0 < layerProd n f j τ id := by
  unfold layerProd
  simp only [id]
  refine mul_pos (Finset.prod_pos fun i _ => Finset.prod_pos fun k _ => ?_) (Finset.prod_pos fun i _ => ?_)
  · have := h i
    have := h k
    positivity
  · have := h i
    positivity

theorem layerProd_nonneg (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) {τ : Fin a → ℝ} (h : ∀ i, 0 ≤ τ i) :
    0 ≤ layerProd n f j τ id := by
  unfold layerProd
  simp only [id]
  refine mul_nonneg (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun k _ => ?_)
    (Finset.prod_nonneg fun i _ => ?_)
  · have := h i
    have := h k
    positivity
  · have := h i
    positivity

theorem measurable_layerProd (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) :
    Measurable fun τ : Fin a → ℝ => layerProd n f j τ id := by
  unfold layerProd
  simp only [id]
  refine Measurable.mul (Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun k _ => ?_)
    (Finset.measurable_prod _ fun i _ => ?_) <;> fun_prop

theorem locSize_nonneg {n a : ℕ} (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (g : Matrix (Fin n) (Fin n) ℂ) (i : Fin a) : 0 ≤ locSize j W g i := by
  have h : ∀ V, 0 ≤ detOn g V := fun V => by
    unfold detOn
    split_ifs <;> positivity
  exact Real.rpow_nonneg (div_nonneg (h _) (h _)) _

theorem pi_compl {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)]
    (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] (H : ∀ i, Subgroup (G i))
    (h : ∀ i, μ i (H i : Set (G i))ᶜ = 0) :
    Measure.pi μ (Subgroup.pi Set.univ H : Set (∀ i, G i))ᶜ = 0 := by
  rw [← mem_ae_iff]
  have : ∀ᵐ x ∂(Measure.pi μ), ∀ i, x i ∈ (H i : Set (G i)) :=
    ae_all_iff.2 fun i => Measure.tendsto_eval_ae_ae.eventually (mem_ae_iff.2 (h i))
  filter_upwards [this] with x hx i _ using hx i

theorem bound : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (p q : ℕ), HasSig I p q → ∀ (c : InfinitePlace I.F → ℝ) (c₀ : InfinitePlace I₀.F → ℝ), IsGaugeAll I c → IsGaugeAll I₀ c₀ → ∀ B : Set (Fin a → ℝ), MeasurableSet B → B ⊆ simplexH a → ENNReal.ofReal (∏ v, c v) * covol (flagGroup I xf S) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) {g | sizesAt I xf S g ∈ B} ≤ ENNReal.ofReal (cIw p q j ^ I.f * (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2)) * (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Λ i)) * (ENNReal.ofReal (∏ v, c₀ v) * covol (latGroup I₀ x₀) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) Set.univ) * ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hj had p q hsig c c₀ hc hc₀ B hB hBs
  by_cases hA : {g | sizesAt I xf S g ∈ B} = ∅
  · have : covol (flagGroup I xf S) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) {g | sizesAt I xf S g ∈ B} = 0 := by
      rw [hA]
      refine le_antisymm (iInf_le_of_le ∅ (iInf_le_of_le MeasurableSet.empty (iInf_le_of_le (by simp) ?_))) zero_le
      simp
    rw [this, mul_zero]
    exact zero_le
  obtain ⟨g₀, hg₀⟩ := Set.nonempty_iff_ne_empty.2 hA
  have hsat := GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis I I₀ e xf a j S Λ x₀ T T' T₀ hj had
  have hiso := GlobalTheory.T.isTotallyIsotropicFlag_complexified_saturatedFlag I _ a j S hsat
  obtain ⟨-, hrd, hrd1, hf, hcard, -⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hf0 : I.f ≠ 0 := by omega
  have hex := fun v => GlobalTheory.T.exists_gauge_measures_isotropicFlag_parabolic I.n (I.ε v) a j _ hj (hiso v)
  choose μN hσN hμN using fun v => (hex v).1
  choose μM hσM hμM using fun v => (hex v).2.1
  choose μK hK0 hK1 hKl using fun v => (hex v).2.2
  haveI : ∀ v, IsProbabilityMeasure (μK v) := fun v => ⟨hK1 v⟩
  have hgN := fun v => GlobalTheory.T.isotropicFlagUnipotentRadical_closed_subgroup_keeps I.n (I.ε v) a j _ (hiso v)
  have hgM := fun v => GlobalTheory.T.isotropicFlagLevi_maxCompact_closed_subgroups I.n (I.ε v) a (flagAt I S v)
  choose N hN using fun v => (hgN v).1
  choose M hM using fun v => (hgM v).1
  choose K hK using fun v => (hgM v).2.2.1
  have mN : ∀ x : I.Ginf, x ∈ Subgroup.pi Set.univ N ↔ ∀ v, x v ∈ flagN (I.ε v) (flagAt I S v) := fun x => by
    simp only [Subgroup.mem_pi, Set.mem_univ, true_imp_iff, ← hN, SetLike.mem_coe]
  have mM : ∀ x : I.Ginf, x ∈ Subgroup.pi Set.univ M ↔ ∀ v, x v ∈ flagM (I.ε v) (flagAt I S v) := fun x => by
    simp only [Subgroup.mem_pi, Set.mem_univ, true_imp_iff, ← hM, SetLike.mem_coe]
  have mK : ∀ x : I.Ginf, x ∈ Subgroup.pi Set.univ K ↔ ∀ v, x v ∈ maxK (I.ε v) := fun x => by
    simp only [Subgroup.mem_pi, Set.mem_univ, true_imp_iff, ← hK, SetLike.mem_coe]
  haveI : ∀ v, PolishSpace (Formalism.REAL.UJ (I.ε v)) := fun v => by
    haveI : PolishSpace (Matrix (Fin I.n) (Fin I.n) ℂ) := inferInstanceAs (PolishSpace (Fin I.n → Fin I.n → ℂ))
    exact (Formalism.REAL.isClosedEmbeddingMatrix I.n (I.ε v)).1.polishSpace
  have hiw := fun v => GlobalTheory.T.iwasawa_decomposition_unitary_isotropicFlag I.n (I.ε v) a j _ (hiso v)
  have hdec : ∀ g : I.Ginf, ∃ u ∈ Subgroup.pi Set.univ N, ∃ m ∈ Subgroup.pi Set.univ M,
      ∃ k ∈ Subgroup.pi Set.univ K, g = u * m * k := by
    intro g
    choose u hu m hm k hk he using fun v => (hiw v).1 (g v)
    exact ⟨u, (mN _).2 hu, m, (mM _).2 hm, k, (mK _).2 hk, funext he⟩
  have hmove : ∀ u ∈ Subgroup.pi Set.univ N, ∀ m ∈ Subgroup.pi Set.univ M, ∀ k ∈ Subgroup.pi Set.univ K, ∀ i,
      sizesAt I xf S (u * m * k) i ^ I.f = sizesAt I xf S 1 i ^ I.f * ∏ v, locSize j (flagAt I S v) (uMat (m v)) i :=
    fun u hu m hm k hk i => GlobalTheory.T.gradedPieceSizes_unipotent_levi_compact_move I xf a j hj S hsat u m k ((mN _).1 hu) ((mM _).1 hm) ((mK _).1 hk) i
  have hs0 : ∀ g i, 0 ≤ sizesAt I xf S g i := fun g i => size_nonneg I _ _ _
  have hm1 : ∀ m ∈ Subgroup.pi Set.univ M, ∀ i,
      sizesAt I xf S m i ^ I.f = sizesAt I xf S 1 i ^ I.f * ∏ v, locSize j (flagAt I S v) (uMat (m v)) i := by
    intro m hm i
    simpa using hmove 1 (one_mem _) m hm 1 (one_mem _) i
  have hs1 : ∀ i, 0 < sizesAt I xf S 1 i := by
    intro i
    obtain ⟨u, hu, m, hm, k, hk, rfl⟩ := hdec g₀
    refine (hs0 1 i).lt_of_ne' fun h0 => ?_
    have h := hmove u hu m hm k hk i
    rw [h0, zero_pow hf0, zero_mul] at h
    exact ((hBs hg₀).2 i).1.ne' (pow_eq_zero_iff hf0 |>.1 h)
  let s : I.Ginf → Fin a → ℝ := fun m i =>
    (sizesAt I xf S 1 i ^ I.f * ∏ v, locSize j (flagAt I S v) (uMat (m v)) i) ^ ((I.f : ℝ)⁻¹)
  have hloc : ∀ v, Measurable fun (g : Formalism.REAL.UJ (I.ε v)) (i : Fin a) => locSize j (flagAt I S v) (uMat g) i :=
    fun v => measurable_pi_iff.2 fun i => GlobalTheory.T.measurable_flagLocalSizes_unitary _ _ _ _ _ i
  have hsm : Measurable s := measurable_pi_iff.2 fun i =>
    (measurable_const.mul (Finset.measurable_prod _ fun v _ =>
      (GlobalTheory.T.measurable_flagLocalSizes_unitary _ _ _ _ _ i).comp (measurable_pi_apply v))).pow_const _
  have hs : ∀ u ∈ Subgroup.pi Set.univ N, ∀ m ∈ Subgroup.pi Set.univ M, ∀ k ∈ Subgroup.pi Set.univ K,
      s m = sizesAt I xf S (u * m * k) := by
    intro u hu m hm k hk
    funext i
    simp only [s]
    rw [← hmove u hu m hm k hk i, Real.pow_rpow_inv_natCast (hs0 _ i) hf0]
  have hsM : ∀ m ∈ Subgroup.pi Set.univ M, s m = sizesAt I xf S m := fun m hm => by
    simpa using hs 1 (one_mem _) m hm 1 (one_mem _)
  let δ : ∀ v, Formalism.REAL.UJ (I.ε v) → ENNReal := fun v m =>
    ENNReal.ofReal (layerProd I.n 1 j (locSize j (flagAt I S v) (uMat m)) id)
  have hδ : ∀ v, Measurable (δ v) := fun v => ((measurable_layerProd I.n 1 j).comp (hloc v)).ennreal_ofReal
  have hL1 := layerProd_pos I.n I.f j hs1
  have htδ : ∀ m ∈ Subgroup.pi Set.univ M, ENNReal.ofReal (layerProd I.n I.f j (sizesAt I xf S 1) id) *
      ∏ v, δ v (m v) = ENNReal.ofReal (layerProd I.n I.f j (sizesAt I xf S m) id) := by
    intro m hm
    rw [GlobalTheory.T.flagLayerProductMeasure_mul_prod_local _ I.n I.f a j _ _ (fun v => locSize j (flagAt I S v) (uMat (m v))) (hm1 m hm),
      ENNReal.ofReal_mul hL1.le,
      ENNReal.ofReal_prod_of_nonneg fun v _ => layerProd_nonneg _ _ _ (locSize_nonneg _ _ _)]
  have ht0 : ENNReal.ofReal (layerProd I.n I.f j (sizesAt I xf S 1) id) ≠ 0 := by simpa using hL1
  have hcp := fun v => gauge_pos (hc v)
  have hIw := SatModel.cIw_pos p q j
  have hR : 0 < (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2) :=
    Real.rpow_pos_of_pos (by rw [hrd]; linarith) _
  let F : (Fin a → ℝ) → ENNReal := B.indicator fun τ => ENNReal.ofReal (layerProd I.n I.f j τ id)
  have hF : Measurable F := (measurable_layerProd I.n I.f j).ennreal_ofReal.indicator hB
  have hform := GlobalTheory.T.iwasawaNMKIntegration_pi_product _ (fun v => Formalism.REAL.UJ (I.ε v)) (fun v => Formalism.REAL.muG (I.ε v)) μN μM μK
    (fun v => ENNReal.ofReal (c v)) (fun _ => ENNReal.ofReal (cIw p q j)) δ (fun v => by simpa using hcp v)
    (fun v => ENNReal.ofReal_ne_top) hδ (fun v φ hφ => GlobalTheory.T.unitary_iwasawa_integration_formula_real_place I.n (I.ε v) p q (hsig v).1 (hsig v).2 a j hj _
      (hiso v) (c v) (μN v) (μM v) (μK v) (hc v) (hμN v) (hμM v) (hK0 v) (hK1 v) (hKl v) φ hφ)
  rw [← ENNReal.ofReal_prod_of_nonneg fun v _ => (hcp v).le, Finset.prod_const, Finset.card_univ, hcard,
    ← ENNReal.ofReal_pow hIw.le] at hform
  have hrad := GlobalTheory.T.unipotentRadical_integral_points_covolume I xf a j hj S hsat μN hμN
  rw [ENNReal.ofReal_mul hR.le] at hrad
  have hlevi := GlobalTheory.T.levi_factor_integral_mod_integral_points_le I I₀ e xf a j S Λ x₀ T T' T₀ hj had μM c₀ hμM hc₀ F hF
  have eN : {g : I.Ginf | ∀ v, g v ∈ flagN (I.ε v) (flagAt I S v)} =
      ((Subgroup.pi Set.univ N : Subgroup I.Ginf) : Set I.Ginf) := Set.ext fun x => (mN x).symm
  have eM : {g : I.Ginf | ∀ v, g v ∈ flagM (I.ε v) (flagAt I S v)} =
      ((Subgroup.pi Set.univ M : Subgroup I.Ginf) : Set I.Ginf) := Set.ext fun x => (mM x).symm
  rw [eN] at hrad
  rw [eM] at hlevi
  have hmain := covol_le (G := I.Ginf) (Subgroup.pi Set.univ N) (Subgroup.pi Set.univ M) (Subgroup.pi Set.univ K)
    (isClosed_set_pi fun v _ => (show IsClosed (N v : Set (Formalism.REAL.UJ (I.ε v))) by
      rw [hN]; exact (hgN v).2.1))
    (isClosed_set_pi fun v _ => (show IsClosed (M v : Set (Formalism.REAL.UJ (I.ε v))) by
      rw [hM]; exact (hgM v).2.1))
    (isClosed_set_pi fun v _ => (show IsClosed (K v : Set (Formalism.REAL.UJ (I.ε v))) by
      rw [hK]; exact (hgM v).2.2.2.1))
    (fun m hm u hu => (mN _).2 fun v => (hgM v).2.2.2.2 _ ((mM _).1 hm v) _ ((mN _).1 hu v))
    (fun u hu m hm h => funext fun v => (hiw v).2 _ ((mN _).1 hu v) _ ((mM _).1 hm v) ((mK _).1 h v)) hdec
    (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) (Measure.pi μN) (Measure.pi μM) (Measure.pi μK)
    (fun m => ∏ v, δ v (m v)) (fun m => F (sizesAt I xf S m))
    (Finset.measurable_prod _ fun v _ => (hδ v).comp (measurable_pi_apply v))
    (pi_compl _ _ fun v => by rw [hN]; exact (hμN v).1) (pi_compl _ _ fun v => by rw [hM]; exact (hμM v).1)
    (pi_compl _ _ fun v => by rw [hK]; exact hK0 v) measure_univ
    (fun l hl => (measurePreserving_pi μM μM (f := fun v g => g * l v) fun v => ⟨measurable_mul_const _,
      GlobalTheory.T.isRiemannianHaarOnSubgroup_map_mul_right_unitary I.n (I.ε v) (M v) _ (μM v) (by rw [hM]; exact (hgM v).2.1) (by rw [hM]; exact hμM v) (l v)
        (hl.2 v trivial) ((mK _).1 hl.1 v)⟩).map_eq)
    (fun l hl m hm => by
      refine (ENNReal.mul_right_inj ht0 ENNReal.ofReal_ne_top).1 ?_
      rw [htδ _ hm, htδ _ (mul_mem hm hl.2), ← hsM m hm, hs 1 (one_mem _) m hm l hl.1, one_mul])
    _ _ _ _ (by simpa using pow_pos hIw _) ENNReal.ofReal_ne_top (by simpa using hR) ENNReal.ofReal_ne_top ht0
    ENNReal.ofReal_ne_top hform (flagGroup I xf S)
    {g : I.Ginf | ∃ γ ∈ I.GFset, γ.1 = g ∧ xf⁻¹ * γ.2 * xf ∈ I.Kset ∧ ∀ v, g v ∈ flagN (I.ε v) (flagAt I S v)}
    (leviGroup I xf S) {g | sizesAt I xf S g ∈ B} (s ⁻¹' B)
    (hsm hB) (GlobalTheory.T.flagLatticeStabiliserRealGroup_mul_mem I xf a S)
    (fun x ⟨γ, h1, h2, h3, h4⟩ => ⟨⟨γ, h1, h2, h3⟩, fun v => (hgN v).2.2 _ (h4 v)⟩)
    (fun m ⟨h1, g, hg, u, hu, h2⟩ => ⟨(mM _).2 h1, g, hg, u, (mN _).2 hu, h2⟩)
    (fun x ⟨γ, h1, h2, h3, h4⟩ => (mN _).2 h4)
    (fun γ hγ g hg => by
      rw [Set.mem_setOf_eq, GlobalTheory.T.flagGradedPieceSizes_stabiliser_mul I xf a j S hsat γ hγ g]
      exact hg)
    (fun u hu m hm k hk h => by
      rw [Set.mem_preimage, hs u hu m hm k hk]
      exact h)
    (fun m hm hZ => by
      rw [Set.mem_preimage, hsM m hm] at hZ
      rw [htδ m hm]
      simp only [F, Set.indicator_of_mem hZ, le_refl]) hrad
  have hint : ∫⁻ τ in {τ : Fin a → ℝ | ∀ i, 0 < τ i}, F τ * ENNReal.ofReal (∏ i, 2 * (I.f : ℝ) * j i / τ i) ≤
      ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ) := by
    rw [← lintegral_indicator hB]
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun τ => ?_)
    by_cases hτ : τ ∈ B
    · simp only [F, Set.indicator_of_mem hτ, FlagMeas.dens]
      rw [ENNReal.ofReal_mul (layerProd_pos _ _ _ fun i => ((hBs hτ).2 i).1).le]
    · simp only [F, Set.indicator_of_notMem hτ, zero_mul, le_refl]
  refine hmain.trans ?_
  rw [ENNReal.ofReal_mul (pow_pos hIw _).le, mul_assoc _ (∏ i, _), mul_assoc _ (_ * _) (∫⁻ τ in B, _)]
  gcongr
  refine hlevi.trans ?_
  gcongr

end GlobalTheory.FlagBase.OneClass
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagClass_measure_bound_lattice_stabiliser : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (p q : ℕ), HasSig I p q → ∀ (c : InfinitePlace I.F → ℝ) (c₀ : InfinitePlace I₀.F → ℝ), IsGaugeAll I c → IsGaugeAll I₀ c₀ → ∀ B : Set (Fin a → ℝ), MeasurableSet B → B ⊆ simplexH a → ENNReal.ofReal (∏ v, c v) * covol (flagGroup I xf S) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) {g | sizesAt I xf S g ∈ B} ≤ ENNReal.ofReal (cIw p q j ^ I.f * (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2)) * (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Λ i)) * (ENNReal.ofReal (∏ v, c₀ v) * covol (latGroup I₀ x₀) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) Set.univ) * ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ) := by
  atlas_forward_decl GlobalTheory.FlagBase.OneClass.bound
end
