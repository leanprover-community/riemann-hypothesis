import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevEmbeddingDiscreteSeriesHilbertSchmidt
import BuildAid.ForwardExisting

section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem toMK_mem_UJ (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem continuous_orbit (hσ : IsURepOn (UJset ε) σ) (w : H) : Continuous fun k : KG ε => σ (toMK k) w :=
  (hσ.2.2 w).comp_continuous (continuous_toMK ε) toMK_mem_UJ

theorem integrable_avg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (w : H) :
    Integrable (fun k : KG ε => e k • σ (toMK k) w) (muK ε) :=
  (he.smul (continuous_orbit hσ w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem sigma_K_mul (hσ : IsURepOn (UJset ε) σ) (a b : KG ε) (w : H) :
    σ (toMK (a * b)) w = σ (toMK a) (σ (toMK b) w) :=
  sigma_mul hσ (toMK_mem_UJ a) (toMK_mem_UJ b) w

theorem inner_K (hσ : IsURepOn (UJset ε) σ) (a : KG ε) (x w : H) :
    ⟪σ (toMK a) w, x⟫_ℂ = ⟪w, σ (toMK a⁻¹) x⟫_ℂ := by
  have h := LinearIsometry.inner_map_map ⟨(σ (toMK a) : H →ₗ[ℂ] H), hσ.2.1 _ (toMK_mem_UJ a)⟩ w (σ (toMK a⁻¹) x)
  have e : σ (toMK a) (σ (toMK a⁻¹) x) = x := by
    rw [← sigma_K_mul hσ, mul_inv_cancel]; exact sigma_one hσ x
  rw [← h]
  exact congrArg (fun z => ⟪σ (toMK a) w, z⟫_ℂ) e.symm

theorem kFinFun_coef (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : IsKFin ε σ y) :
    KFinFun ε (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) := by
  obtain ⟨S, hS, hyS, hK⟩ := hy
  let φ : H → H → KG ε → ℂ := fun s s' k => ⟪σ (toMK k) s', s⟫_ℂ
  obtain ⟨t, ht⟩ : S.FG := Module.Finite.iff_fg.1 hS
  have hfin : (Set.image2 φ (t : Set H) (t : Set H)).Finite := t.finite_toSet.image2 _ t.finite_toSet
  have key : ∀ s ∈ S, ∀ s' ∈ S, φ s s' ∈ Submodule.span ℂ (Set.image2 φ (t : Set H) (t : Set H)) := by
    intro s hs s' hs'
    rw [← ht] at hs hs'
    induction hs using Submodule.span_induction with
    | mem x hx =>
      induction hs' using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span (Set.mem_image2_of_mem hx hz)
      | zero =>
        have : φ x 0 = 0 := by ext k; simp [φ]
        rw [this]; exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : φ x (a + b) = φ x a + φ x b := by ext k; simp [φ, inner_add_left]
        rw [this]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : φ x (c • a) = (starRingEnd ℂ c) • φ x a := by ext k; simp [φ, inner_smul_left, mul_comm]
        rw [this]; exact Submodule.smul_mem _ _ ha
    | zero =>
      have : φ 0 s' = 0 := by ext k; simp [φ]
      rw [this]; exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      have : φ (a + b) s' = φ a s' + φ b s' := by ext k; simp [φ, inner_add_right]
      rw [this]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : φ (c • a) s' = c • φ a s' := by ext k; simp [φ, inner_smul_right]
      rw [this]; exact Submodule.smul_mem _ _ ha
  have htS : ∀ x ∈ (t : Set H), x ∈ S := fun x hx => ht ▸ Submodule.subset_span hx
  refine ⟨Submodule.span ℂ (Set.image2 φ (t : Set H) (t : Set H)), FiniteDimensional.span_of_finite ℂ hfin, ?_, ?_, ?_⟩
  · have : (fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ) = φ y y := by
      ext k; exact inner_conj_symm _ _
    rw [this]; exact key y hyS y hyS
  · intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, -, b, -, rfl⟩ := hx
      exact (continuous_orbit hσ b).inner continuous_const
    | zero => exact continuous_zero
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  · intro ψ hψ k₀
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      constructor
      · have : (fun k => φ a b (k₀ * k)) = φ (σ (toMK k₀⁻¹) a) b := by
          ext k; simp only [φ]; rw [sigma_K_mul hσ, inner_K hσ]
        rw [this]; exact key _ (hK _ (toMK_mem_K _) _ (htS a ha)) _ (htS b hb)
      · have : (fun k => φ a b (k * k₀)) = φ a (σ (toMK k₀) b) := by
          ext k; simp only [φ]; rw [sigma_K_mul hσ]
        rw [this]; exact key _ (htS a ha) _ (hK _ (toMK_mem_K _) _ (htS b hb))
    | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨Submodule.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
    | smul c a _ ha => exact ⟨Submodule.smul_mem _ c ha.1, Submodule.smul_mem _ c ha.2⟩

variable [CompleteSpace H]

theorem inner_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (x w : H) :
    ⟪x, kAvg ε σ e w⟫_ℂ = ∫ k, e k * ⟪x, σ (toMK k) w⟫_ℂ ∂(muK ε) := by
  rw [kAvg, ← integral_inner (integrable_avg hσ he w)]
  simp only [inner_smul_right]

theorem inner_kAvg_ne_zero (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : y ≠ 0) :
    ⟪y, kAvg ε σ (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) y⟫_ℂ ≠ 0 := by
  have hc : Continuous fun k : KG ε => ⟪y, σ (toMK k) y⟫_ℂ := continuous_const.inner (continuous_orbit hσ y)
  rw [inner_kAvg hσ hc.star]
  have e : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  simp only [e]
  rw [integral_complex_ofReal]
  have hpos : 0 < ∫ k : KG ε, ‖⟪y, σ (toMK k) y⟫_ℂ‖ ^ 2 ∂(muK ε) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (hc.norm.pow 2)
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) ?_
    have : σ (toMK (1 : KG ε)) y = y := sigma_one hσ y
    rw [this]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hy))
  exact_mod_cast hpos.ne'

omit [CompleteSpace H] in

theorem exists_clm_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) :
    ∃ Q : H →L[ℂ] H, ∀ w, Q w = kAvg ε σ e w := by
  let L : H →ₗ[ℂ] H :=
    { toFun := kAvg ε σ e
      map_add' := fun x y => by
        simp only [kAvg, map_add, smul_add]
        exact integral_add (integrable_avg hσ he x) (integrable_avg hσ he y)
      map_smul' := fun c x => by
        simp only [kAvg, map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (∫ k, ‖e k‖ ∂(muK ε)) fun w => ?_, fun w => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, fun k : KG ε => hσ.2.1 _ (toMK_mem_UJ k) w]
  exact integral_mul_const _ _

theorem kAvg_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {S : Submodule ℂ H}
    [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H} (hz : z ∈ S) : kAvg ε σ e z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro u hu
  rw [inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪u, σ (toMK k) z⟫_ℂ = 0 := fun k =>
    Submodule.inner_left_of_mem_orthogonal (hK _ (toMK_mem_K k) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KCoef

namespace GlobalTheory.TypeSum

theorem kCoef_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → (∀ y, IsKFin ε σ y → KFinFun ε (fun k => star ⟪y, σ (toMK k) y⟫_ℂ)) ∧ (∀ y : H, y ≠ 0 → ⟪y, kAvg ε σ (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) y⟫_ℂ ≠ 0) ∧ (∀ e : KG ε → ℂ, Continuous e → ∃ Q : H →L[ℂ] H, ∀ w, Q w = kAvg ε σ e w) ∧ ∀ e : KG ε → ℂ, Continuous e → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ z ∈ S, kAvg ε σ e z ∈ S :=
  fun _ _ _ _ _ _ _ hσ => ⟨fun _ hy => KCoef.kFinFun_coef hσ hy, fun _ hy => KCoef.inner_kAvg_ne_zero hσ hy,
    fun _ he => KCoef.exists_clm_kAvg hσ he, fun _ he _ _ hK _ hz => KCoef.kAvg_mem hσ he hK hz⟩

end GlobalTheory.TypeSum
end

section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_embedding_discrete_series_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (f x : ι → H) (A : ℝ), 0 ≤ A → (∀ j, Sm ε σ (x j)) → (∀ l ∈ S, ∀ z : ι → ℂ, ‖∑ j, z j • Dw σ l (x j)‖ ^ 2 ≤ A * ∑ j, ‖z j‖ ^ 2) → ‖∑ j, ⟪f j, x j⟫_ℂ‖ ^ 2 ≤ C * A * ∑ j, ‖f j‖ ^ 2 := by
  first | exact @GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt | exact GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt | (intros; apply GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt <;> assumption)
end

section
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.admitted

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem isKFin_of_mem_closure (hσ : IsURepOn (UJset ε) σ) {U : Set H} {M : ℕ}
    (hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S)
    {u : H} (hu : u ∈ closure U) : IsKFin ε σ u := by
  let t : Set H := Set.range fun k : KG ε => σ (toMK k) u
  obtain ⟨b, hbt, hsp, hli⟩ := exists_linearIndependent ℂ t
  have hfin : b.Finite := by
    by_contra hinf
    haveI : Infinite b := Set.infinite_coe_iff.2 hinf
    let e : Fin (M + 1) ↪ b := Fin.valEmbedding.trans (Infinite.natEmbedding b)
    choose k hk using fun i => hbt (e i).2
    have hc : Continuous fun w : H => fun i : Fin (M + 1) => σ (toMK (k i)) w :=
      continuous_pi fun i => (σ _).continuous
    have ho := (isOpen_setOf_linearIndependent (𝕜 := ℂ) (E := H) (ι := Fin (M + 1))).preimage hc
    have hu' : LinearIndependent ℂ fun i : Fin (M + 1) => σ (toMK (k i)) u := by
      have := hli.comp e e.injective
      rwa [show (Subtype.val ∘ e : Fin (M + 1) → H) = _ from funext fun i => (hk i).symm] at this
    obtain ⟨w, hw, hwU⟩ := mem_closure_iff.1 hu _ ho hu'
    obtain ⟨S, hS, hM, hwS, hK⟩ := hU w hwU
    have h1 : LinearIndependent ℂ fun i : Fin (M + 1) =>
        (⟨σ (toMK (k i)) w, hK _ (toMK_mem_K _) w hwS⟩ : S) :=
      LinearIndependent.of_comp S.subtype hw
    have h2 := h1.fintype_card_le_finrank
    rw [Fintype.card_fin] at h2
    omega
  refine ⟨Submodule.span ℂ t, hsp ▸ FiniteDimensional.span_of_finite ℂ hfin, Submodule.subset_span ⟨1, ?_⟩,
    fun g hg v hv => ?_⟩
  · exact sigma_one hσ u
  · refine (Submodule.map_span_le (σ g : H →ₗ[ℂ] H) _ _).2 ?_ ⟨v, hv, rfl⟩
    rintro _ ⟨k, rfl⟩
    obtain ⟨g', rfl⟩ : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
    exact Submodule.subset_span ⟨g' * k, sigma_mul hσ (K_le_UJ hg) (K_le_UJ (toMK_mem_K k)) u⟩

variable [CompleteSpace H]

theorem exists_word_clm (h : Std ε σ) (W : Submodule ℂ H) [CompleteSpace W] (hW : ∀ w ∈ W, Sm ε σ w)
    {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) : ∃ A : W →L[ℂ] H, ∀ w : W, A w = Dw σ l w := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) h.1 l hl
  let A : W →ₗ[ℂ] H := (smooth (Jm ε) σ).subtype ∘ₗ L ∘ₗ Submodule.inclusion hW
  have hA : ∀ x : W, A x = Dw σ l x := fun x => hL _
  refine ⟨⟨A, A.continuous_of_seq_closed_graph fun s x z hs hz =>
    h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_⟩, hA⟩
  have h1 : Tendsto (fun j => ⟪y, A (s j)⟫_ℂ) atTop (𝓝 ⟪y, z⟫_ℂ) := tendsto_const_nhds.inner hz
  simp only [hA, fun x : W => inner_Dw h.1 hl hy (hW _ x.2)] at h1 ⊢
  exact tendsto_nhds_unique h1
    (tendsto_const_nhds.mul (tendsto_const_nhds.inner ((continuous_subtype_val.tendsto x).comp hs)))

theorem finiteDimensional_of_smooth (h : Std ε σ) (W : Submodule ℂ H) [CompleteSpace W]
    (hW : ∀ w ∈ W, Sm ε σ w) : FiniteDimensional ℂ W := by
  obtain ⟨S, C, hS, hC, hts⟩ := GlobalTheory.T.sobolev_embedding_discrete_series_hilbertSchmidt n ε H σ h
  choose A hA using fun l : {l // l ∈ S} => exists_word_clm h W hW (hS l.1 l.2)
  haveI : Finite {l // l ∈ S} := (List.finite_toSet S).to_subtype
  obtain ⟨B, hB⟩ := (Set.finite_range fun l => ‖A l‖ ^ 2).bddAbove
  have hB' : ∀ l, ‖A l‖ ^ 2 ≤ |B| := fun l => (hB ⟨l, rfl⟩).trans (le_abs_self B)
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ W
  have hfin : Finite w := by
    by_contra hinf
    haveI : Infinite w := not_finite_iff_infinite.1 hinf
    obtain ⟨m, hm⟩ := exists_nat_gt (C * |B|)
    let e : Fin m ↪ w := Fin.valEmbedding.trans (Infinite.natEmbedding w)
    have ho : Orthonormal ℂ fun j => b (e j) := b.orthonormal.comp e e.injective
    have key := hts (Fin m) (fun j => b (e j)) (fun j => b (e j)) |B| (abs_nonneg B) (fun j => hW _ (b (e j)).2)
      (fun l hl z => by
        have e1 : ∑ j, z j • Dw σ l (b (e j) : H) = A ⟨l, hl⟩ (∑ j, z j • b (e j)) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hA]
        have e2 : ‖∑ j, z j • b (e j)‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := by
          have := ho.inner_sum z z Finset.univ
          rw [inner_self_eq_norm_sq_to_K] at this
          simp only [RCLike.conj_mul] at this
          exact_mod_cast this
        rw [e1, ← e2]
        calc _ ≤ (‖A ⟨l, hl⟩‖ * ‖∑ j, z j • b (e j)‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ((A _).le_opNorm _) 2
          _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hB' _) (sq_nonneg _))
    have hn : ∀ j, ‖(b (e j) : H)‖ = 1 := fun j => ho.1 j
    simp only [inner_self_eq_norm_sq_to_K, hn] at key
    simp at key
    have h0 : 0 ≤ C * |B| := mul_nonneg hC (abs_nonneg B)
    nlinarith
  haveI := Fintype.ofFinite w
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

end GlobalTheory.TypeSum.admitted

namespace GlobalTheory.TypeSum

theorem finiteDimensional_of_bounded_orbits : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (U : Submodule ℂ H) (M : ℕ),
    (∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S) →
      FiniteDimensional ℂ U := by
  intro n ε H _ _ _ σ h U M hU
  haveI : CompleteSpace U.topologicalClosure := U.isClosed_topologicalClosure.completeSpace_coe
  haveI := admitted.finiteDimensional_of_smooth h U.topologicalClosure fun w hw =>
    h.2.2.1 w (admitted.isKFin_of_mem_closure h.1 (U := U) hU hw)
  exact Submodule.finiteDimensional_of_le U.le_topologicalClosure

end GlobalTheory.TypeSum
end

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (U : Submodule ℂ H) (M : ℕ), (∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S) → FiniteDimensional ℂ U := by
  atlas_forward_decl GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits
end

section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KAvgRank

open GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sigma_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (k₀ : KG ε) (w : H) :
    σ (toMK k₀) (kAvg ε σ e w) = kAvg ε σ (fun k => e (k₀⁻¹ * k)) w := by
  rw [kAvg, ← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ he w), kAvg,
    ← integral_mul_left_eq_self (fun k => e (k₀⁻¹ * k) • σ (toMK k) w) k₀]
  simp only [map_smul, inv_mul_cancel_left, sigma_K_mul hσ]

theorem exists_stable (hσ : IsURepOn (UJset ε) σ) {F : Submodule ℂ (KG ε → ℂ)} [FiniteDimensional ℂ F]
    (hc : ∀ φ ∈ F, Continuous φ) (hl : ∀ φ ∈ F, ∀ k₀ : KG ε, (fun k => φ (k₀ * k)) ∈ F) {e : KG ε → ℂ} (he : e ∈ F)
    (w : H) : ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      kAvg ε σ e w ∈ S ∧ IsKStableOn ε σ S := by
  let L : F →ₗ[ℂ] H :=
    { toFun := fun φ => kAvg ε σ φ w
      map_add' := fun x y => by
        simp only [kAvg, Submodule.coe_add, Pi.add_apply, add_smul]
        exact integral_add (integrable_avg hσ (hc _ x.2) w) (integrable_avg hσ (hc _ y.2) w)
      map_smul' := fun c x => by
        simp only [kAvg, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_assoc]
        exact integral_smul _ _ }
  refine ⟨LinearMap.range L, inferInstance, LinearMap.finrank_range_le L, ⟨⟨e, he⟩, rfl⟩, ?_⟩
  rintro k hk _ ⟨φ, rfl⟩
  obtain ⟨k₀, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hk
  exact ⟨⟨_, hl φ φ.2 k₀⁻¹⟩, (sigma_kAvg hσ (hc _ φ.2) k₀ w).symm⟩

theorem adjoint_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {Q : H →L[ℂ] H}
    (hQ : ∀ w, Q w = kAvg ε σ e w) {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H}
    (hz : z ∈ S) : ContinuousLinearMap.adjoint Q z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal']
  intro u hu
  rw [ContinuousLinearMap.adjoint_inner_left, hQ, inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪z, σ (toMK k) u⟫_ℂ = 0 := fun k => by
    have h := inner_K hσ k⁻¹ u z
    rw [inv_inv] at h
    rw [← h]
    exact Submodule.inner_right_of_mem_orthogonal (hK _ (toMK_mem_K _) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KAvgRank

namespace GlobalTheory.TypeSum

theorem kAvg_finite_rank : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), Orthonormal ℂ a ∧ (∀ j, IsKFin ε σ (a j)) ∧ (∀ j, IsKFin ε σ (c j)) ∧ ∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j := by
  intro n ε H _ _ _ σ h e ⟨F, hF, heF, hc, ht⟩
  have hσ := h.1
  obtain ⟨Q, hQ⟩ := KCoef.exists_clm_kAvg hσ (hc e heF)
  let U : Submodule ℂ H := LinearMap.range (Q : H →ₗ[ℂ] H)
  have hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      u ∈ S ∧ IsKStableOn ε σ S := by
    rintro _ ⟨w, rfl⟩
    have := KAvgRank.exists_stable hσ hc (fun φ hφ k₀ => (ht φ hφ k₀).1) heF w
    rwa [← hQ] at this
  haveI : FiniteDimensional ℂ U := GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension n ε H σ h U _ hU
  let b := stdOrthonormalBasis ℂ U
  refine ⟨_, fun j => (b j : H), fun j => ContinuousLinearMap.adjoint Q (b j), ?_, fun j => ?_, fun j => ?_,
    fun w => ?_⟩
  · exact b.orthonormal.comp_linearIsometry U.subtypeₗᵢ
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, h2, h3⟩
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, KAvgRank.adjoint_mem hσ (hc e heF) hQ h3 h2, h3⟩
  · have := congrArg Subtype.val (b.sum_repr' ⟨Q w, ⟨w, rfl⟩⟩)
    rw [← hQ]
    simp only [ContinuousLinearMap.adjoint_inner_left]
    simpa using this.symm

end GlobalTheory.TypeSum
end
