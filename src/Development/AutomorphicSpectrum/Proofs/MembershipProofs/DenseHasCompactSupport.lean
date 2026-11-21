import Lemmata.SchwartzCoordinateDivision

open Complex
open scoped Real ContDiff

namespace GlobalTheory.CompanionTheory.DiracComb

theorem hadamard_lemma : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f → f 0 = 0 → ∃ g : Fin n → (Fin n → ℝ) → ℂ, (∀ i, ContDiff ℝ ∞ (g i)) ∧ ∀ x, f x = ∑ i, (x i : ℂ) * g i x := @_root_.SchwartzCoordinateDivision.hadamard_lemma

theorem summable_weight (n : ℕ) :
    Summable fun m : Fin n → ℤ => ((1 + ‖(fun i => (m i : ℝ))‖) ^ (2 * n))⁻¹ := by
  have h1 : Summable fun k : ℤ => ((1 + |(k : ℝ)|) ^ 2)⁻¹ := by
    refine Summable.of_norm_bounded_eventually (Real.summable_one_div_int_pow.2 (by norm_num : 1 < 2)) ?_
    filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
    have hk' : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
    rw [Real.norm_of_nonneg (by positivity), one_div, ← sq_abs (k : ℝ)]
    gcongr
    linarith
  have h2 : ∀ n : ℕ, Summable fun m : Fin n → ℤ => ∏ i, ((1 + |(m i : ℝ)|) ^ 2)⁻¹ := by
    intro n
    induction n with
    | zero => exact Summable.of_finite
    | succ n ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).summable_iff]
      have := h1.mul_of_nonneg ih (fun _ => by positivity)
        (fun _ => Finset.prod_nonneg fun _ _ => by positivity)
      refine this.congr fun p => ?_
      simp [Fin.prod_univ_succ, Fin.consEquiv, mul_comm]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) (h2 n)
  rw [Finset.prod_inv_distrib, pow_mul]
  refine inv_anti₀ (Finset.prod_pos fun _ _ => by positivity) ?_
  have h3 := Finset.prod_le_prod (s := Finset.univ) (f := fun i : Fin n => (1 + |(m i : ℝ)|) ^ 2)
    (g := fun _ => (1 + ‖(fun i => (m i : ℝ))‖) ^ 2) (fun _ _ => by positivity) (fun i _ => by
      have := norm_le_pi_norm (fun i => (m i : ℝ)) i
      rw [Real.norm_eq_abs] at this
      gcongr)
  simpa using h3

theorem exists_comb : ∀ (n : ℕ), ∃ S : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, S f = ∑' m : Fin n → ℤ, f (fun i => (m i : ℝ)) := by
  intro n
  have hb : ∀ (f : SchwartzMap (Fin n → ℝ) ℂ) (x : Fin n → ℝ), ‖f x‖ ≤
      (2 ^ (2 * n) * (Finset.Iic (2 * n, 0)).sup (schwartzSeminormFamily ℂ (Fin n → ℝ) ℂ) f) *
        ((1 + ‖x‖) ^ (2 * n))⁻¹ := by
    intro f x
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (2 * n, 0)) (k := 2 * n)
      (n := 0) le_rfl le_rfl f x
    rw [norm_iteratedFDeriv_zero] at this
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact this
  have hs : ∀ f : SchwartzMap (Fin n → ℝ) ℂ,
      Summable fun m : Fin n → ℤ => ‖f (fun i => (m i : ℝ))‖ := fun f =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => hb f _)
      ((summable_weight n).mul_left _)
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun f => ∑' m : Fin n → ℤ, f (fun i => (m i : ℝ))) (fun f g => ?_) (fun a f => ?_) ?_,
    fun f => rfl⟩
  · exact (hs f).of_norm.tsum_add (hs g).of_norm
  · exact tsum_mul_left
  · refine ⟨Finset.Iic (2 * n, 0),
      2 ^ (2 * n) * ∑' m : Fin n → ℤ, ((1 + ‖(fun i => (m i : ℝ))‖) ^ (2 * n))⁻¹,
      by positivity, fun f => ?_⟩
    refine (tsum_of_norm_bounded ((summable_weight n).mul_left _).hasSum (fun m => hb f _)).trans ?_
    rw [tsum_mul_left]
    exact le_of_eq (by ring)

theorem exists_unity (n : ℕ) : ∃ ρ : (Fin n → ℤ) → (Fin n → ℝ) → ℝ, (∀ m, ContDiff ℝ ∞ (ρ m)) ∧
    (∀ m, tsupport (ρ m) ⊆ Metric.ball (fun i => (m i : ℝ)) 1) ∧
    LocallyFinite (fun m => Function.support (ρ m)) ∧ ∀ x, ∑ᶠ m, ρ m x = 1 := by
  have hcov : (Set.univ : Set (Fin n → ℝ)) ⊆
      ⋃ m : Fin n → ℤ, Metric.ball (fun i => (m i : ℝ)) 1 := by
    intro x _
    refine Set.mem_iUnion.2 ⟨fun i => ⌊x i⌋, ?_⟩
    rw [Metric.mem_ball, dist_pi_lt_iff one_pos]
    intro i
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [Int.floor_le (x i), Int.lt_floor_add_one (x i)]
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Fin n → ℝ)) isClosed_univ
    (fun m : Fin n → ℤ => Metric.ball (fun i => (m i : ℝ)) 1) (fun _ => Metric.isOpen_ball) hcov
  exact ⟨fun m => ρ m, fun m => (ρ m).contMDiff.contDiff, hρ, ρ.locallyFinite,
    fun x => ρ.sum_eq_one (Set.mem_univ x)⟩

theorem exists_partition : ∀ (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ), HasCompactSupport (f : (Fin n → ℝ) → ℂ) → ∃ (s : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → SchwartzMap (Fin n → ℝ) ℂ), (∀ m, tsupport (g m : (Fin n → ℝ) → ℂ) ⊆ Metric.ball (fun i => (m i : ℝ)) 1) ∧ f = ∑ m ∈ s, g m := by
  intro n f hf
  obtain ⟨ρ, h1, h2, h3, h4⟩ := exists_unity n
  have hsm : ∀ m, ContDiff ℝ ∞ (fun x => ρ m x • f x) := fun m => (h1 m).smul (f.smooth ⊤)
  have hcs : ∀ m, HasCompactSupport (fun x => ρ m x • f x) := fun m =>
    HasCompactSupport.smul_left (f := ρ m) hf
  have hfin : {m | (Function.support (ρ m) ∩ tsupport (f : (Fin n → ℝ) → ℂ)).Nonempty}.Finite :=
    h3.finite_nonempty_inter_compact hf
  obtain ⟨s, hs⟩ := hfin.exists_finset_coe
  have hts : ∀ m, tsupport ((hcs m).toSchwartzMap (hsm m) : (Fin n → ℝ) → ℂ) ⊆ tsupport (ρ m) :=
    fun m => tsupport_smul_subset_left (ρ m) f
  refine ⟨s, fun m => (hcs m).toSchwartzMap (hsm m), fun m => (hts m).trans (h2 m), ?_⟩
  ext x
  rw [sum_apply]
  suffices h : f x = ∑ m ∈ s, ρ m x • f x from h.trans (Finset.sum_congr rfl fun _ _ => rfl)
  by_cases hx : x ∈ tsupport (f : (Fin n → ℝ) → ℂ)
  · have hsub : Function.support (fun m => ρ m x) ⊆ s := by
      intro m hm
      rw [hs]
      exact ⟨x, hm, hx⟩
    rw [← Finset.sum_smul, ← finsum_eq_sum_of_support_subset _ hsub, h4, one_smul]
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem dense_hasCompactSupport : ∀ (n : ℕ), Dense {f : SchwartzMap (Fin n → ℝ) ℂ | HasCompactSupport (f : (Fin n → ℝ) → ℂ)} := @_root_.SchwartzCoordinateDivision.dense_hasCompactSupport

theorem exists_quot : ∃ q : ℝ → ℂ, ContDiffOn ℝ ∞ q (Metric.ball 0 1) ∧
    ∀ t ∈ Metric.ball (0 : ℝ) 1, (t : ℂ) = (cexp (2 * π * I * t) - 1) * q t := @_root_.SchwartzCoordinateDivision.exists_quot

theorem exists_div (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) :
    ∃ g : Fin n → SchwartzMap (Fin n → ℝ) ℂ, (∀ i, HasCompactSupport (g i : (Fin n → ℝ) → ℂ)) ∧
      ∀ x, f x = ∑ i, (cexp (2 * π * I * x i) - 1) * g i x := _root_.SchwartzCoordinateDivision.exists_div n f hf h0

theorem eq_mul_comb : ∀ (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ), (∀ (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → T g = T f) → (∀ (m : Fin n → ℤ) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = f (x + fun i => (m i : ℝ))) → T g = T f) → ∃ a : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = a * ∑' m : Fin n → ℤ, f (fun i => (m i : ℝ)) := by
  intro n T hχ hτ
  obtain ⟨S, hS⟩ := exists_comb n
  have hA : ∀ f : SchwartzMap (Fin n → ℝ) ℂ, tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1 →
      f 0 = 0 → T f = 0 := by
    intro f hf h0
    obtain ⟨g, hg, hg'⟩ := exists_div n f hf h0
    have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) := by
      intro i
      refine ContDiff.mul ?_ ((g i).smooth ⊤)
      exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i))).cexp
    have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) :=
      fun i => (hg i).mul_left
    have e : f = ∑ i, ((hcs i).toSchwartzMap (hsm i) - g i) := by
      ext x
      rw [hg' x, sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = cexp (2 * π * I * x i) * g i x - g i x
      ring
    rw [e, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sub, hχ i (g i) _ (fun x => rfl), sub_self]
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : (Fin n → ℝ) → ℝ)) :=
    b.hasCompactSupport.comp_left rfl
  let ψ : SchwartzMap (Fin n → ℝ) ℂ :=
    h₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hψ : ∀ x, ψ x = (b x : ℂ) := fun x => rfl
  have hψ0 : ψ 0 = 1 := by
    rw [hψ, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
  have hψs : tsupport (ψ : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1 := by
    refine (closure_mono ?_).trans (b.tsupport_eq.subset.trans
      (Metric.closedBall_subset_ball (by show (1 / 2 : ℝ) < 1; norm_num)))
    intro x hx h
    exact hx (by rw [hψ, h]; simp)
  have hB : ∀ f : SchwartzMap (Fin n → ℝ) ℂ, tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1 →
      T f = T ψ * f 0 := by
    intro f hf
    have := hA (f - f 0 • ψ) ?_ ?_
    · rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul] at this
      rw [this, mul_comm]
    · have hsub : Function.support (⇑(f - f 0 • ψ)) ⊆
          tsupport (f : (Fin n → ℝ) → ℂ) ∪ tsupport (ψ : (Fin n → ℝ) → ℂ) := by
        intro x hx
        by_contra hc
        rw [Set.mem_union, not_or] at hc
        apply hx
        show f x - f 0 • ψ x = 0
        rw [image_eq_zero_of_notMem_tsupport hc.1, image_eq_zero_of_notMem_tsupport hc.2]
        simp
      exact (closure_minimal hsub ((isClosed_tsupport _).union (isClosed_tsupport _))).trans
        (Set.union_subset hf hψs)
    · show f 0 - f 0 • ψ 0 = 0
      rw [hψ0]; simp
  have hC : ∀ (m : Fin n → ℤ) (f : SchwartzMap (Fin n → ℝ) ℂ),
      tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball (fun i => (m i : ℝ)) 1 → T f = T ψ * S f := by
    intro m f hf
    set c : Fin n → ℝ := fun i => (m i : ℝ) with hc
    let g := SchwartzMap.compSubConstCLM ℂ (-c) f
    have hg : ∀ x, g x = f (x + c) := fun x => by
      simp only [g, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
    have hgs : tsupport (g : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1 := by
      have hsub : Function.support (g : (Fin n → ℝ) → ℂ) ⊆
          (fun x => x + c) ⁻¹' tsupport (f : (Fin n → ℝ) → ℂ) := by
        intro x hx
        exact subset_tsupport _ (by rwa [Function.mem_support, hg] at hx)
      refine (closure_minimal hsub ((isClosed_tsupport _).preimage (by fun_prop))).trans ?_
      intro x hx
      have := hf hx
      simpa [Metric.mem_ball, dist_eq_norm] using this
    rw [← hτ m f g hg, hB g hgs, hg, zero_add, hS, tsum_eq_single m]
    intro k hk
    refine image_eq_zero_of_notMem_tsupport fun h => hk ?_
    have h1 := hf h
    funext i
    have h2 := (dist_le_pi_dist (fun i => (k i : ℝ)) c i).trans_lt h1
    rw [Real.dist_eq] at h2
    have h3 : |k i - m i| < 1 := by
      simp only [hc] at h2
      exact_mod_cast h2
    exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 h3)
  refine ⟨T ψ, fun f => ?_⟩
  rw [← hS]
  have hcl : IsClosed {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f} :=
    isClosed_eq T.continuous (continuous_const.mul S.continuous)
  refine closure_minimal (t := {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f}) ?_ hcl (dense_hasCompactSupport n f)
  intro f hf
  obtain ⟨s, g, hg, rfl⟩ := exists_partition n f hf
  show T _ = T ψ * S _
  rw [map_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => hC m (g m) (hg m)

end GlobalTheory.CompanionTheory.DiracComb
