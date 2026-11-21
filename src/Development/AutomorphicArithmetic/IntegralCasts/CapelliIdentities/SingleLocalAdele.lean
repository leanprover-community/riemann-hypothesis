import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

section
open MeasureTheory Metric

section
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]


omit [IsUltrametricDist K] [ProperSpace K] in
private lemma cond_pi (ψ : AddChar K ℂ) {d : K}
    (hd : ∀ t : K, (∀ x : K, ‖x‖ ≤ 1 → ψ (x * t) = 1) ↔ ‖t‖ ≤ ‖d‖)
    {κ : Type} [Fintype κ] {c : K} (hc : c ≠ 0) (y : κ → K) :
    (∀ x : κ → K, ‖x‖ ≤ ‖c‖ → ψ (dotProduct x y) = 1) ↔ ‖y‖ ≤ ‖d / c‖ := by
  classical
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  constructor
  · intro h
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [norm_div, le_div_iff₀ hc', ← norm_mul, ← hd]
    intro x hx
    have := h (Pi.single i (x * c)) (by
      rw [Pi.norm_single, norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hx)
    rw [single_dotProduct] at this
    rw [← this]; congr 1; ring
  · intro h x hx
    have key : ∀ s : Finset κ, ψ (∑ i ∈ s, x i * y i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, ih, mul_one]
        have h1 : ‖y i * c‖ ≤ ‖d‖ := by
          rw [norm_mul, ← le_div_iff₀ hc', ← norm_div]
          exact (norm_le_pi_norm y i).trans h
        have h2 := (hd _).2 h1 (x i / c) (by
          rw [norm_div]
          exact div_le_one_of_le₀ ((norm_le_pi_norm x i).trans hx) (norm_nonneg _))
        rw [← h2]; congr 1; field_simp
    exact key _

omit [IsUltrametricDist K] [ProperSpace K] in
private lemma unif {κ : Type} [Fintype κ] {f : (κ → K) → ℂ} (h1 : IsLocallyConstant f)
    (h2 : HasCompactSupport f) :
    ∃ e : K, e ≠ 0 ∧ ∀ u : κ → K, ‖u‖ ≤ ‖e‖ → ∀ x, f (x + u) = f x := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric (c := fun z : ℂ => f ⁻¹' {z}) h2
    (fun z => h1 _) (fun x _ => by simp)
  obtain ⟨e, he0, heδ⟩ := NormedField.exists_norm_lt K hδ
  refine ⟨e, norm_pos_iff.1 he0, fun u hu x => ?_⟩
  have hlt : ‖u‖ < δ := lt_of_le_of_lt hu heδ
  by_cases hx : x ∈ tsupport f
  · obtain ⟨z, hz⟩ := h x hx
    have a1 : f x = z := hz (mem_ball_self hδ)
    have a2 : f (x + u) = z := hz (by simpa [mem_ball, dist_eq_norm] using hlt)
    rw [a1, a2]
  · by_cases hx' : x + u ∈ tsupport f
    · obtain ⟨z, hz⟩ := h _ hx'
      have a1 : f (x + u) = z := hz (mem_ball_self hδ)
      have a2 : f x = z := hz (by simpa [mem_ball, dist_eq_norm] using hlt)
      rw [a1, a2]
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

omit [IsUltrametricDist K] [ProperSpace K] in
private lemma bdd {κ : Type} [Fintype κ] {f : (κ → K) → ℂ}
    (h2 : HasCompactSupport f) :
    ∃ c : K, c ≠ 0 ∧ ∀ x : κ → K, ¬ ‖x‖ ≤ ‖c‖ → f x = 0 := by
  obtain ⟨R, hR⟩ := h2.isCompact.isBounded.subset_closedBall 0
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (max R 0)
  refine ⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := mem_closedBall_zero_iff.1 (hR h)
  exact hx (this.trans ((le_max_left _ _).trans hc.le))

omit [IsUltrametricDist K] in
private lemma sb_of {κ : Type} [Fintype κ] {f : (κ → K) → ℂ} {e c : K} (he : e ≠ 0)
    (h1 : ∀ u : κ → K, ‖u‖ ≤ ‖e‖ → ∀ x, f (x + u) = f x)
    (h2 : ∀ x : κ → K, ¬ ‖x‖ ≤ ‖c‖ → f x = 0) :
    IsLocallyConstant f ∧ HasCompactSupport f := by
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [closedBall_mem_nhds x (norm_pos_iff.2 he)] with y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    simpa using h1 (y - x) hy x
  · exact HasCompactSupport.intro (isCompact_closedBall 0 ‖c‖)
      (fun x hx => h2 x (by simpa using hx))

end

section
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  {κ : Type} [Fintype κ] [MeasurableSpace (κ → K)] [BorelSpace (κ → K)]
  (μ : Measure (κ → K)) [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ)

private noncomputable def four (f : (κ → K) → ℂ) (y : κ → K) : ℂ :=
  ∫ x, ψ (dotProduct x y) * f x ∂μ

omit [IsUltrametricDist K] [ProperSpace K] in
private lemma four_transl (f : (κ → K) → ℂ) (a y : κ → K) :
    four μ ψ (fun x => f (x + a)) y = ψ (-(dotProduct a y)) * four μ ψ f y := by
  unfold four
  rw [← integral_add_right_eq_self (fun x => ψ (dotProduct x y) * f x) a, ← integral_const_mul]
  congr 1
  ext x
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct]
  congr 2
  ring

omit [IsUltrametricDist K] [ProperSpace K] [BorelSpace (κ → K)] [μ.IsAddHaarMeasure] in
private lemma four_mod (f : (κ → K) → ℂ) (b y : κ → K) :
    four μ ψ (fun x => ψ (dotProduct x b) * f x) y = four μ ψ f (y + b) := by
  unfold four
  congr 1
  ext x
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, dotProduct_add]

variable {d : K} (hd : ∀ t : K, (∀ x : K, ‖x‖ ≤ 1 → ψ (x * t) = 1) ↔ ‖t‖ ≤ ‖d‖)
include hd

omit [IsUltrametricDist K] [ProperSpace K] in
private lemma four_supp {f : (κ → K) → ℂ} {e : K} (he : e ≠ 0)
    (h1 : ∀ u : κ → K, ‖u‖ ≤ ‖e‖ → ∀ x, f (x + u) = f x) (y : κ → K) (hy : ¬ ‖y‖ ≤ ‖d / e‖) :
    four μ ψ f y = 0 := by
  rw [← cond_pi ψ hd he] at hy
  push Not at hy
  obtain ⟨u, hu, hne⟩ := hy
  have := four_transl μ ψ f (-u) y
  rw [show (fun x => f (x + -u)) = f from funext (h1 _ (by simpa using hu)), neg_dotProduct,
    neg_neg] at this
  by_contra h
  apply hne
  exact (mul_right_cancel₀ h (this.symm.trans (one_mul _).symm))

omit [IsUltrametricDist K] [ProperSpace K] [BorelSpace (κ → K)] [μ.IsAddHaarMeasure] in
private lemma four_inv {f : (κ → K) → ℂ} {c : K} (hc : c ≠ 0)
    (h2 : ∀ x : κ → K, ¬ ‖x‖ ≤ ‖c‖ → f x = 0) (u : κ → K) (hu : ‖u‖ ≤ ‖d / c‖) (y : κ → K) :
    four μ ψ f (y + u) = four μ ψ f y := by
  rw [← four_mod]
  congr 1
  ext x
  by_cases hx : ‖x‖ ≤ ‖c‖
  · rw [(cond_pi ψ hd hc u).2 hu x hx, one_mul]
  · rw [h2 x hx, mul_zero]

omit [IsUltrametricDist K] in
private lemma four_sb (hd0 : d ≠ 0) {f : (κ → K) → ℂ} (h1 : IsLocallyConstant f)
    (h2 : HasCompactSupport f) :
    IsLocallyConstant (four μ ψ f) ∧ HasCompactSupport (four μ ψ f) := by
  obtain ⟨e, he, h1⟩ := unif h1 h2
  obtain ⟨c, hc, h2⟩ := bdd h2
  exact sb_of (div_ne_zero hd0 hc) (four_inv μ ψ hd hc h2) (four_supp μ ψ hd he h1)

omit hd [ProperSpace K] [MeasurableSpace (κ → K)] [BorelSpace (κ → K)] in
private lemma ind_inv (r : ℝ) (u : κ → K) (hu : ‖u‖ ≤ r) (x : κ → K) :
    (closedBall (0 : κ → K) r).indicator (fun _ => (1 : ℂ)) (x + u) =
      (closedBall (0 : κ → K) r).indicator (fun _ => (1 : ℂ)) x := by
  have : x + u ∈ closedBall (0 : κ → K) r ↔ x ∈ closedBall (0 : κ → K) r := by
    simp only [mem_closedBall_zero_iff]
    constructor
    · intro h
      have := IsUltrametricDist.norm_add_le_max (x + u) (-u)
      rw [add_neg_cancel_right, norm_neg] at this
      exact this.trans (max_le h hu)
    · intro h
      exact (IsUltrametricDist.norm_add_le_max x u).trans (max_le h hu)
  by_cases hx : x ∈ closedBall (0 : κ → K) r
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (this.1 h))]

omit [ProperSpace K] in
private lemma four_ind {c : K} (hc : c ≠ 0) (y : κ → K) :
    four μ ψ ((closedBall (0 : κ → K) ‖c‖).indicator (fun _ => (1 : ℂ))) y =
      (μ.real (closedBall 0 ‖c‖) : ℂ) *
        (closedBall (0 : κ → K) ‖d / c‖).indicator (fun _ => (1 : ℂ)) y := by
  by_cases hy : ‖y‖ ≤ ‖d / c‖
  · have := four_inv μ ψ hd hc
      (f := (closedBall (0 : κ → K) ‖c‖).indicator (fun _ => (1 : ℂ)))
      (fun x hx => Set.indicator_of_notMem (by simpa using hx) _) y hy 0
    rw [zero_add] at this
    rw [this, Set.indicator_of_mem (by simpa using hy), mul_one]
    unfold four
    simp only [dotProduct_zero, AddChar.map_zero_eq_one, one_mul]
    rw [integral_indicator_const _ measurableSet_closedBall]
    simp
  · rw [four_supp μ ψ hd hc (ind_inv _) y hy, Set.indicator_of_notMem (by simpa using hy),
      mul_zero]


end
end

section
open Matrix
end

section
open NumberField IsDedekindDomain Filter Topology
open scoped nonZeroDivisors

namespace UpperTheory.TraceAwayCharacter

private lemma trace_eq (F : Type) [Field F] [NumberField F] (x : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F x)
      = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (mixedEmbedding.latticeBasis F),
    Algebra.trace_eq_matrix_trace (integralBasis F)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mixedEmbedding.latticeBasis_apply, ← map_mul, mixedEmbedding.latticeBasis_repr_apply]

private lemma far (q : ℚ) (hq : ∀ z : ℤ, q ≠ z) :
    ∃ m : ℕ, (Complex.exp (-(2 * Real.pi * Complex.I) * ((((m : ℚ) * q : ℚ) : ℝ) : ℂ))).re ≤ 0 := by
  by_contra! h
  set z : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (q : ℂ)) with hz
  have hpow : ∀ m : ℕ, Complex.exp (-(2 * Real.pi * Complex.I) *
      ((((m : ℚ) * q : ℚ) : ℝ) : ℂ)) = z ^ m := by
    intro m
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz1 : z ≠ 1 := by
    intro h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    apply hq (-n)
    have h2 : (q : ℂ) = ((-n : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (neg_ne_zero.mpr Complex.two_pi_I_ne_zero)
      rw [hn]
      push_cast
      ring
    exact_mod_cast h2
  have hd : z ^ q.den = 1 := by
    rw [← hpow, Rat.den_mul_eq_num, Complex.exp_eq_one_iff]
    refine ⟨-q.num, ?_⟩
    push_cast
    ring
  have hs : ∑ m ∈ Finset.range q.den, z ^ m = 0 := by
    rw [geom_sum_eq hz1, hd]
    simp
  have hpos : 0 < (∑ m ∈ Finset.range q.den, z ^ m).re := by
    rw [Complex.re_sum]
    refine Finset.sum_pos (fun m _ => hpow m ▸ h m) ?_
    exact Finset.nonempty_range_iff.mpr q.den_nz
  rw [hs] at hpos
  simp at hpos

private lemma exists_pole (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x : F, (∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → u.valuation F x ≤ 1) ∧ ¬ IsIntegral ℤ x := by
  obtain ⟨x, hx, hx1⟩ :=
    FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) v.ne_bot v.isPrime.ne_top
  refine ⟨x, fun u hu => ?_, fun hi => hx1 ?_⟩
  · have hle : ¬ v.asIdeal ≤ u.asIdeal := fun h =>
      hu (HeightOneSpectrum.ext (v.isMaximal.eq_of_le u.isPrime.ne_top h).symm)
    obtain ⟨t, ht, htu⟩ := Set.not_subset.mp hle
    have hv0 : (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot
    have h1 := (FractionalIdeal.mem_inv_iff hv0).mp hx (algebraMap _ F t)
      (FractionalIdeal.mem_coeIdeal_of_mem _ ht)
    obtain ⟨s, hs⟩ := (FractionalIdeal.mem_one_iff _).mp h1
    have h2 : u.valuation F (algebraMap _ F t) = 1 := by
      refine le_antisymm (u.valuation_le_one t) (not_lt.mp fun h => htu ?_)
      exact (u.valuation_lt_one_iff_mem t).mp h
    have h3 : u.valuation F (algebraMap (𝓞 F) F s) ≤ 1 := u.valuation_le_one s
    rwa [hs, map_mul, h2, mul_one] at h3
  · exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hi⟩, rfl⟩

private lemma exists_trace (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (N : ℕ) (hN : N ≠ 0) :
    ∃ y : F, (∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → u.valuation F y ≤ 1) ∧
      ∀ z : ℤ, Algebra.trace ℚ F ((N : F) * y) ≠ z := by
  classical
  by_contra! h
  obtain ⟨x, hx, hxi⟩ := exists_pole F v
  let M : Submodule ℤ F :=
    AddSubgroup.toIntSubmodule
      { carrier := {a | ∃ y : F, (∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → u.valuation F y ≤ 1) ∧
          a = (N : F) * y}
        add_mem' := by
          rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a + b, fun u hu => Valuation.map_add_le _ (ha u hu) (hb u hu), by ring⟩
        zero_mem' := ⟨0, by simp, by simp⟩
        neg_mem' := by
          rintro _ ⟨a, ha, rfl⟩
          exact ⟨-a, fun u hu => by simpa using ha u hu, by ring⟩ }
  have hM : ∀ a, a ∈ M ↔ ∃ y : F,
      (∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → u.valuation F y ≤ 1) ∧ a = (N : F) * y :=
    fun _ => Iff.rfl
  have hle : M ≤ Submodule.span ℤ (Set.range ((Algebra.traceForm ℚ F).dualBasis
      (traceForm_nondegenerate ℚ F) (integralBasis F))) := by
    rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis]
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := (hM a).mp ha
    obtain ⟨c, rfl⟩ := (mem_span_integralBasis F).mp hb
    obtain ⟨z, hz⟩ := h (y * algebraMap _ F c) fun u hu => by
      rw [map_mul]
      exact mul_le_one' (hy u hu) (u.valuation_le_one c)
    refine Submodule.mem_one.mpr ⟨z, ?_⟩
    rw [Algebra.traceForm_apply, mul_assoc, hz]
    simp
  have hfg : M.FG := Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle
  refine hxi (isIntegral_of_smul_mem_submodule M ?_ hfg x ?_)
  · refine (Submodule.ne_bot_iff _).mpr ⟨(N : F), (hM _).mpr ⟨1, by simp, by simp⟩, ?_⟩
    exact_mod_cast hN
  · intro a ha
    obtain ⟨y, hy, rfl⟩ := (hM a).mp ha
    refine (hM _).mpr ⟨x * y, fun u hu => ?_, by rw [smul_eq_mul]; ring⟩
    rw [map_mul]
    exact mul_le_one' (hx u hu) (hy u hu)

private lemma tendsto_local (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (w : ℕ → u.adicCompletion F) (hw : ∀ n, Valued.v (w n) ≤ 1) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : u.adicCompletion F) * w n) atTop (𝓝 0) := by
  have hnat : ∀ m : ℕ, ((m : ℕ) : u.adicCompletion F) =
      algebraMap F (u.adicCompletion F) (algebraMap (𝓞 F) F (m : 𝓞 F)) := by
    intro m
    simp
  have hval : ∀ m : ℕ, Valued.v ((m : ℕ) : u.adicCompletion F) =
      u.valuation F (algebraMap (𝓞 F) F (m : 𝓞 F)) := by
    intro m
    rw [hnat]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _
  set p : ℕ := Ideal.absNorm u.asIdeal with hp
  have hp0 : p ≠ 0 := fun h => u.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hp1 : Valued.v ((p : ℕ) : u.adicCompletion F) < 1 := by
    rw [hval]
    exact (u.valuation_lt_one_iff_mem _).mpr (Ideal.absNorm_mem _)
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hp1
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff] at ht ⊢
  intro γ hγ
  obtain ⟨k, hk⟩ := (ht γ hγ).exists
  filter_upwards [eventually_ge_atTop (p ^ k)] with n hn
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero (pow_ne_zero k hp0)) hn
  refine lt_of_le_of_lt ?_ hk
  rw [hc, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul]
  refine mul_le_of_le_one_right' ?_
  rw [Valuation.restrict_le_one_iff, map_mul]
  refine mul_le_one' ?_ (hw n)
  rw [hval]
  exact u.valuation_le_one _

private lemma tendsto_finite (F : Type) [Field F] [NumberField F]
    (a : ℕ → FiniteAdeleRing (𝓞 F) F) (w : ∀ u : HeightOneSpectrum (𝓞 F), ℕ → u.adicCompletion F)
    (hw : ∀ u n, Valued.v (w u n) ≤ 1)
    (ha : ∀ u n, a n u = ((n.factorial : ℕ) : u.adicCompletion F) * w u n) :
    Tendsto a atTop (𝓝 0) := by
  have hmem : ∀ u n, a n u ∈ (u.adicCompletionIntegers F : Set (u.adicCompletion F)) := by
    intro u n
    rw [ha]
    exact mul_mem (natCast_mem (u.adicCompletionIntegers F) _) (hw u n)
  let b : ℕ → ∀ u : HeightOneSpectrum (𝓞 F),
      (u.adicCompletionIntegers F : Set (u.adicCompletion F)) := fun n u => ⟨a n u, hmem u n⟩
  let b0 : ∀ u : HeightOneSpectrum (𝓞 F),
      (u.adicCompletionIntegers F : Set (u.adicCompletion F)) :=
    fun u => ⟨0, zero_mem (u.adicCompletionIntegers F)⟩
  have hb : Tendsto b atTop (𝓝 b0) := by
    rw [tendsto_pi_nhds]
    intro u
    rw [tendsto_subtype_rng]
    simp only [b, b0, ha]
    exact tendsto_local F u (w u) (hw u)
  exact ((RestrictedProduct.isEmbedding_structureMap
    (R := fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
    (A := fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F)))
    (𝓕 := cofinite)).continuous.tendsto b0).comp hb

private lemma exists_away (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : F) : ∃ r : FiniteAdeleRing (𝓞 F) F,
      r v = 0 ∧ ∀ u, u ≠ v → r u = algebraMap F (u.adicCompletion F) x := by
  classical
  refine ⟨⟨fun u => if u = v then 0 else algebraMap F (u.adicCompletion F) x, ?_⟩, ?_, ?_⟩
  · filter_upwards [(algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2] with u hu
    split_ifs
    · exact zero_mem (u.adicCompletionIntegers F)
    · exact hu
  · exact if_pos rfl
  · exact fun u hu => if_neg hu

end UpperTheory.TraceAwayCharacter

open UpperTheory.TraceAwayCharacter in
theorem UpperTheory.standard_additive_character :
    ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ),
        Continuous ψ →
        (∀ x : F, ψ (algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) x) = 1) →
        (∀ a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F, a.2 = 0 →
          ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
            (Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F)
              (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) : ℝ))) →
        ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          ∃ a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F,
            a.1 = 0 ∧ (∀ u, u ≠ v → a.2 u = 0) ∧ ψ a ≠ 1 := by
  intro F _ _ ψ hc hF hinf v
  classical
  by_contra! hv
  let j : FiniteAdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F := fun r => (0, r)
  have hj : Continuous j := continuous_const.prodMk continuous_id
  have key : ∀ (x : F) (r : FiniteAdeleRing (𝓞 F) F),
      (∀ u, u ≠ v → r u = algebraMap F (u.adicCompletion F) x) →
      ψ (-j r) = Complex.exp (-(2 * Real.pi * Complex.I) *
        (((Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ)) := by
    intro x r hr
    let i : AdeleRing (𝓞 F) F := (algebraMap F (InfiniteAdeleRing F) x, 0)
    let c : AdeleRing (𝓞 F) F := (0, r - algebraMap F (FiniteAdeleRing (𝓞 F) F) x)
    have h1 : ψ c = 1 := hv c rfl fun u hu => by
      change r u - algebraMap F (u.adicCompletion F) x = 0
      rw [hr u hu, sub_self]
    have h2 : i = -j r + c + algebraMap F (AdeleRing (𝓞 F) F) x := by
      refine Prod.ext ?_ ?_
      · change algebraMap F (InfiniteAdeleRing F) x
          = -0 + 0 + algebraMap F (InfiniteAdeleRing F) x
        ring
      · change 0 = -r + (r - algebraMap F (FiniteAdeleRing (𝓞 F) F) x)
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) x
        ring
    have h3 := hinf i rfl
    have h4 : InfiniteAdeleRing.ringEquiv_mixedSpace F i.1 = mixedEmbedding F x :=
      (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
    rw [h4, trace_eq, h2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1, hF, mul_one,
      mul_one] at h3
    exact h3
  have hy : ∀ n : ℕ, ∃ y : F, (∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → u.valuation F y ≤ 1) ∧
      (Complex.exp (-(2 * Real.pi * Complex.I) *
        (((Algebra.trace ℚ F ((n.factorial : F) * y) : ℚ) : ℝ) : ℂ))).re ≤ 0 := by
    intro n
    obtain ⟨y, hy, hz⟩ := exists_trace F v n.factorial n.factorial_ne_zero
    obtain ⟨m, hm⟩ := far _ hz
    refine ⟨(m : F) * y, fun u hu => ?_, ?_⟩
    · rw [map_mul]
      refine mul_le_one' ?_ (hy u hu)
      have : u.valuation F (algebraMap (𝓞 F) F (m : 𝓞 F)) ≤ 1 := u.valuation_le_one _
      rwa [map_natCast] at this
    · rwa [mul_left_comm, ← nsmul_eq_mul m, map_nsmul, nsmul_eq_mul]
  choose y hy hre using hy
  choose r hr0 hr using fun n : ℕ => exists_away F v ((n.factorial : F) * y n)
  have ht : Tendsto r atTop (𝓝 0) := by
    refine tendsto_finite F r
      (fun u n => if u = v then 0 else algebraMap F (u.adicCompletion F) (y n)) ?_ ?_
    · intro u n
      split_ifs with hu
      · simp
      · exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).trans_le (hy n u hu)
    · intro u n
      split_ifs with hu
      · subst hu
        rw [hr0, mul_zero]
      · rw [hr n u hu, map_mul, map_natCast]
  have hcont : Continuous fun s => (ψ (-j s)).re :=
    Complex.continuous_re.comp (hc.comp hj.neg)
  have hlim := (hcont.tendsto 0).comp ht
  have h0 : (ψ (-j 0)).re = 1 := by
    have : j 0 = 0 := rfl
    rw [this, neg_zero, AddChar.map_zero_eq_one, Complex.one_re]
  rw [h0] at hlim
  have hle : (1 : ℝ) ≤ 0 := le_of_tendsto' hlim fun n => by
    change (ψ (-j (r n))).re ≤ 0
    rw [key _ _ (hr n)]
    exact hre n
  exact absurd hle (by norm_num)
end

section
open scoped RestrictedProduct
open Filter Set

private lemma UpperTheory.factorizable_generation {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    [∀ i, T2Space (R i)] {A : ∀ i, Set (R i)} (ho : ∀ i, IsOpen (A i))
    (hc : ∀ i, IsCompact (A i)) {κ : Type*} [Finite κ] (v : ι) (φ : (κ → R v) → ℂ)
    (h1 : IsLocallyConstant φ) (h2 : HasCompactSupport φ) (g : (κ → Πʳ i, [R i, A i]) → ℂ)
    (hg : ∀ x, g x = φ (fun i => x i v) *
      Set.indicator {z : κ → Πʳ i, [R i, A i] | ∀ i u, u ≠ v → z i u ∈ A u} 1 x) :
    IsLocallyConstant g ∧ HasCompactSupport g := by
  classical
  set S : Set (κ → Πʳ i, [R i, A i]) := {z | ∀ i u, u ≠ v → z i u ∈ A u} with hS
  have hSo : IsOpen S := by
    rw [hS, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      (RestrictedProduct.isOpen_forall_imp_mem ho (p := fun u => u ≠ v)).preimage
        (f := fun z : κ → Πʳ i, [R i, A i] => z i) (continuous_apply i)
  have hSc : IsClosed S := by
    simp only [hS, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun u => isClosed_iInter fun _ =>
      (hc u).isClosed.preimage
        ((RestrictedProduct.continuous_eval u).comp (continuous_apply i))
  have hev : Continuous fun (x : κ → Πʳ i, [R i, A i]) (i : κ) => x i v :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  have hK : ∀ K : Set (R v), IsCompact K →
      IsCompact {y : Πʳ i, [R i, A i] | y v ∈ K ∧ ∀ u, u ≠ v → y u ∈ A u} := by
    intro K hK
    have hle : (cofinite : Filter ι) ≤ 𝓟 ({v}ᶜ : Set ι) := by simp
    have hQ : IsCompact (Set.univ.pi (Function.update A v K)) :=
      isCompact_univ_pi fun u => by
        by_cases h : u = v
        · subst h; simpa using hK
        · simpa [h] using hc u
    have hP := (RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
      (S := ({v}ᶜ : Set ι))).isCompact_preimage_iff (K := Set.univ.pi (Function.update A v K))
      (by
        rw [RestrictedProduct.range_coe_principal]
        intro x hx u hu
        have h : u ≠ v := hu
        simpa [h] using hx u trivial) |>.mpr hQ
    convert hP.image (RestrictedProduct.continuous_inclusion hle) using 1
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      refine ⟨⟨y.1, hy2⟩, fun u _ => ?_, rfl⟩
      by_cases h : u = v
      · subst h; rw [Function.update_self]; exact hy1
      · rw [Function.update_of_ne h]; exact hy2 u h
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, fun u hu => z.2 hu⟩
      have := hz v trivial
      rw [Function.update_self] at this
      exact this
  constructor
  · have hI : IsLocallyConstant (S.indicator (1 : (κ → Πʳ i, [R i, A i]) → ℂ)) :=
      (LocallyConstant.indicator (1 : LocallyConstant (κ → Πʳ i, [R i, A i]) ℂ)
        (U := S) ⟨hSc, hSo⟩).isLocallyConstant
    rw [funext hg]
    exact (h1.comp_continuous hev).mul hI
  · refine HasCompactSupport.intro (isCompact_univ_pi fun i : κ =>
      hK _ (h2.isCompact.image (continuous_apply i))) fun x hx => ?_
    rw [hg]
    by_cases hxS : x ∈ S
    · by_contra hne
      refine hx fun i _ => ⟨⟨fun j => x j v, ?_, rfl⟩, hxS i⟩
      exact subset_tsupport _ (left_ne_zero_of_mul hne)
    · rw [Set.indicator_of_notMem hxS, mul_zero]

private lemma UpperTheory.valuation_subring_compact {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [Valued K Γ] [(Valued.v : Valuation K Γ).RankOne] [LocallyCompactSpace K] :
    IsCompact ((Valued.v : Valuation K Γ).valuationSubring : Set K) := by
  letI := Valued.toNontriviallyNormedField K Γ
  haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact isCompact_iff_compactSpace.mpr
    (Valued.integer.properSpace_iff_compactSpace_integer.mp this)

theorem UpperTheory.schwartz_function_generation :
    ∀ (F : Type) [Field F] [NumberField F],
        (∀ u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), LocallyCompactSpace (u.adicCompletion F)) →
        ∀ (κ : Type) [Fintype κ] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
          (φ : (κ → v.adicCompletion F) → ℂ), IsLocallyConstant φ → HasCompactSupport φ →
          ∀ g : (κ → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) → ℂ,
            (∀ x, g x = φ (fun i => x i v) *
              Set.indicator {z : κ → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F |
                ∀ i u, u ≠ v → z i u ∈ u.adicCompletionIntegers F} 1 x) →
            IsLocallyConstant g ∧ HasCompactSupport g := by
  intro F _ _ hlc κ _ v φ h1 h2 g hg
  exact UpperTheory.factorizable_generation
    (R := fun u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
      u.adicCompletion F)
    (A := fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)
    (fun u => haveI := hlc u; UpperTheory.valuation_subring_compact) v φ h1 h2 g hg
end

section
noncomputable section

namespace UpperTheory.Reformulated.B.SingleLocalAdele

open GlobalTheory.WeilM Matrix

section Local





variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [Invertible (2 : K)]
  {ψ : AddChar K ℂ} {κ : Type} [Fintype κ] [DecidableEq κ]



end Local

section Global

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private def sL (v : Pl F) : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

private theorem eval_single_local (v : Pl F) (a : Fv F v) : evFin F v (sL v a) = a := evalV_singleFin_self v a

private theorem mul_s (v : Pl F) (u : AF F) (a : Fv F v) : u * sL v a = sL v (evFin F v u * a) := by
  refine Prod.ext ((mul_zero _).trans rfl) (af_ext fun w => ?_)
  change evalV F w (u.2 * singleFin v a) = evalV F w (singleFin v (evFin F v u * a))
  rw [map_mul]
  by_cases h : w = v
  · subst h; rw [evalV_singleFin_self, evalV_singleFin_self]; rfl
  · rw [evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]

private theorem sL_one_mul_eq_sL_evFin (v : Pl F) (u : AF F) : sL v 1 * u = sL v (evFin F v u) := by
  rw [mul_comm, mul_s, mul_one]

private theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl F) (z : M) :
    At (evFin F v) z ↔ sL v 1 • z = z := by
  refine ⟨fun h => ?_, fun h u hu => ?_⟩
  · have := h (1 - sL v 1) (by rw [map_sub, map_one, eval_single_local, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · rw [← h, smul_smul, mul_s, hu, zero_mul, map_zero, zero_smul]


private def psiK (ψ : AddChar (AF F) ℂ) (v : Pl F) : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom (sL v).toAddMonoidHom

private theorem psi_at (ψ : AddChar (AF F) ℂ) (v : Pl F) {a : AF F} (h : sL v 1 * a = a) :
    ψ a = psiK ψ v (evFin F v a) := by
  rw [sL_one_mul_eq_sL_evFin] at h
  exact (congrArg ψ h).symm


private theorem exists_schwartz (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ f : SchwartzMap V ℂ, f 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) := b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) rfl
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]

private def evp {κ : Type} (v : Pl F) (w : (κ → AF F) × (κ → AF F)) : (κ → Fv F v) × (κ → Fv F v) :=
  (fun i => evFin F v (w.1 i), fun i => evFin F v (w.2 i))

private theorem ev_dot {κ : Type} [Fintype κ] (v : Pl F) (a b : κ → AF F) :
    evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ fun i => evFin F v (b i) := by
  simp only [dotProduct, map_sum, map_mul]

open Classical in
private theorem acts_eq {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : Pl F) [Invertible (2 : Fv F v)]
    {w : (κ → AF F) × (κ → AF F)} (hw : sL v 1 • w = w) {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _)
    (h : Acts (evFin F v) (schr ψ w) φ φ₁) : φ₁ = schr (psiK ψ v) (evp v w) φ := by
  obtain ⟨f, hf⟩ := exists_schwartz (κ → mixedEmbedding.mixedSpace F)
  let S : Set (κ → Af F) := {z | ∀ i u, u ≠ v → z i u ∈ u.adicCompletionIntegers F}
  let r : (κ → AF F) → ℂ := fun x => f (fun i => evI F (x i)) * S.indicator 1 fun i => (x i).2
  have hr : ∀ x z : κ → AF F, sL v 1 • z = z → r (x + z) = r x := fun x z hz => by
    have h0 : ∀ i, z i = sL v (evFin F v (z i)) := fun i => (congrFun hz i).symm.trans (sL_one_mul_eq_sL_evFin v _)
    have h1 : (fun i => evI F ((x + z) i)) = fun i => evI F (x i) := funext fun i => by
      have : (z i).1 = 0 := by rw [h0]; rfl
      change InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (z i).1) = _
      rw [this, add_zero]; rfl
    have h2 : (fun i => ((x + z) i).2) ∈ S ↔ (fun i => (x i).2) ∈ S := by
      refine forall_congr' fun i => forall_congr' fun u => forall_congr' fun hu => ?_
      have : evalV F u (z i).2 = 0 := by rw [h0]; exact evalV_singleFin_ne hu _
      change evalV F u ((x i).2 + (z i).2) ∈ _ ↔ evalV F u (x i).2 ∈ _
      rw [map_add, this, add_zero]
    simp only [r, h1, Set.indicator, h2, Pi.one_apply]
  have hg := UpperTheory.schwartz_function_generation F (fun u => (locField u).toLocallyCompactSpace) κ v φ hφ.1 hφ.2 _ fun _ => rfl
  have hR : Rest (evFin F v) φ r := ⟨fun x z hz => hr x z ((at_iff v z).1 hz),
    Submodule.subset_span ⟨f, _, hg, funext fun x => mul_left_comm _ _ _⟩⟩
  have hr0 : r 0 = 1 := by
    have h1 : (fun i => evI F ((0 : κ → AF F) i)) = 0 := funext fun i => map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h2 : (fun i => ((0 : κ → AF F) i).2) ∈ S := fun i u _ => zero_mem _
    simp only [r, h1, hf, Set.indicator_of_mem h2, Pi.one_apply, mul_one]
  funext X
  let x : κ → AF F := fun i => sL v (X i)
  have hx : sL v 1 • x = x := funext fun i => by
    change sL v 1 * sL v (X i) = sL v (X i)
    rw [sL_one_mul_eq_sL_evFin, eval_single_local]
  have hw1 : sL v 1 • w.1 = w.1 := congrArg Prod.fst hw
  have hw2 : sL v 1 • w.2 = w.2 := congrArg Prod.snd hw
  have hx1 : r x = 1 := by rw [← zero_add x, hr _ _ hx, hr0]
  have hX : (fun i => evFin F v (x i)) = X := funext fun i => eval_single_local v _
  have h2 : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]
  have := congrFun (h r hR) x
  simp only [tens, schr] at this
  rw [hr _ _ hw1, hx1, hX, mul_one, mul_one, psi_at ψ v (by
    rw [mul_add, mul_left_comm, ← smul_eq_mul (sL v 1), ← smul_eq_mul (sL v 1), ← dotProduct_smul, ← dotProduct_smul,
      hw2]), map_add, map_mul, ev_dot, ev_dot, hX, h2] at this
  rw [← this]
  simp only [schr, evp, Pi.add_apply, map_add]
  congr 2
  funext i
  exact congrArg (· + _) (eval_single_local v _)



private theorem rT_smul (v : Pl F) (a : Fv F v) (y : Fv F v ⊗[F] E) :
    LinearMap.rTensor E (sL v) (a • y) = sL v a • LinearMap.rTensor E (sL v) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul b e =>
    refine congrArg (· ⊗ₜ[F] e) (?_ : sL v (a * b) = sL v a * sL v b)
    rw [mul_s, eval_single_local]


variable {n d : ℕ}


private def liftM (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) : Matrix (Fin n) (Fin d) (AE F E) :=
  Matrix.of fun i j => LinearMap.rTensor E (sL v) ((splitAlgEquiv h t).symm (p.1 (i, j), p.2 (i, j)))

variable (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v)







end Global

section Main

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}


end Main

end UpperTheory.Reformulated.B.SingleLocalAdele

end
end
