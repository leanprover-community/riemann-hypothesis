import Mathlib

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

