module

public import Lib.DiscreteSeries.Bruhat.QuadricBlocks
public import Lib.SiegelWeil.OneVector.FinitePlaceDensity

/-!
# The quadrics of the standard form at a finite place

At a finite place the standard hermitian form of rank at least two has a basis that begins with a
hyperbolic pair, and an integral basis of hyperbolic pairs followed by orthonormal vectors. So the
volume disintegrates along the form, and on a quadric the mass of a box is bounded by the integral
of the content index over the box.

* `New.Floors.IntegralPlace.isDisintegration_of_hyperbolic_basis`: the disintegration.
* `New.Floors.IntegralPlace.quadricMeasure_coordinateBox_le`: the mass of a box on a quadric of
  hyperbolic planes plus a form.
* `New.Floors.IntegralPlace.exists_kernel_isDisintegration_le`: if ζ_R(μ) ≤ 2 and the rank is at
  least 2μ + 4, then some s-finite kernel is a disintegration of the volume for which the points y
  of a quadric with u y integral, for a unit u, have bounded mass.

Notions from other files:
* `New.Floors.Place.IsDisintegration`: a family of measures on the quadrics of a form, continuous
  in the index, whose integral over the index is a given measure.
* `New.Floors.Place.quadricMeasure`: the measure on a quadric of a hyperbolic plane plus a form.
* `New.idealZeta`: the sum ζ_R(s) of [R : I]^(−s) over the ideals I of finite index in R.
* `New.Floors.IntegralPlace.contentIndex`: the volume of the set of c with c p integral, for a
  vector p with a unit entry.
* `New.Floors.coordinateBox`: the vectors with all coordinates in a given set.

## Relation to the literature

Known result: a local density bound for hermitian forms. See
`Lib.SiegelWeil.OneVector.SiegelClassSum`.
-/

@[expose] public section

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure ProbabilityTheory ENNReal Fintype FloorGroups Place SemilocalField
  Function

section Place

variable {A ι κ : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  [P : Place A] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Let `B` have as many columns as rows, with Gram matrix `planeSumGram S` for the form `T`: a
hyperbolic plane plus `S`. Let `det T` have modulus one (a matrix scales the volume by the modulus
of its determinant) and let `S` be hermitian with `S * S = 1`, so that the columns of `B` are a
basis. Then `B` carries the measures `P.quadricMeasure S b`, on the quadrics of norm `δ⁻¹ b` for
`planeSumGram S` (`δ = P.skewUnit`), to a disintegration of the volume along `T`: they are the fiber
measures of the volume on the quadrics `x* T x = δ⁻¹ b`. -/
lemma Place.isDisintegration_map_quadricMeasure {T : Matrix ι ι A}
    {S : Matrix κ κ A} {B : Matrix ι (Fin 2 ⊕ κ) A} (h_gram : Bᴴ * T * B = planeSumGram S)
    (h_card : card ι = card (Fin 2 ⊕ κ)) (hT : P.modulus T.det = 1) (hS : Sᴴ = S)
    (hS_sq : S * S = 1) :
    P.IsDisintegration volume T
      fun b : skewAdjoint A ↦ (P.quadricMeasure S b).map (B *ᵥ ·) := by
  have h_plane : planeSumGram S * planeSumGram S = 1 := by
    simp [fromBlocks_multiply, hS_sq, ← one_fin_two]
  -- Reindex the columns of `B` to get a square matrix `M`. Its Gram matrix has square one.
  let e : ι ≃ Fin 2 ⊕ κ := equivOfCardEq h_card
  let M : Matrix ι ι A := B * inclMatrix A e
  have gram_sq : (Mᴴ * T * M) ^ 2 = 1 := by
    rw [gram_mul, h_gram, conjTranspose_inclMatrix_mul_mul_inclMatrix, sq, submatrix_mul_equiv,
      h_plane, submatrix_one_equiv]
  have h_unit : IsUnit M.det := by
    rw [sq, ← mul_assoc] at gram_sq
    exact isUnit_det_of_left_inverse gram_sq
  -- Taking determinants, `modulus M.det ^ 4 = 1`; so `B` keeps the volume.
  have h_mod : P.modulus M.det = 1 := by
    have h_star : P.modulus (star M.det) = P.modulus M.det := (P.modulus_star_and_neg M.det).left
    have h_pow : P.modulus M.det ^ 4 = 1 :=
      calc
        P.modulus M.det ^ 4 = (P.modulus (star M.det) * P.modulus T.det * P.modulus M.det) ^ 2 := by
          rw [h_star, hT]
          ring
        _ = P.modulus ((Mᴴ * T * M) ^ 2).det := by
          simp only [det_pow, det_mul, det_conjTranspose, map_pow, map_mul]
        _ = 1 := by rw [gram_sq, det_one, map_one]
    exact (ENNReal.pow_right_strictMono four_ne_zero).injective (h_pow.trans (one_pow 4).symm)
  have h_vol : volume.map (B *ᵥ ·) = volume :=
    calc
      volume.map (B *ᵥ ·) = (volume.map (inclMatrix A e *ᵥ ·)).map (B *ᵥ ·) := by
        rw [(measurePreserving_inclMatrix e).map_eq]
      _ = volume.map (M *ᵥ ·) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        simp only [M, comp_def, mulVec_mulVec]
      _ = volume := by rw [P.map_mulVec_volume ι M h_unit, h_mod, inv_one, one_smul]
  have h_left : planeSumGram S * (Bᴴ * T) * B = 1 := by
    rw [Matrix.mul_assoc, h_gram, h_plane]
  rw [← h_vol]
  exact (isDisintegration_quadricMeasure hS).map h_gram h_left

end Place

/-! ### The mass of a box on a quadric of hyperbolic planes -/

section Form

variable {A σ ν : Type} [CommRing A] [StarRing A] [Fintype σ] [DecidableEq σ] [Fintype ν]

/-- The value of the form of `σ` hyperbolic planes plus `T` at a vector with first block `w₁`. -/
lemma star_dotProduct_hyperbolicGram_mulVec (T : Matrix ν ν A) (w₁ : σ → A) (w' : ν ⊕ σ → A) :
    star (w₁ ⊕ᵥ w') ⬝ᵥ hyperbolicGram σ T *ᵥ (w₁ ⊕ᵥ w') =
      star w₁ ⬝ᵥ (fun j ↦ w' (.inr j)) + star (fun j ↦ w' (.inr j)) ⬝ᵥ w₁ +
        star (fun k ↦ w' (.inl k)) ⬝ᵥ T *ᵥ (fun k ↦ w' (.inl k)) := by
  simp [hyperbolicGram, dotProduct, mulVec, Fintype.sum_sum_type, Matrix.one_apply, mul_add,
    Finset.sum_add_distrib]
  ring

end Form

namespace IntegralPlace

open Sum Set

variable {A : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A]
  {σ ν : Type} [Fintype σ] [DecidableEq σ] [Fintype ν] [DecidableEq ν]

/-- The box of the vectors `y` with `u y` integral is measurable. -/
lemma measurableSet_coordinateBox (κ : Type) [Finite κ] (u : Aˣ) :
    MeasurableSet (coordinateBox κ {x : A | u.val * x ∈ P.integers}) := by
  have h_eq : coordinateBox κ {x : A | u.val * x ∈ P.integers} =
      ⋂ i, (fun v : κ → A ↦ u.val * v i) ⁻¹' (P.integers : Set A) := by
    ext v
    simp
  rw [h_eq]
  exact .iInter fun i ↦ isCompact_O.measurableSet.preimage (by fun_prop)

/-- Let `ζ_R(μ) ≤ 2` and let `σ` have at least `μ + 1` elements. On the quadric of any skew `b`
for one hyperbolic plane, the hyperbolic planes indexed by `σ` and a hermitian form `T`, the points
`y` with `u y` integral, `u` a unit, have mass at most `ζ_R(μ) |u|^(-d)`, where `d + 1` is the
rank.

Fix the half `v` of the hyperbolic coordinates indexed by `σ` that is paired with the first block
`w₁`. The form is linear in `w₁`, so moving `w₁` along an integral vector `r` with `r · v = c`, the
content of `v`, moves the quadric of `b` to that of `b + x`, for `x` in a set of skew elements of
measure `|c|`, and keeps the box. So the mass on one quadric is at most `|c|⁻¹`, the content index
of `v`, times the mass on all quadrics, which is the volume
(`lintegral_form_eq_lintegral_flatChart`), and `lintegral_contentIndex_pow_le` bounds the integral
of the content index over the box. -/
theorem quadricMeasure_coordinateBox_le {μ : ℕ} (hμ : idealZeta P.integers μ ≤ 2)
    (hσ : μ + 1 ≤ card σ) {T : Matrix ν ν A} (hT : Tᴴ = T) (b : skewAdjoint A) (u : Aˣ) :
    P.quadricMeasure (hyperbolicGram σ T) b
        (coordinateBox (Fin 2 ⊕ σ ⊕ ν ⊕ σ) {x : A | u.val * x ∈ P.integers}) ≤
      idealZeta P.integers μ * (P.modulus u)⁻¹ ^ (2 * card σ + card ν + 1) := by
  classical
  obtain ⟨i₀⟩ : Nonempty σ := card_pos_iff.1 (by lia)
  have hH : (hyperbolicGram σ T)ᴴ = hyperbolicGram σ T := by
    simp [hyperbolicGram, fromBlocks_conjTranspose,
      conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, hT]
  set H : Matrix (σ ⊕ ν ⊕ σ) (σ ⊕ ν ⊕ σ) A := hyperbolicGram σ T with hH_def
  let S : Set (Fin 2 ⊕ σ ⊕ ν ⊕ σ → A) := coordinateBox _ {x : A | u.val * x ∈ P.integers}
  have hS : MeasurableSet S := measurableSet_coordinateBox _ u
  let ind : (Fin 2 ⊕ σ ⊕ ν ⊕ σ → A) → ℝ≥0∞ := S.indicator 1
  have h_ind : Measurable ind := measurable_one.indicator hS
  -- The mass of the box in the fibre of the chart over `p`, on the quadric of `β`.
  let F (β : skewAdjoint A) (p : A × (σ ⊕ ν ⊕ σ → A)) : ℝ≥0∞ :=
    ∫⁻ a, ind (flatChart H β (p, a)) ∂P.skewMeasure
  have hF : Measurable fun q : skewAdjoint A × A × (σ ⊕ ν ⊕ σ → A) ↦ F q.1 q.2 :=
    (h_ind.comp (measurable_flatChart.comp (by fun_prop :
      Measurable fun z : (skewAdjoint A × A × (σ ⊕ ν ⊕ σ → A)) × skewAdjoint A ↦
        (z.1.1, (z.1.2, z.2))))).lintegral_prod_right'
  let W (w' : ν ⊕ σ → A) : ℝ≥0∞ := contentIndex i₀ fun j : σ ↦ w' (inr j)
  have hW : Measurable W := by fun_prop
  let Φ (x : Fin 2 ⊕ σ ⊕ ν ⊕ σ → A) : ℝ≥0∞ := ind x * W fun k ↦ x (inr (inr k))
  have hΦ : Measurable Φ := h_ind.mul (hW.comp (by fun_prop :
    Measurable fun x : Fin 2 ⊕ σ ⊕ ν ⊕ σ → A ↦ fun k : ν ⊕ σ ↦ x (inr (inr k))))
  let M (p : A × (σ ⊕ ν ⊕ σ → A)) : ℝ≥0∞ := ∫⁻ s : A, Φ (![s, p.1] ⊕ᵥ p.2)
  have hΦ_pair : Measurable fun z : A × A × (σ ⊕ ν ⊕ σ → A) ↦ Φ (![z.1, z.2.1] ⊕ᵥ z.2.2) :=
    hΦ.comp measurePreserving_pair_sumElim.measurable
  have hM : Measurable M := hΦ_pair.lintegral_prod_left'
  -- Integrals over the parameters `(t, w)` of the chart, with the first block of `w` innermost.
  have h_split {g : A × (σ ⊕ ν ⊕ σ → A) → ℝ≥0∞} (hg : Measurable g) :
      ∫⁻ p, g p = ∫⁻ t : A, ∫⁻ w' : ν ⊕ σ → A, ∫⁻ w₁ : σ → A, g (t, w₁ ⊕ᵥ w') := by
    rw [volume_eq_prod, lintegral_prod _ hg.aemeasurable]
    refine lintegral_congr fun t ↦ ?_
    have hg_t : Measurable fun y : σ ⊕ ν ⊕ σ → A ↦ g (t, y) := by fun_prop
    rw [← (measurePreserving_sumElim (A := A) (ι := σ) (κ := ν ⊕ σ)).lintegral_comp hg_t,
      volume_eq_prod, lintegral_prod_symm' (fun a : (σ → A) × (ν ⊕ σ → A) ↦ g (t, a.1 ⊕ᵥ a.2))
        (hg_t.comp measurable_sumElim_pair)]
  have h_chart : Measurable fun z : (A × (σ ⊕ ν ⊕ σ → A)) × skewAdjoint A ↦ flatChart H b z :=
    ((measurable_flatChart (T := H)).comp measurable_prodMk_left :)
  have h_left : P.quadricMeasure H b S = ∫⁻ p, F b p := by
    rw [← lintegral_indicator_one hS, quadricMeasure, lintegral_map h_ind h_chart,
      lintegral_prod (fun z ↦ ind (flatChart H b z)) (h_ind.comp h_chart).aemeasurable]
  have h_mid : ∫⁻ p, M p = ∫⁻ x, Φ x :=
    calc ∫⁻ p, M p = ∫⁻ r : A × A × (σ ⊕ ν ⊕ σ → A), Φ (![r.1, r.2.1] ⊕ᵥ r.2.2) :=
          (lintegral_prod_symm' _ hΦ_pair).symm
      _ = ∫⁻ x, Φ x := measurePreserving_pair_sumElim.lintegral_comp hΦ
  have h_final : ∫⁻ x, Φ x ≤
      idealZeta P.integers μ * (P.modulus u)⁻¹ ^ (2 * card σ + card ν + 1) := by
    let eσ : (Fin 2 ⊕ σ ⊕ ν) ⊕ σ ≃ Fin 2 ⊕ σ ⊕ ν ⊕ σ :=
      (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumAssoc _ _ _))
    have h_card : card (Fin 2 ⊕ σ ⊕ ν) + (card σ - 1) = 2 * card σ + card ν + 1 := by
      simp only [card_sum, card_fin]
      lia
    have h_le := lintegral_contentIndex_pow_le (P := P) (s := 1) hμ (k := card σ - 1) eσ i₀
      (V := 1) u (one_mem _) ⟨h_card, by lia, by lia⟩
    calc ∫⁻ x, Φ x = ∫⁻ x in S, W fun k ↦ x (inr (inr k)) := by
          rw [← lintegral_indicator hS]
          refine lintegral_congr fun x ↦ ?_
          by_cases hx : x ∈ S <;> simp [Φ, ind, hx]
      _ ≤ _ := by simpa [eσ, W, S, coordinateBox, Fin.forall_fin_two] using h_le
  rw [h_left]
  refine le_trans ?_ (h_mid.le.trans h_final)
  have hFb : Measurable fun p : A × (σ ⊕ ν ⊕ σ → A) ↦ F b p :=
    (hF.comp measurable_prodMk_left :)
  rw [h_split hFb, h_split hM]
  refine lintegral_le_of_ae_imp P.ae_isUnit fun t' ht ↦ ?_
  obtain ⟨t, rfl⟩ := ht
  refine lintegral_le_of_ae_imp ((tendsto_eval_ae_ae (i := inr i₀)).eventually P.ae_isUnit)
    fun w' (hw' : IsUnit (w' (inr i₀))) ↦ ?_
  -- The content `c` of the last block `v` of `w'`.
  let v : σ → A := fun j ↦ w' (inr j)
  obtain ⟨c, r, hr, hrv, hc⟩ := exists_content (p := v) hw'
  have hW_eq : W w' = (P.modulus c)⁻¹ := by
    have h_set : {a : A | ∀ j : σ, a * w' (inr j) ∈ P.integers} = {a | c.val * a ∈ P.integers} :=
      Set.ext hc
    simp only [W, contentIndex, iInf_pos hw', h_set, volume_setOf_mul_mem]
  have h_ne_zero : P.modulus c ≠ 0 := by simp
  have h_ne_top : P.modulus c ≠ ∞ := by simp
  -- The integral over `s` is the integral over all quadrics.
  have hM_eq (w₁ : σ → A) : M (↑t, w₁ ⊕ᵥ w') =
      (∫⁻ β, F β (↑t, w₁ ⊕ᵥ w') ∂P.skewMeasure) * (P.modulus c)⁻¹ := by
    have h_form := lintegral_form_eq_lintegral_flatChart hH (f := fun q ↦ ind q.2)
      (h_ind.comp measurable_snd) t (w₁ ⊕ᵥ w')
    calc M (↑t, w₁ ⊕ᵥ w') = ∫⁻ s : A, ind (![s, ↑t] ⊕ᵥ (w₁ ⊕ᵥ w')) * (P.modulus c)⁻¹ := by
          simp only [M, Φ, ← hW_eq, W, elim_inr]
      _ = (∫⁻ s : A, ind (![s, ↑t] ⊕ᵥ (w₁ ⊕ᵥ w'))) * (P.modulus c)⁻¹ :=
          lintegral_mul_const' _ _ (by simp)
      _ = _ := by rw [h_form]
  simp only [hM_eq]
  -- The skew elements by which the quadric may be moved.
  let K : Set (skewAdjoint A) := {x | ((c * star c)⁻¹ : Aˣ).val * x.val ∈ P.integers}
  have hK_meas : MeasurableSet K := isCompact_O.measurableSet.preimage (by fun_prop)
  have hK : P.skewMeasure K = P.modulus c := by
    have h_star : star ((c * star c)⁻¹ : Aˣ).val = ((c * star c)⁻¹ : Aˣ) := by
      rw [← Units.coe_star, star_inv, star_mul, star_star]
    rw [skewMeasure_setOf_mul_mem _ h_star]
    simp [modulus_inv, ← sq, ← rpow_natCast_mul]
  -- Moving the first block along `star r` moves the value of the form by `δ⁻¹ x`.
  let y (x : skewAdjoint A) : A := P.element * P.skewUnit⁻¹.val * x.val * c⁻¹.val
  let e (x : skewAdjoint A) : σ → A := star (y x) • star r
  have hδ : star P.skewUnit⁻¹.val = -P.skewUnit⁻¹.val := by
    have h1 : P.skewUnit.val * P.skewUnit⁻¹.val = 1 := Units.mul_inv _
    have h2 := congrArg star h1
    rw [star_mul, P.star_skewUnit, star_one] at h2
    linear_combination (-P.skewUnit⁻¹.val) * h2 + (-star P.skewUnit⁻¹.val) * h1
  have h_e (x : skewAdjoint A) :
      star (e x) ⬝ᵥ v + star v ⬝ᵥ e x = P.skewUnit⁻¹.val * x.val := by
    have h_star : star (e x) = y x • r := by
      ext j
      simp [e]
    have hx : star x.val = -x.val := skewAdjoint.star_val_eq
    have hy : y x * c = P.element * P.skewUnit⁻¹.val * x.val := by
      simp only [y]
      linear_combination (P.element * P.skewUnit⁻¹.val * x.val) * c.inv_mul
    have h_conj : star v ⬝ᵥ e x = star (y x * c) := by
      rw [dotProduct_smul, star_dotProduct_star, hrv, smul_eq_mul]
      exact (star_mul' _ _).symm
    rw [h_star, smul_dotProduct, hrv, smul_eq_mul, h_conj, hy, star_mul, star_mul, hδ, hx]
    linear_combination (P.skewUnit⁻¹.val * x.val) * P.element_add_star
  have h_mem (s : A) (w₁ : σ → A) : (![s, ↑t] ⊕ᵥ (w₁ ⊕ᵥ w')) ∈ S ↔
      (u.val * s ∈ P.integers ∧ u.val * t ∈ P.integers) ∧ (∀ j, u.val * w₁ j ∈ P.integers) ∧
        ∀ k, u.val * w' k ∈ P.integers := by
    simp [S, Fin.forall_fin_two]
  have h_pt {x : skewAdjoint A} (hx : x ∈ K) (w₁ : σ → A) (a : skewAdjoint A) :
      ind (flatChart H b ((↑t, w₁ ⊕ᵥ w'), a)) =
        ind (flatChart H (b + x) ((↑t, (w₁ + e x) ⊕ᵥ w'), a)) := by
    have h_value : P.skewUnit⁻¹.val * (b + x : skewAdjoint A).val -
          star ((w₁ + e x) ⊕ᵥ w') ⬝ᵥ H *ᵥ ((w₁ + e x) ⊕ᵥ w') =
        P.skewUnit⁻¹.val * b.val - star (w₁ ⊕ᵥ w') ⬝ᵥ H *ᵥ (w₁ ⊕ᵥ w') := by
      rw [hH_def, star_dotProduct_hyperbolicGram_mulVec, star_dotProduct_hyperbolicGram_mulVec,
        star_add, add_dotProduct, dotProduct_add, AddSubgroup.coe_add]
      linear_combination -h_e x
    simp only [flatChart, h_value]
    change S.indicator 1 _ = S.indicator 1 _
    rw [indicator_apply, indicator_apply]
    refine if_congr ?_ rfl rfl
    rw [h_mem, h_mem]
    refine and_congr_right fun _ ↦ ⟨fun h ↦ ⟨?_, h.2⟩, fun h ↦ ⟨?_, h.2⟩⟩
    all_goals
      have hcu : c.val * u.val ∈ P.integers := (hc u).1 fun j ↦ h.2 (inr j)
      have hu_e (j : σ) : u.val * e x j ∈ P.integers := by
        let ρ : A := ((c * star c)⁻¹ : Aˣ).val * x.val
        have hρ : ρ ∈ P.integers := hx
        have hx_eq : x.val = ((c * star c : Aˣ) : A) * ρ :=
          (Units.mul_inv_cancel_left (c * star c) x.val).symm
        have hy : y x = P.element * P.skewUnit⁻¹.val * star c.val * ρ := by
          simp only [y, hx_eq, Units.val_mul, Units.coe_star]
          linear_combination (P.element * P.skewUnit⁻¹.val * star c.val * ρ) * c.mul_inv
        have h_eq : u.val * e x j = c.val * u.val *
            (star P.element * star P.skewUnit⁻¹.val * star ρ * star (r j)) := by
          simp only [e, Pi.smul_apply, Pi.star_apply, smul_eq_mul, hy, star_mul, star_star]
          ring
        rw [h_eq]
        have h_star {z : A} (hz : z ∈ P.integers) : star z ∈ P.integers :=
          P.isAdelic.toIsStarStable.star_mem hz
        exact mul_mem hcu (mul_mem (mul_mem (mul_mem (h_star P.element_mem)
          (h_star P.skewUnit_inv_mem)) (h_star hρ)) (h_star (hr j)))
      intro j
    · simpa [mul_add] using add_mem (h.1 j) (hu_e j)
    · simpa [mul_add] using (add_mem_cancel_right (hu_e j)).1 (by simpa [mul_add] using h.1 j)
  have h_shift : ∀ x ∈ K, ∫⁻ w₁ : σ → A, F b (↑t, w₁ ⊕ᵥ w') =
      ∫⁻ w₁ : σ → A, F (b + x) (↑t, w₁ ⊕ᵥ w') := fun x hx ↦
    calc ∫⁻ w₁ : σ → A, F b (↑t, w₁ ⊕ᵥ w')
        = ∫⁻ w₁ : σ → A, F (b + x) (↑t, (w₁ + e x) ⊕ᵥ w') :=
          lintegral_congr fun w₁ ↦ lintegral_congr fun a ↦ h_pt hx w₁ a
      _ = _ := lintegral_add_right_eq_self (fun w₁ : σ → A ↦ F (b + x) (↑t, w₁ ⊕ᵥ w')) (e x)
  have h_elim : Measurable fun w₁ : σ → A ↦ (w₁ ⊕ᵥ w' : σ ⊕ ν ⊕ σ → A) :=
    measurable_sumElim_pair.comp (measurable_id.prodMk measurable_const)
  have h_swap : AEMeasurable (uncurry fun (x : skewAdjoint A) (w₁ : σ → A) ↦
      F (b + x) (↑t, w₁ ⊕ᵥ w')) (P.skewMeasure.prod volume) :=
    (hF.comp ((measurable_const.add measurable_fst).prodMk
      (measurable_const.prodMk (h_elim.comp measurable_snd)))).aemeasurable
  calc ∫⁻ w₁ : σ → A, F b (↑t, w₁ ⊕ᵥ w')
      = (P.modulus c)⁻¹ * ((∫⁻ w₁ : σ → A, F b (↑t, w₁ ⊕ᵥ w')) * P.skewMeasure K) := by
        rw [hK, mul_left_comm, ENNReal.inv_mul_cancel h_ne_zero h_ne_top, mul_one]
    _ = (P.modulus c)⁻¹ * ∫⁻ x in K, (∫⁻ w₁ : σ → A, F (b + x) (↑t, w₁ ⊕ᵥ w')) ∂P.skewMeasure := by
        rw [← setLIntegral_const, setLIntegral_congr_fun hK_meas h_shift]
    _ ≤ (P.modulus c)⁻¹ * ∫⁻ x, (∫⁻ w₁ : σ → A, F (b + x) (↑t, w₁ ⊕ᵥ w')) ∂P.skewMeasure := by
        gcongr
        exact Measure.restrict_le_self
    _ = (P.modulus c)⁻¹ * ∫⁻ w₁ : σ → A, ∫⁻ x, F (b + x) (↑t, w₁ ⊕ᵥ w') ∂P.skewMeasure := by
        rw [lintegral_lintegral_swap h_swap]
    _ = (P.modulus c)⁻¹ * ∫⁻ w₁ : σ → A, ∫⁻ β, F β (↑t, w₁ ⊕ᵥ w') ∂P.skewMeasure := by
        congr 2 with w₁
        exact lintegral_add_left_eq_self (fun β ↦ F β (↑t, w₁ ⊕ᵥ w')) b
    _ = ∫⁻ w₁ : σ → A, (∫⁻ β, F β (↑t, w₁ ⊕ᵥ w') ∂P.skewMeasure) * (P.modulus c)⁻¹ := by
        rw [← lintegral_const_mul' _ _ (by simp)]
        simp only [mul_comm]

end IntegralPlace

/-! ### The standard form -/

variable {A κ : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] [Fintype κ]

/-- A finite type with at least two elements has the cardinality of a pair plus a rest. -/
lemma card_eq_card_pair_sum (h : 2 ≤ card κ) : card κ = card (Fin 2 ⊕ Fin (card κ - 2)) := by
  rw [card_sum, card_fin, card_fin, Nat.add_sub_cancel' h]

/-- An orthonormal block splits integrally into hyperbolic pairs indexed by `σ` and
orthonormal vectors indexed by `ν`. -/
lemma IntegralPlace.exists_integral_hyperbolicBlock (σ ν : Type) [Fintype σ] [DecidableEq σ]
    [Fintype ν] [DecidableEq ν] :
    ∃ C : Matrix (σ ⊕ ν ⊕ σ) (σ ⊕ ν ⊕ σ) A,
      Cᴴ * C = hyperbolicGram σ 1 ∧ IsIntMatrix P.integers C := by
  obtain ⟨c, hc_mem, hc⟩ := P.isAdelic.exists_norm_neg_one
  have hτ := P.element_add_star
  -- For each index in `σ`, replace the orthonormal vectors `x`, `y` by
  -- `x + c y`, `τ̄ x - τ c y`, where `τ = P.element` has trace one.
  let C' : Matrix (σ ⊕ ν ⊕ σ) (σ ⊕ ν ⊕ σ) A :=
    fromBlocks 1 (fromCols 0 (star P.element • 1)) (fromRows 0 (c • 1))
      (fromBlocks 1 0 0 (-(P.element * c) • 1))
  have hC' : C'ᴴ * C' = hyperbolicGram σ 1 := by
    ext (i | i | i) (j | j | j) <;>
      simp [C', hyperbolicGram, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    all_goals obtain rfl | hij := eq_or_ne j i <;> simp_all <;> grind
  refine ⟨C', hC', ?_⟩
  rintro (i | i | i) (j | j | j) <;>
    simp [C', Matrix.one_apply, ite_mem, mul_mem, hc_mem, P.element_mem,
      IsStarStable.star_mem]

/-- At a finite place, the standard hermitian form has an integral basis that consists of one
hyperbolic pair, the hyperbolic pairs indexed by `σ`, and orthonormal vectors indexed by `ν`: its
Gram matrix is `planeSumGram (hyperbolicGram σ 1)`. -/
lemma IntegralPlace.exists_split_basis {σ ν : Type} [Fintype σ] [DecidableEq σ] [Fintype ν]
    [DecidableEq ν] (h : card κ = card (Fin 2 ⊕ σ ⊕ ν ⊕ σ)) :
    ∃ B : Matrix κ (Fin 2 ⊕ σ ⊕ ν ⊕ σ) A,
      Bᴴ * B = planeSumGram (hyperbolicGram σ (1 : Matrix ν ν A)) ∧ IsIntMatrix P.integers B := by
  -- Give the first hyperbolic pair the extra index `none`.
  obtain ⟨C, hC, h_int⟩ := P.exists_integral_hyperbolicBlock (Option σ) ν
  let row : κ ≃ Option σ ⊕ ν ⊕ Option σ := equivOfCardEq (by simp_all +arith)
  let col : Fin 2 ⊕ σ ⊕ ν ⊕ σ → Option σ ⊕ ν ⊕ Option σ
    | .inl i => if i = 0 then .inl none else .inr (.inr none)
    | .inr (.inl i) => .inl (some i)
    | .inr (.inr (.inl i)) => .inr (.inl i)
    | .inr (.inr (.inr i)) => .inr (.inr (some i))
  refine ⟨C.submatrix row col, ?_, fun i j ↦ h_int (row i) (col j)⟩
  rw [conjTranspose_submatrix, submatrix_mul_equiv, hC]
  ext (i | i | i | i) (j | j | j | j)
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [col, planeSumGram, hyperbolicGram, Matrix.one_apply]

/-- At a finite place, the standard hermitian form of rank at least two has a basis that begins
with a hyperbolic pair and ends with orthonormal vectors: its Gram matrix is `planeSumGram 1`. -/
lemma IntegralPlace.exists_hyperbolic_basis (h : 2 ≤ card κ) :
    ∃ B : Matrix κ (Fin 2 ⊕ Fin (card κ - 2)) A, Bᴴ * B = planeSumGram 1 := by
  -- Take no additional hyperbolic pairs. The remaining columns form the orthonormal block.
  let ν := Fin (card κ - 2)
  obtain ⟨B, hB, -⟩ := P.exists_split_basis (σ := Empty) (ν := ν)
    (by simpa [ν] using card_eq_card_pair_sum h)
  let cols : Fin 2 ⊕ ν → Fin 2 ⊕ Empty ⊕ ν ⊕ Empty := Sum.map id (Sum.inr ∘ Sum.inl)
  refine ⟨B.submatrix (Equiv.refl κ) cols, ?_⟩
  rw [conjTranspose_submatrix, submatrix_mul_equiv, hB]
  ext (i | i) (j | j) <;> rfl

variable [DecidableEq κ]

/-- Let `A` be a finite place and let `κ` have at least two elements. Let `B` be a basis for the
standard form on `κ → A` with Gram matrix `planeSumGram 1`: a hyperbolic pair, then orthonormal
vectors. It carries the measures `P.quadricMeasure 1 b`, for skew `b`, on the quadrics of norm
`δ⁻¹ b` for `planeSumGram 1` (`δ = P.skewUnit`), to a disintegration of the volume along
`x ↦ x* x`: they are its fiber measures on the quadrics `x* x = δ⁻¹ b`. -/
lemma IntegralPlace.isDisintegration_of_hyperbolic_basis (h_rank : 2 ≤ card κ)
    {B : Matrix κ (Fin 2 ⊕ Fin (card κ - 2)) A} (hB : Bᴴ * B = planeSumGram 1) :
    P.IsDisintegration volume (1 : Matrix κ κ A)
      fun b : skewAdjoint A ↦ (P.quadricMeasure 1 b).map (B *ᵥ ·) :=
  have h_gram : Bᴴ * (1 : Matrix κ κ A) * B = planeSumGram 1 := by rw [Matrix.mul_one, hB]
  have h_det : P.modulus (1 : Matrix κ κ A).det = 1 := by simp
  isDisintegration_map_quadricMeasure h_gram (card_eq_card_pair_sum h_rank) h_det
    conjTranspose_one (mul_one 1)

/-- Let A be a finite place, let ζ_R(μ) ≤ 2, and let κ have r + 1 ≥ 2μ + 4 elements. Then the
volume of A^κ disintegrates along the standard form x ↦ x* x into an s-finite kernel l, with l β on
the quadric x* x = δ⁻¹ β for skew β, and for a unit u the set `coordinateBox` of the points y with
all u y_i in R has mass at most ζ_R(μ) |u|^(-r) for each l β. Here R is the ring of integers of A,
δ = `skewUnit`, ζ_R(μ) = `idealZeta R μ` is the sum of [R : I]^(-μ) over the ideals I of finite
index, and |x| = `modulus x` is the factor by which multiplication by x scales the volume of A. -/
theorem IntegralPlace.exists_kernel_isDisintegration_le {μ r : ℕ}
    (hμ : idealZeta P.integers μ ≤ 2) (h_card : card κ = r + 1) (h_rank : 2 * μ + 3 ≤ r) :
    ∃ l : Kernel (skewAdjoint A) (κ → A), IsSFiniteKernel l ∧
      P.IsDisintegration volume (1 : Matrix κ κ A) l ∧
      ∀ (β : skewAdjoint A) (u : Aˣ), l β (coordinateBox κ {x : A | u.val * x ∈ P.integers}) ≤
        idealZeta P.integers μ * (P.modulus u)⁻¹ ^ r := by
  -- A basis of `μ + 2` hyperbolic pairs followed by `r - (2 μ + 3)` orthonormal vectors.
  have h_index : card κ =
      card (Fin 2 ⊕ Fin (μ + 1) ⊕ Fin (r - (2 * μ + 3)) ⊕ Fin (μ + 1)) := by
    simp only [card_sum, card_fin]
    lia
  obtain ⟨B, hB, hB_int⟩ := P.exists_split_basis (σ := Fin (μ + 1))
    (ν := Fin (r - (2 * μ + 3))) h_index
  let S : Matrix (Fin (μ + 1) ⊕ Fin (r - (2 * μ + 3)) ⊕ Fin (μ + 1))
      (Fin (μ + 1) ⊕ Fin (r - (2 * μ + 3)) ⊕ Fin (μ + 1)) A := hyperbolicGram (Fin (μ + 1)) 1
  have hS : Sᴴ = S := by
    simp [S, hyperbolicGram, fromBlocks_conjTranspose,
      conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_fromRows_eq_fromCols_conjTranspose]
  have hS_sq : S * S = 1 := by
    ext (i | i | i) (j | j | j) <;>
      simp [S, hyperbolicGram, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have h_plane : planeSumGram S * planeSumGram S = 1 := by
    simp [fromBlocks_multiply, hS_sq, ← one_fin_two]
  -- The kernel is the image of the measure of the parameters under the flat chart, followed by B.
  obtain ⟨l, h_sfinite, hl⟩ := exists_kernel_eq_map (volume.prod P.skewMeasure)
    (K := fun q : skewAdjoint A ×
        (A × (Fin (μ + 1) ⊕ Fin (r - (2 * μ + 3)) ⊕ Fin (μ + 1) → A)) × skewAdjoint A ↦
      B *ᵥ flatChart S q.1 q.2) (by fun_prop)
  have h_eq : (l : skewAdjoint A → Measure (κ → A)) =
      fun b : skewAdjoint A ↦ (P.quadricMeasure S b).map (B *ᵥ ·) := by
    ext1 b
    rw [hl, Measure.map_map (by fun_prop) (by fun_prop), comp_def]
  have h_dis : P.IsDisintegration volume (1 : Matrix κ κ A) l := by
    rw [h_eq]
    exact isDisintegration_map_quadricMeasure (by rw [Matrix.mul_one, hB]) h_index (by simp) hS
      hS_sq
  refine ⟨l, h_sfinite, h_dis, fun β u ↦ ?_⟩
  -- `B` has an integral left inverse, so it maps into the box only points of the box.
  have h_gram_int : IsIntMatrix P.integers (planeSumGram S) := by
    rintro (i | i | i | i) (j | j | j | j) <;> try fin_cases i <;> try fin_cases j
    all_goals simp [S, hyperbolicGram, Matrix.one_apply]
    all_goals split_ifs <;> simp
  have h_left : planeSumGram S * Bᴴ * B = 1 := by rw [Matrix.mul_assoc, hB, h_plane]
  have h_box : (B *ᵥ ·) ⁻¹' coordinateBox κ {x : A | u.val * x ∈ P.integers} ⊆
      coordinateBox _ {x : A | u.val * x ∈ P.integers} := by
    intro y hy i
    have h_eq : u.val • y = (planeSumGram S * Bᴴ) *ᵥ (u.val • B *ᵥ y) := by
      rw [mulVec_smul, mulVec_mulVec, h_left, one_mulVec]
    have h_int := (h_gram_int.mul hB_int.conjTranspose).mulVec (v := u.val • B *ᵥ y) hy i
    rw [← h_eq] at h_int
    exact h_int
  calc l β (coordinateBox κ {x : A | u.val * x ∈ P.integers})
      = P.quadricMeasure S β ((B *ᵥ ·) ⁻¹' coordinateBox κ {x : A | u.val * x ∈ P.integers}) := by
        rw [h_eq]
        exact map_apply (by fun_prop) (measurableSet_coordinateBox κ u)
    _ ≤ P.quadricMeasure S β (coordinateBox _ {x : A | u.val * x ∈ P.integers}) :=
        measure_mono h_box
    _ ≤ idealZeta P.integers μ * (P.modulus u)⁻¹ ^
          (2 * card (Fin (μ + 1)) + card (Fin (r - (2 * μ + 3))) + 1) :=
        quadricMeasure_coordinateBox_le hμ (by simp) conjTranspose_one β u
    _ = idealZeta P.integers μ * (P.modulus u)⁻¹ ^ r := by
        congr 2
        simp only [card_fin]
        lia

end New.Floors
