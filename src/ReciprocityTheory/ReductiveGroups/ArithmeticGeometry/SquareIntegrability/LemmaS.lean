import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RSubMean
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaSA

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex Metric

noncomputable section

variable {ι : Type} [Fintype ι]

lemma lemS_finrank : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  first
  | rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]
  | rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι),
      Complex.finrank_real_complex, finrank_euclideanSpace]
  | (rw [(WithLp.linearEquiv 2 ℝ (ι → ℂ)).finrank_eq, Module.finrank_pi_fintype]
     simp [Complex.finrank_real_complex, mul_comm])
  | simp [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]

theorem lemS_local (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ) (hF : Differentiable ℂ F)
    (v0 : EuclideanSpace ℂ ι) :
    ‖F v0‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) ≤
      2 * (q : ℝ) ^ Fintype.card ι *
        ∫ u in closedBall v0 (Real.sqrt (2 * Fintype.card ι) / Real.sqrt (q * Real.pi)),
          ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := by
  set s := Real.sqrt (q * Real.pi) with hs
  set ρ := Real.sqrt (2 * Fintype.card ι) with hρ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q * Real.pi := mul_pos (by linarith) Real.pi_pos
  have hs0 : 0 < s := Real.sqrt_pos.mpr hqpos
  have hs2 : s ^ 2 = q * Real.pi := Real.sq_sqrt hqpos.le
  let eC : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι)
  let eR : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ (Fintype.equivFin ι)
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℂ (Fin (Fintype.card ι)) → EuclideanSpace ℂ ι,
      w = fun z => s⁻¹ • eC.symm z := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℂ (Fin (Fintype.card ι)) → ℂ,
      G = fun z => F (v0 + w z) * Complex.exp (-((q * Real.pi : ℝ) : ℂ) * inner ℂ v0 (w z)) :=
    ⟨_, rfl⟩
  obtain ⟨Hf, hHf⟩ : ∃ Hf : EuclideanSpace ℂ ι → ℝ,
      Hf = fun u => ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := ⟨_, rfl⟩
  have hwd : Differentiable ℂ w := by
    rw [hw]
    exact (eC.symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiable).const_smul s⁻¹
  have hGd : Differentiable ℂ G := by
    rw [hG]
    refine (hF.comp ((differentiable_const v0).add hwd)).mul ?_
    refine Differentiable.cexp ?_
    refine (differentiable_const _).mul ?_
    exact (innerSL ℂ v0).differentiable.comp hwd
  have hwn : ∀ z, ‖w z‖ = s⁻¹ * ‖z‖ := by
    intro z
    rw [hw]
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0, LinearIsometryEquiv.norm_map]
  have hw0 : w 0 = 0 := by rw [hw]; simp
  have hexp2 : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
    rw [sq, ← Real.exp_add, two_mul]
  have key : ∀ z, ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Hf (v0 + w z) := by
    intro z
    have hz : ‖z‖ ^ 2 = q * Real.pi * ‖w z‖ ^ 2 := by
      rw [hwn, mul_pow, ← hs2, inv_pow]
      field_simp
    have hadd : ‖v0 + w z‖ ^ 2 = ‖v0‖ ^ 2 + 2 * (inner ℂ v0 (w z)).re + ‖w z‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ)]
      first | rfl | simp
    have hre : (-((q * Real.pi : ℝ) : ℂ) * inner ℂ v0 (w z)).re =
        -(q * Real.pi) * (inner ℂ v0 (w z)).re := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have e1 : Real.exp (2 * (-(q * Real.pi) * (inner ℂ v0 (w z)).re)) * Real.exp (-‖z‖ ^ 2) =
        Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0 + w z‖ ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, hz, hadd]
      congr 1
      ring
    calc ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
        = ‖F (v0 + w z)‖ ^ 2 *
            (Real.exp (2 * (-(q * Real.pi) * (inner ℂ v0 (w z)).re)) * Real.exp (-‖z‖ ^ 2)) := by
          rw [hG]
          simp only [norm_mul, Complex.norm_exp, mul_pow, hre, hexp2]
          ring
      _ = _ := by rw [e1, hHf]; ring
  have hmem : ∀ z, v0 + w z ∈ Metric.closedBall v0 (ρ / s) ↔
      z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ := by
    intro z
    have hsub : v0 + w z - v0 = w z := by abel
    rw [Metric.mem_closedBall, Metric.mem_closedBall, dist_eq_norm, dist_eq_norm, hsub, sub_zero, hwn,
      div_eq_inv_mul]
    exact ⟨fun h => le_of_mul_le_mul_left h (inv_pos.mpr hs0),
      fun h => mul_le_mul_of_nonneg_left h (inv_pos.mpr hs0).le⟩
  have hA : ∫ z in Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ,
      ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.exp (q * Real.pi * ‖v0‖ ^ 2) * ∫ z, (Metric.closedBall v0 (ρ / s)).indicator Hf (v0 + w z) := by
    rw [← integral_indicator measurableSet_closedBall, ← integral_const_mul]
    congr 1
    funext z
    by_cases hzb : z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ
    · rw [Set.indicator_of_mem hzb, Set.indicator_of_mem ((hmem z).2 hzb), key z]
    · have h2 : v0 + w z ∉ Metric.closedBall v0 (ρ / s) := fun h => hzb ((hmem z).1 h)
      simp [Set.indicator_apply, hzb, h2]
  have hC : ∫ z, (Metric.closedBall v0 (ρ / s)).indicator Hf (v0 + w z) =
      s ^ (2 * Fintype.card ι) * ∫ u, (Metric.closedBall v0 (ρ / s)).indicator Hf u := by
    set h := (Metric.closedBall v0 (ρ / s)).indicator Hf
    have h1 : ∫ z, h (v0 + w z) = ∫ y, h (v0 + s⁻¹ • y) := by
      rw [hw]
      exact (eR.symm.measurePreserving).integral_comp eR.symm.toHomeomorph.measurableEmbedding
        (fun y => h (v0 + s⁻¹ • y))
    rw [h1, MeasureTheory.Measure.integral_comp_smul (μ := volume) (fun y => h (v0 + y)) s⁻¹,
      lemS_finrank, integral_add_left_eq_self, inv_pow, inv_inv, abs_of_pos (pow_pos hs0 _),
      smul_eq_mul]
  have L : ‖G 0‖ ^ 2 ≤ 2 / Real.pi ^ Fintype.card ι *
      ∫ z in Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ,
        ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := sq_norm_zero_le_gauss_ball G hGd
  have hG0 : G 0 = F v0 := by rw [hG]; simp [hw0]
  have hsn : s ^ (2 * Fintype.card ι) = (q * Real.pi) ^ Fintype.card ι := by rw [pow_mul, hs2]
  have hJ : ∫ u, (Metric.closedBall v0 (ρ / s)).indicator Hf u =
      ∫ u in Metric.closedBall v0 (ρ / s), ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := by
    rw [integral_indicator measurableSet_closedBall, hHf]
  rw [hA, hC, hG0, hsn, hJ] at L
  have hE : Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hpi : Real.pi ^ Fintype.card ι ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
  set J := ∫ u in Metric.closedBall v0 (ρ / s), ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2)
  calc ‖F v0‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2)
      ≤ 2 / Real.pi ^ Fintype.card ι *
          (Real.exp (q * Real.pi * ‖v0‖ ^ 2) * ((q * Real.pi) ^ Fintype.card ι * J)) *
          Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) := mul_le_mul_of_nonneg_right L (Real.exp_pos _).le
    _ = 2 * (q : ℝ) ^ Fintype.card ι * J * (Real.pi ^ Fintype.card ι / Real.pi ^ Fintype.card ι) *
          (Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2)) := by
        rw [mul_pow]; ring
    _ = 2 * (q : ℝ) ^ Fintype.card ι * J := by rw [hE, div_self hpi]; ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex Metric

noncomputable section

variable {ι : Type} [Fintype ι]

lemma lemS_pack (hP : Ext.PackingCount) (S : Finset (EuclideanSpace ℂ ι)) (δ ρ : ℝ)
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hS : ∀ a ∈ S, ‖a‖ ≤ ρ)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ ‖a - b‖) :
    (S.card : ℝ) ≤ (1 + 4 * ρ / δ) ^ (2 * Fintype.card ι) := by
  have hr : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    first
      | rw [Module.finrank_real_of_complex, finrank_euclideanSpace]
      | rw [finrank_real_of_complex, finrank_euclideanSpace]
  let e := ((stdOrthonormalBasis ℝ (EuclideanSpace ℂ ι)).reindex (finCongr hr)).repr
  let P := S.map ⟨e, e.injective⟩
  have hcard : P.card = S.card := Finset.card_map _
  rcases lt_or_ge ρ (δ / 2) with hsmall | hbig
  · have h1 : S.card ≤ 1 := by
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      by_contra hab
      have h3 := hsep a ha b hb hab
      have h2 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
      linarith [hS a ha, hS b hb]
    calc (S.card : ℝ) ≤ 1 := by exact_mod_cast h1
      _ ≤ (1 + 4 * ρ / δ) ^ (2 * Fintype.card ι) := by
        refine one_le_pow₀ ?_
        have : 0 ≤ 4 * ρ / δ := by positivity
        linarith
  · have hR : δ ≤ max δ ρ := le_max_left _ _
    have hnorm : ∀ x ∈ P, ‖x‖ ≤ max δ ρ := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      simp only [Function.Embedding.coeFn_mk, LinearIsometryEquiv.norm_map]
      exact (hS a ha).trans (le_max_right _ _)
    have hsep' : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y := by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hy
      have hab : a ≠ b := fun h => hxy (by rw [h])
      simp only [Function.Embedding.coeFn_mk, LinearIsometryEquiv.dist_map, dist_eq_norm]
      first
        | exact hsep a ha b hb hab
        | (rw [← map_sub, LinearIsometryEquiv.norm_map]; exact hsep a ha b hb hab)
    have hPc := hP (2 * Fintype.card ι) P δ (max δ ρ) hδ hR hnorm hsep'
    rw [hcard] at hPc
    have hle : 3 * max δ ρ / δ ≤ 1 + 4 * ρ / δ := by
      rw [div_le_iff₀ hδ, add_mul, one_mul, div_mul_cancel₀ _ hδ.ne']
      rcases le_total δ ρ with h | h
      · rw [max_eq_right h]
        linarith
      · rw [max_eq_left h]
        linarith
    refine hPc.trans ?_
    first
      | exact pow_le_pow_left₀ (by positivity) hle _
      | exact pow_le_pow_left (by positivity) hle _

lemma firstMinimum_le_norm (Y : GT ι) {x : EuclideanSpace ℂ ι} (hx : x ∈ lat Y.b) (hne : x ≠ 0) :
    Y.la1 ≤ ‖x‖ := by
  unfold GT.la1
  refine csInf_le ⟨0, ?_⟩ ⟨x, hx, hne, rfl⟩
  rintro t ⟨y, _, _, rfl⟩
  exact norm_nonneg y

lemma firstMinimum_pos (Y : GT ι) (hN : 0 < Fintype.card ι) : 0 < Y.la1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set (lat Y.b))) 0 rfl
  have hne : ({t : ℝ | ∃ x ∈ lat Y.b, x ≠ 0 ∧ t = ‖x‖}).Nonempty := by
    obtain ⟨i⟩ : Nonempty (Fin (2 * Fintype.card ι)) := ⟨⟨0, by omega⟩⟩
    exact ⟨_, Y.b i, Submodule.subset_span ⟨i, rfl⟩, Y.b.ne_zero i, rfl⟩
  unfold GT.la1
  refine lt_of_lt_of_le hε (le_csInf hne ?_)
  rintro t ⟨x, hx, hx0, rfl⟩
  by_contra hlt
  push_neg at hlt
  have hmem : (⟨x, hx⟩ : lat Y.b) ∈ Metric.ball (0 : lat Y.b) ε := by
    simpa [Metric.mem_ball, dist_zero_right] using hlt
  have h0 := hball hmem
  simp only [Set.mem_singleton_iff] at h0
  exact hx0 (congrArg Subtype.val h0)

lemma lemS_Hf_eq_inner (w v : EuclideanSpace ℂ ι) : Hf w v = inner ℂ v w := by
  simp only [Hf, PiLp.inner_apply, RCLike.inner_apply]
  all_goals (refine Finset.sum_congr rfl fun i _ => ?_; ring)

lemma lemS_periodic (Y : GT ι) (q : ℕ) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec q)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (v : EuclideanSpace ℂ ι) :
    Y.ptN2 q F (γ + v) = Y.ptN2 q F v := by
  obtain ⟨_, hF'⟩ := hF
  have h := hF' γ hγ v
  have hnorm : ‖v + γ‖ ^ 2 = ‖v‖ ^ 2 + 2 * (Hf v γ).re + ‖γ‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), lemS_Hf_eq_inner, inner_re_symm]
    rfl
  have hγγ : Hf γ γ = ((‖γ‖ ^ 2 : ℝ) : ℂ) := by
    rw [lemS_Hf_eq_inner]
    first
      | exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) γ
      | (rw [inner_self_eq_norm_sq_to_K]; simp)
      | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
  have hA : ∀ z : ℂ, ((q : ℂ) * (Real.pi : ℂ) * z + (q : ℂ) * (Real.pi : ℂ) * ((‖γ‖ ^ 2 : ℝ) : ℂ) / 2).re =
      q * Real.pi * z.re + q * Real.pi * ‖γ‖ ^ 2 / 2 := by
    intro z
    simp
    first
      | (left; rw [← Complex.ofReal_pow, Complex.ofReal_re])
      | ring
  have key : Real.exp (q * Real.pi * (Hf v γ).re + q * Real.pi * ‖γ‖ ^ 2 / 2) ^ 2 *
      Real.exp (-(q * Real.pi) * (‖v‖ ^ 2 + 2 * (Hf v γ).re + ‖γ‖ ^ 2)) =
        Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  simp only [GT.ptN2]
  rw [add_comm γ v, h, norm_mul, norm_mul, Y.ka_abs γ hγ, Complex.norm_exp, hnorm, hγγ, hA]
  linear_combination ‖F v‖ ^ 2 * key

lemma lemS_cover (Y : GT ι) (q : ℕ) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec q)
    (v0 : EuclideanSpace ℂ ι) (ρ K : ℝ)
    (hK : ∀ S : Finset (EuclideanSpace ℂ ι), (∀ a ∈ S, ‖a‖ ≤ ρ) →
      (∀ a ∈ S, ∀ b ∈ S, a - b ∈ lat Y.b) → (S.card : ℝ) ≤ K) :
    ∫ u in closedBall v0 ρ, Y.ptN2 q F u ≤
      K * ∫ u in ZSpan.fundamentalDomain Y.b, Y.ptN2 q F u := by
  classical
  have hc : Continuous F := hF.1.continuous
  have hfc : Continuous fun u => Y.ptN2 q F u := by
    unfold GT.ptN2
    exact (hc.norm.pow 2).mul (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hf0 : ∀ u, 0 ≤ Y.ptN2 q F u := fun u => by
    unfold GT.ptN2
    positivity
  have hmeas : Measurable fun u => ENNReal.ofReal (Y.ptN2 q F u) :=
    ENNReal.measurable_ofReal.comp hfc.measurable
  have hfd : MeasureTheory.IsAddFundamentalDomain (lat Y.b) (ZSpan.fundamentalDomain Y.b)
      MeasureTheory.volume := ZSpan.isAddFundamentalDomain Y.b MeasureTheory.volume
  have hK0 : 0 ≤ K := by
    have h := hK ∅ (by simp) (by simp)
    simpa using h
  have hcount : ∀ x : EuclideanSpace ℂ ι, ∑' γ : lat Y.b,
      (closedBall v0 ρ).indicator (fun _ => (1 : ENNReal)) (γ +ᵥ x) ≤ ENNReal.ofReal K := by
    intro x
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun T => ?_
    have h1 : ∑ γ ∈ T, (closedBall v0 ρ).indicator (fun _ => (1 : ENNReal)) (γ +ᵥ x) =
        ((T.filter (fun γ : lat Y.b => γ +ᵥ x ∈ closedBall v0 ρ)).card : ENNReal) := by
      rw [Finset.natCast_card_filter]
      refine Finset.sum_congr rfl fun γ _ => ?_
      by_cases h : γ +ᵥ x ∈ closedBall v0 ρ
      · rw [Set.indicator_of_mem h, if_pos h]
      · rw [Set.indicator_of_notMem h, if_neg h]
    rw [h1]
    have hinj : Function.Injective (fun γ : lat Y.b => (γ +ᵥ x) - v0) := by
      intro a b h
      exact Subtype.ext (by simpa [Submodule.vadd_def, vadd_eq_add] using h)
    have hS := hK ((T.filter (fun γ : lat Y.b => γ +ᵥ x ∈ closedBall v0 ρ)).image
        (fun γ : lat Y.b => (γ +ᵥ x) - v0)) ?_ ?_
    · rw [Finset.card_image_of_injective _ hinj] at hS
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hS
    · intro a ha
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
      have hγ' := (Finset.mem_filter.1 hγ).2
      rw [Metric.mem_closedBall, dist_eq_norm] at hγ'
      exact hγ'
    · intro a ha b hb
      obtain ⟨γ, _, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨γ', _, rfl⟩ := Finset.mem_image.1 hb
      have e : ((γ +ᵥ x) - v0) - ((γ' +ᵥ x) - v0) = (γ : EuclideanSpace ℂ ι) - γ' := by
        simp only [Submodule.vadd_def, vadd_eq_add]
        abel
      rw [e]
      exact sub_mem γ.2 γ'.2
  have hper : ∀ (γ : lat Y.b) (u : EuclideanSpace ℂ ι),
      (closedBall v0 ρ).indicator (fun u => ENNReal.ofReal (Y.ptN2 q F u)) (γ +ᵥ u) =
        (closedBall v0 ρ).indicator (fun _ => (1 : ENNReal)) (γ +ᵥ u) * ENNReal.ofReal (Y.ptN2 q F u) := by
    intro γ u
    have hp : Y.ptN2 q F (γ +ᵥ u) = Y.ptN2 q F u := by
      rw [Submodule.vadd_def, vadd_eq_add]
      exact lemS_periodic Y q hF γ.2 u
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hp, one_mul]
    · rw [zero_mul]
  have hae : ∀ γ : lat Y.b, AEMeasurable (fun u => (closedBall v0 ρ).indicator
      (fun _ => (1 : ENNReal)) (γ +ᵥ u) * ENNReal.ofReal (Y.ptN2 q F u))
      (MeasureTheory.volume.restrict (ZSpan.fundamentalDomain Y.b)) := fun γ =>
    (((measurable_const.indicator measurableSet_closedBall).comp (measurable_const_vadd γ)).mul
      hmeas).aemeasurable
  haveI : MeasureTheory.VAddInvariantMeasure (lat Y.b) (EuclideanSpace ℂ ι) MeasureTheory.volume :=
    ⟨fun c s _ => MeasureTheory.measure_preimage_add _ (c : EuclideanSpace ℂ ι) s⟩
  have hlin : ∫⁻ u in closedBall v0 ρ, ENNReal.ofReal (Y.ptN2 q F u) ≤
      ENNReal.ofReal K * ∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal (Y.ptN2 q F u) := by
    calc ∫⁻ u in closedBall v0 ρ, ENNReal.ofReal (Y.ptN2 q F u)
        = ∫⁻ u, (closedBall v0 ρ).indicator (fun u => ENNReal.ofReal (Y.ptN2 q F u)) u :=
          (MeasureTheory.lintegral_indicator measurableSet_closedBall _).symm
      _ = ∑' γ : lat Y.b, ∫⁻ u in ZSpan.fundamentalDomain Y.b,
            (closedBall v0 ρ).indicator (fun u => ENNReal.ofReal (Y.ptN2 q F u)) (γ +ᵥ u) :=
          hfd.lintegral_eq_tsum'' _
      _ = ∑' γ : lat Y.b, ∫⁻ u in ZSpan.fundamentalDomain Y.b,
            (closedBall v0 ρ).indicator (fun _ => (1 : ENNReal)) (γ +ᵥ u) *
              ENNReal.ofReal (Y.ptN2 q F u) :=
          tsum_congr fun γ => MeasureTheory.lintegral_congr fun u => hper γ u
      _ = ∫⁻ u in ZSpan.fundamentalDomain Y.b, ∑' γ : lat Y.b,
            (closedBall v0 ρ).indicator (fun _ => (1 : ENNReal)) (γ +ᵥ u) *
              ENNReal.ofReal (Y.ptN2 q F u) :=
          (MeasureTheory.lintegral_tsum hae).symm
      _ ≤ ∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal K * ENNReal.ofReal (Y.ptN2 q F u) := by
          refine MeasureTheory.lintegral_mono fun u => ?_
          rw [ENNReal.tsum_mul_right]
          exact mul_le_mul_of_nonneg_right (hcount u) zero_le
      _ = ENNReal.ofReal K * ∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal (Y.ptN2 q F u) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hint_D : MeasureTheory.IntegrableOn (fun u => Y.ptN2 q F u) (ZSpan.fundamentalDomain Y.b) :=
    (hfc.continuousOn.integrableOn_compact
      (ZSpan.fundamentalDomain_isBounded Y.b).isCompact_closure).mono_set subset_closure
  have hfin : ∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal (Y.ptN2 q F u) ≠ ⊤ :=
    (MeasureTheory.Integrable.lintegral_lt_top hint_D).ne
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => hf0 u)
      hfc.aestronglyMeasurable,
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => hf0 u)
      hfc.aestronglyMeasurable]
  calc (∫⁻ u in closedBall v0 ρ, ENNReal.ofReal (Y.ptN2 q F u)).toReal
      ≤ (ENNReal.ofReal K * ∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal (Y.ptN2 q F u)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hlin
    _ = K * (∫⁻ u in ZSpan.fundamentalDomain Y.b, ENNReal.ofReal (Y.ptN2 q F u)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0]

theorem lemS_main (hP : Ext.PackingCount) : GSupStatement := by
  intro ι _ Y q hq F hF v
  set N := Fintype.card ι with hNdef
  set ρ := Real.sqrt (2 * N) / Real.sqrt (q * Real.pi) with hρ
  set K := (1 + 4 * Real.sqrt (2 * N) / (Real.sqrt (q * Real.pi) * Y.la1)) ^ (2 * N) with hKdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hK : ∀ S : Finset (EuclideanSpace ℂ ι), (∀ a ∈ S, ‖a‖ ≤ ρ) →
      (∀ a ∈ S, ∀ b ∈ S, a - b ∈ lat Y.b) → (S.card : ℝ) ≤ K := by
    intro S hS hSl
    rcases Nat.eq_zero_or_pos N with hN | hN
    · have hE : IsEmpty ι := Fintype.card_eq_zero_iff.mp hN
      have hsub : ∀ a b : EuclideanSpace ℂ ι, a = b := fun a b =>
        PiLp.ext (fun i => isEmptyElim i)
      have : S.card ≤ 1 := Finset.card_le_one.mpr (fun a _ b _ => hsub a b)
      rw [hKdef, hN, mul_zero, pow_zero]
      exact_mod_cast this
    · have hla := firstMinimum_pos Y hN
      have := lemS_pack hP S Y.la1 ρ hla hρ0 hS (fun a ha b hb hab =>
        firstMinimum_le_norm Y (hSl a ha b hb) (sub_ne_zero.mpr hab))
      have e : 4 * Real.sqrt (2 * N) / (Real.sqrt (q * Real.pi) * Y.la1) = 4 * ρ / Y.la1 := by
        rw [hρ, mul_div_assoc', div_div]
      rw [hKdef, e]
      exact this
  have hK0 : 0 ≤ K := by simpa using hK ∅ (by simp) (by simp)
  have h1 := lemS_local q hq F hF.1 v
  have h2 := lemS_cover Y q hF v ρ K hK
  set D := ZSpan.fundamentalDomain Y.b with hDdef
  have hvol := lemS_vol_le Y
  have hvol0 : volume D ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero Y.b
  have hvr : 0 < volume.real D := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hvol0 (ne_top_of_le_ne_top ENNReal.one_ne_top hvol)
  have hvr1 : volume.real D ≤ 1 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hvol)
  have hl2 : Y.l2 q F = (volume.real D)⁻¹ * ∫ u in D, Y.ptN2 q F u := by
    rw [GT.l2, setAverage_eq, smul_eq_mul]
  have hD0 : 0 ≤ ∫ u in D, Y.ptN2 q F u :=
    setIntegral_nonneg (ZSpan.fundamentalDomain_measurableSet Y.b)
      (fun u _ => by simp only [GT.ptN2]; positivity)
  have hID : ∫ u in D, Y.ptN2 q F u ≤ Y.l2 q F := by
    rw [hl2]
    exact le_mul_of_one_le_left hD0 ((one_le_inv₀ hvr).mpr hvr1)
  have hq0 : 0 ≤ 2 * (q : ℝ) ^ N := by positivity
  calc Y.ptN2 q F v ≤ 2 * (q : ℝ) ^ N * ∫ u in closedBall v ρ, Y.ptN2 q F u := h1
    _ ≤ 2 * (q : ℝ) ^ N * (K * ∫ u in D, Y.ptN2 q F u) := mul_le_mul_of_nonneg_left h2 hq0
    _ ≤ 2 * (q : ℝ) ^ N * (K * Y.l2 q F) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hID hK0) hq0
    _ = 2 * (q : ℝ) ^ N * K * Y.l2 q F := by ring

theorem gSup (hP : Ext.PackingCount) : GSupStatement := lemS_main hP

end

end ReciprocityTheory.ChartRestriction.G.I2
end
