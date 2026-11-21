import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseChart
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DegreeTopEqArithDegree

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

section Local

variable {K : Type*} [Field K] [NumberField K]

theorem finitePlace_isNonarchimedean (v : FinitePlace K) : IsNonarchimedean (⇑v) :=
  fun a b ↦ v.add_le a b

theorem sum_block_exponents {m : Coord n →₀ ℕ} {δ : ι → ℕ}
    (h : Finsupp.weight (coordDeg n) m = δ) (k : ι) :
    ∑ i : Fin (n k + 1), m ⟨k, i⟩ = δ k := by
  classical
  have h1 := congrFun h k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply] at h1
  rw [← h1, Fintype.sum_sigma]
  simp only [coordDeg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem finitePlace_monomial_le (v : FinitePlace K) (y : Cone n K) {m : Coord n →₀ ℕ} {δ : ι → ℕ}
    (hm : Finsupp.weight (coordDeg n) m = δ) :
    v (∏ p ∈ m.support, y p.1 p.2 ^ m p) ≤ ∏ k, (⨆ i, v (y k i)) ^ δ k := by
  classical
  rw [map_prod]
  simp_rw [map_pow]
  calc ∏ p ∈ m.support, v (y p.1 p.2) ^ m p
      ≤ ∏ p ∈ m.support, (⨆ i, v (y p.1 i)) ^ m p := by
        refine Finset.prod_le_prod (fun p _ ↦ pow_nonneg (apply_nonneg v _) _) fun p _ ↦ ?_
        exact pow_le_pow_left₀ (apply_nonneg v _)
          (le_ciSup (f := fun i ↦ v (y p.1 i)) (Set.finite_range _).bddAbove p.2) _
    _ = ∏ p : Coord n, (⨆ i, v (y p.1 i)) ^ m p := by
        refine Finset.prod_subset (Finset.subset_univ _) fun p _ hp ↦ ?_
        rw [Finsupp.notMem_support_iff.mp hp, pow_zero]
    _ = ∏ k, (⨆ i, v (y k i)) ^ δ k := by
        rw [Fintype.prod_sigma]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        show ∏ i, (⨆ j, v (y k j)) ^ m ⟨k, i⟩ = _
        rw [Finset.prod_pow_eq_pow_sum, sum_block_exponents hm k]

theorem finitePlace_evalCone_le (v : FinitePlace K) (y : Cone n K) {f : MvPolynomial (Coord n) ℤ}
    {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    v (evalCone y f) ≤ ∏ k, (⨆ i, v (y k i)) ^ δ k := by
  classical
  have hR : 0 ≤ ∏ k, (⨆ i, v (y k i)) ^ δ k :=
    Finset.prod_nonneg fun k _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg v _) _
  rcases eq_or_ne f 0 with rfl | hf0
  · simpa [evalCone] using hR
  rw [evalCone, eval₂_eq]
  obtain ⟨m, hm, hle⟩ := (finitePlace_isNonarchimedean v).finset_image_add_of_nonempty
    (fun d ↦ (Int.castRingHom K) (coeff d f) * ∏ p ∈ d.support, y p.1 p.2 ^ d p)
    (support_nonempty.mpr hf0)
  refine hle.trans ?_
  rw [map_mul]
  have h1 : v ((Int.castRingHom K) (coeff m f)) ≤ 1 := by
    rw [eq_intCast]
    exact (finitePlace_isNonarchimedean v).apply_intCast_le_one
  calc v ((Int.castRingHom K) (coeff m f)) * v (∏ p ∈ m.support, y p.1 p.2 ^ m p)
      ≤ 1 * ∏ k, (⨆ i, v (y k i)) ^ δ k :=
        mul_le_mul h1 (finitePlace_monomial_le v y (hf (mem_support_iff.mp hm)))
          (apply_nonneg v _) zero_le_one
    _ = _ := one_mul _

theorem sum_log_finitePlace_add_sum_log_embedding {t : K} (ht : t ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v t)) + ∑ σ : K →+* ℂ, Real.log ‖σ t‖ = 0 := by
  have hfin : (Function.mulSupport fun w : FinitePlace K ↦ w t).Finite :=
    FinitePlace.hasFiniteMulSupport ht
  have hprod := FinitePlace.prod_eq_inv_abs_norm ht
  rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _
    (fun w hw ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hw))] at hprod
  have h1 : (∑ᶠ v : FinitePlace K, Real.log (v t)) = Real.log (|(Algebra.norm ℚ t : ℝ)|⁻¹) := by
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · rw [← Real.log_prod, hprod]
      · simp
      · intro w _
        exact (FinitePlace.pos_iff.mpr ht).ne'
    · intro w hw
      have h1' : w t ≠ 1 := fun h ↦ hw (by show Real.log (w t) = 0; rw [h, Real.log_one])
      exact Finset.mem_coe.mpr (hfin.mem_toFinset.mpr h1')
  have h2 : ∑ σ : K →+* ℂ, Real.log ‖σ t‖ = Real.log |(Algebra.norm ℚ t : ℝ)| := by
    rw [← Real.log_prod (fun σ _ ↦ norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ht))]
    congr 1
    have h3 := Algebra.norm_eq_prod_embeddings ℚ ℂ t
    have h4 : ∏ σ : K →+* ℂ, σ t = ∏ σ : K →ₐ[ℚ] ℂ, σ t :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun σ ↦ rfl
    rw [← norm_prod, h4, ← h3, eq_ratCast, Complex.norm_ratCast]
  rw [h1, h2, Real.log_inv, neg_add_cancel]

end Local

theorem chartForm_agree {P : ArithVariety n} {a : ι → ℤ} {num den : MvPolynomial (Coord n) ℤ}
    (hden : den ∉ P.ideal) {c c' : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ}
    {e e' : MvPolynomial (Coord n) ℤ} (he : IsChartForm P a num den c d e)
    (he' : IsChartForm P a num den c' d' e') {F : Type*} [CommRing F] {z : Cone n F}
    (hz : z ∈ P.points F) :
    evalCone z e * evalCone z (chartMonomial c' d') = evalCone z e' * evalCone z (chartMonomial c d) := by
  have hmem : den * (e * chartMonomial c' d' - e' * chartMonomial c d) ∈ P.ideal := by
    have : den * (e * chartMonomial c' d' - e' * chartMonomial c d) =
        (den * e - num * chartMonomial c d) * chartMonomial c' d' -
          (den * e' - num * chartMonomial c' d') * chartMonomial c d := by ring
    rw [this]
    exact P.ideal.sub_mem (P.ideal.mul_mem_right _ he.2) (P.ideal.mul_mem_right _ he'.2)
  have h2 := (P.isPrime.mem_or_mem hmem).resolve_left hden
  have h3 := hz.2 _ h2
  simp only [evalCone, eval₂_sub, eval₂_mul] at h3 ⊢
  exact sub_eq_zero.mp h3

omit [Fintype ι] in

theorem coordVec_mem_points {P : ArithVariety n} {x : Cone n (AlgebraicClosure ℚ)}
    (hx : x ∈ P.points (AlgebraicClosure ℚ)) : coordVec x ∈ P.points (coordField x) := by
  have hval : ∀ f, (coordField x).val.toRingHom (evalCone (coordVec x) f) = evalCone x f :=
    fun f ↦ (evalCone_map (coordField x).val.toRingHom (coordVec x) f).symm
  refine ⟨fun k h ↦ hx.1 k ?_, fun f hf ↦ ?_⟩
  · funext i
    have : coordVec x k i = 0 := congrFun h i
    exact congrArg Subtype.val this
  · apply (coordField x).val.toRingHom.injective
    rw [hval, map_zero]
    exact hx.2 f hf

theorem neg_le_height_of_chartForm {P : ArithVariety n} {A : HermLine n}
    (s : IntegralSection P A.deg) {C : ℝ} (hs : s.SupNormLE A C) {x : Cone n (AlgebraicClosure ℚ)}
    (hx : x ∈ P.points (AlgebraicClosure ℚ)) {c : (k : ι) → Fin (n k + 1)} {d : ι → ℕ}
    {e : MvPolynomial (Coord n) ℤ} (he : IsChartForm P A.deg s.num s.den c d e)
    (hc : ∀ k, x k (c k) ≠ 0) (hex : evalCone x e ≠ 0) : -C ≤ height A x := by
  set K := coordField x
  set y := coordVec x with hydef
  have hy : y ∈ P.points K := coordVec_mem_points hx
  have hval : ∀ f, K.val.toRingHom (evalCone y f) = evalCone x f :=
    fun f ↦ (evalCone_map K.val.toRingHom y f).symm
  have hyc : ∀ k, y k (c k) ≠ 0 := fun k h ↦ hc k (congrArg Subtype.val h)
  have hey : evalCone y e ≠ 0 := fun h ↦ hex (by rw [← hval, h, map_zero])
  have hmy : evalCone y (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc k)
  set t : K := evalCone y e / evalCone y (chartMonomial c d) with htdef
  have ht : t ≠ 0 := div_ne_zero hey hmy

  have hfin : ∀ v : FinitePlace K, Real.log (v t) ≤
      ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i)) := by
    intro v
    have hM : ∀ k, ∃ i, v (y k i) = ⨆ i, v (y k i) := fun k ↦ exists_eq_ciSup_of_finite
    choose c' hc' using hM
    have hMpos : ∀ k, 0 < ⨆ i, v (y k i) := by
      intro k
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (hy.1 k)
      exact lt_of_lt_of_le (FinitePlace.pos_iff.mpr hi)
        (le_ciSup (f := fun i ↦ v (y k i)) (Set.finite_range _).bddAbove i)
    have hyc' : ∀ k, y k (c' k) ≠ 0 := by
      intro k h
      have := hc' k
      rw [h, map_zero] at this
      exact (hMpos k).ne this
    have hX : ∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := by
      intro k hk
      apply hyc' k
      have := hy.2 _ hk
      simpa [evalCone] using this
    obtain ⟨d', e', he'⟩ := s.regular c' hX
    have hagree := chartForm_agree s.den_not_mem he he' hy
    have hm'y : evalCone y (chartMonomial c' d') ≠ 0 := by
      rw [evalCone_chartMonomial]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc' k)
    have ht' : t = evalCone y e' / evalCone y (chartMonomial c' d') := by
      rw [htdef, div_eq_div_iff hmy hm'y, hagree]
    have he'y : evalCone y e' ≠ 0 := by
      intro h
      rw [ht', h, zero_div] at ht
      exact ht rfl
    obtain ⟨⟨δ, hδ, hδa⟩, _⟩ := he'
    have hvm : v (evalCone y (chartMonomial c' d')) = ∏ k, (⨆ i, v (y k i)) ^ d' k := by
      rw [evalCone_chartMonomial, map_prod]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [map_pow, hc' k]
    have hve := finitePlace_evalCone_le v y hδ
    have hpos_e : 0 < v (evalCone y e') := FinitePlace.pos_iff.mpr he'y
    rw [ht', map_div₀, Real.log_div hpos_e.ne'
      ((FinitePlace.pos_iff.mpr hm'y).ne'), hvm,
      Real.log_prod (fun k _ ↦ (pow_pos (hMpos k) _).ne')]
    have hle : Real.log (v (evalCone y e')) ≤ ∑ k, (δ k : ℝ) * Real.log (⨆ i, v (y k i)) := by
      refine (Real.log_le_log hpos_e hve).trans ?_
      rw [Real.log_prod (fun k _ ↦ (pow_pos (hMpos k) _).ne')]
      simp only [Real.log_pow, le_refl]
    simp only [Real.log_pow]
    rw [← sub_nonneg]
    have hsum : ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i)) -
        (Real.log (v (evalCone y e')) - ∑ k, (d' k : ℝ) * Real.log (⨆ i, v (y k i))) =
        ∑ k, (δ k : ℝ) * Real.log (⨆ i, v (y k i)) - Real.log (v (evalCone y e')) := by
      have hd : ∀ k, (δ k : ℝ) = (A.deg k : ℝ) + (d' k : ℝ) := fun k ↦ by exact_mod_cast hδa k
      simp only [hd, add_mul, Finset.sum_add_distrib]
      ring
    rw [hsum]
    exact sub_nonneg.mpr hle

  have harch : ∀ σ : K →+* ℂ, Real.log ‖σ t‖ ≤ C + Real.log (A.metric fun k i ↦ σ (y k i)) := by
    intro σ
    set z : Cone n ℂ := fun k i ↦ σ (y k i)
    have hz : z ∈ P.points ℂ := sigma_mem_points P hx σ
    have hzc : ∀ k, z k (c k) ≠ 0 := fun k ↦ (map_ne_zero σ).mpr (hyc k)
    have hb := hs z hz c d e he hzc
    have hez : evalCone z e = σ (evalCone y e) := evalCone_map σ y e
    have hmz : evalCone z (chartMonomial c d) = σ (evalCone y (chartMonomial c d)) :=
      evalCone_map σ y _
    have hmet : 0 < A.metric z := A.metric_pos z hz.1
    have hmn : 0 < ‖σ (evalCone y (chartMonomial c d))‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hmy)
    have htn : 0 < ‖σ t‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr ht)
    have hst : ‖σ t‖ = ‖σ (evalCone y e)‖ / ‖σ (evalCone y (chartMonomial c d))‖ := by
      rw [htdef, map_div₀, norm_div]
    have h1 : ‖σ t‖ ≤ Real.exp C * A.metric z := by
      rw [hez, hmz] at hb
      rw [hst, div_le_iff₀ hmn]
      rw [div_le_iff₀ (mul_pos hmn hmet)] at hb
      linarith
    calc Real.log ‖σ t‖ ≤ Real.log (Real.exp C * A.metric z) := Real.log_le_log htn h1
      _ = C + Real.log (A.metric z) := by rw [Real.log_mul (Real.exp_pos C).ne' hmet.ne', Real.log_exp]

  have hPF := sum_log_finitePlace_add_sum_log_embedding ht
  have hdeg : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hsupp1 : (Function.support fun v : FinitePlace K ↦ Real.log (v t)).Finite := by
    refine (FinitePlace.hasFiniteMulSupport ht).subset fun v hv h1 ↦ hv ?_
    have h1' : v t = 1 := h1
    show Real.log (v t) = 0
    rw [h1', Real.log_one]
  have hsupp2 := finite_support_height A x hx.1
  have hF : (∑ᶠ v : FinitePlace K, Real.log (v t)) ≤
      ∑ᶠ v : FinitePlace K, ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i)) :=
    finsum_le_finsum' hsupp1 hsupp2 hfin
  have hA : ∑ σ : K →+* ℂ, Real.log ‖σ t‖ ≤
      ∑ σ : K →+* ℂ, (C + Real.log (A.metric fun k i ↦ σ (y k i))) :=
    Finset.sum_le_sum fun σ _ ↦ harch σ
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul] at hA
  have key : -(Module.finrank ℚ K : ℝ) * C ≤
      (∑ᶠ v : FinitePlace K, ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i))) +
        ∑ σ : K →+* ℂ, Real.log (A.metric fun k i ↦ σ (y k i)) := by
    linarith
  unfold height
  rw [le_inv_mul_iff₀ hdeg]
  have h2 : (Module.finrank ℚ K : ℝ) * -C = -(Module.finrank ℚ K : ℝ) * C := by ring
  rw [h2]
  exact key

theorem heightLowerBound : HeightLowerBound.Statement := by
  intro ι _ _ n P A J _ s C hs hnz x hx
  obtain ⟨j, c, d, e, he, hc, hex⟩ := hnz x hx
  exact neg_le_height_of_chartForm (s j) (hs j) hx he hc hex

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem finitePlace_le_one_of_isIntegral {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
    {x : K} (hx : IsIntegral ℤ x) : v x ≤ 1 := by
  let y : 𝓞 K := ⟨x, hx⟩
  have h := FinitePlace.norm_le_one K v.maximalIdeal y
  rw [FinitePlace.norm_embedding_eq] at h
  exact h

theorem finsum_log_finitePlace_natCast {K : Type*} [Field K] [NumberField K] {δ : ℕ} (hδ : 0 < δ) :
    ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = -(Module.finrank ℚ K * Real.log δ) := by
  have hne : ((δ : ℕ) : K) ≠ 0 := by exact_mod_cast hδ.ne'
  have hfin : (Function.mulSupport fun w : FinitePlace K ↦ w (δ : K)).Finite :=
    FinitePlace.hasFiniteMulSupport hne
  have hprod := FinitePlace.prod_eq_inv_abs_norm hne
  rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _
    (fun x hx ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hx))] at hprod
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · rw [← Real.log_prod (fun v _ ↦ (map_ne_zero _).mpr hne), hprod]
    have : Algebra.norm ℚ ((δ : ℕ) : K) = (δ : ℚ) ^ (Module.finrank ℚ K) := by
      have := Algebra.norm_algebraMap (S := K) (δ : ℚ)
      simpa using this
    rw [this]
    push_cast
    rw [abs_pow, Nat.abs_cast, Real.log_inv, Real.log_pow]
  · intro v hv
    have h1' : v (δ : K) ≠ 1 := fun h ↦ hv (by show Real.log (v (δ : K)) = 0; rw [h, Real.log_one])
    exact Finset.mem_coe.mpr (hfin.mem_toFinset.mpr h1')

theorem vectorL2Norm_le_sqrt_card_mul {m : ℕ} (w : Fin m → ℂ) {R : ℝ} (hR : 0 ≤ R) (hw : ∀ i, ‖w i‖ ≤ R) :
    l2Norm w ≤ Real.sqrt m * R := by
  rw [l2Norm, ← Real.sqrt_sq hR, ← Real.sqrt_mul (Nat.cast_nonneg m)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin m, R ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hw i) 2
    _ = m * R ^ 2 := by simp

theorem height_standard_le (z : Cone n (AlgebraicClosure ℚ)) (hz : BlockNonzero z) {δ : ℕ}
    (hδ : 0 < δ) {R : ℝ} (hR : 0 < R)
    (hint : ∀ k i, IsIntegral ℤ ((δ : AlgebraicClosure ℚ) * z k i))
    (harch : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) k i, ‖σ (z k i)‖ ≤ R) :
    height (HermLine.standard n) z ≤ ∑ k, (Real.log δ + Real.log (Real.sqrt (n k + 1) * R)) := by
  set K := coordField z
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd_def
  have hd : 0 < d := by rw [hd_def]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hne : ((δ : ℕ) : K) ≠ 0 := by exact_mod_cast hδ.ne'

  have hloc : ∀ (v : FinitePlace K) (k : ι),
      Real.log (⨆ i, v (coordVec z k i)) ≤ -Real.log (v (δ : K)) := by
    intro v k
    have hδv : 0 < v (δ : K) := FinitePlace.pos_iff.mpr hne
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hz k)
    have hi0' : coordVec z k i0 ≠ 0 := fun h ↦ hi0 (congrArg Subtype.val h)
    have hpos : 0 < ⨆ i, v (coordVec z k i) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.mpr hi0')
        (le_ciSup (f := fun i ↦ v (coordVec z k i)) (Set.finite_range _).bddAbove i0)
    rw [← Real.log_inv]
    refine Real.log_le_log hpos (ciSup_le fun i ↦ ?_)
    have hI : IsIntegral ℤ ((δ : K) * coordVec z k i) := by
      have h1 := hint k i
      have h2 : (K.val : K →+* AlgebraicClosure ℚ) ((δ : K) * coordVec z k i) =
          (δ : AlgebraicClosure ℚ) * z k i := by
        simp [coordVec]
      rw [← h2] at h1
      exact (isIntegral_algHom_iff ((K.val : K →+* AlgebraicClosure ℚ).toIntAlgHom)
        K.val.injective).mp h1
    have h3 := finitePlace_le_one_of_isIntegral v hI
    rw [map_mul] at h3
    calc v (coordVec z k i) = (v (δ : K))⁻¹ * (v (δ : K) * v (coordVec z k i)) := by
          field_simp
      _ ≤ (v (δ : K))⁻¹ * 1 := mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hδv).le
      _ = (v (δ : K))⁻¹ := mul_one _
  have hsupp1 := finite_support_height (HermLine.standard n) z hz
  have hsupp2 : (Function.support fun v : FinitePlace K ↦ Real.log (v (δ : K))).Finite := by
    refine (FinitePlace.hasFiniteMulSupport hne).subset fun v hv h ↦ hv ?_
    have h' : v (δ : K) = 1 := h
    show Real.log (v (δ : K)) = 0
    rw [h', Real.log_one]
  set T := (hsupp1.union hsupp2).toFinset
  have hfin : (∑ᶠ v : FinitePlace K, ∑ k, ((HermLine.standard n).deg k : ℝ) *
      Real.log (⨆ i, v (coordVec z k i))) ≤ Fintype.card ι * (d * Real.log δ) := by
    rw [finsum_eq_sum_of_support_subset (s := T) _
      (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inl hv)))]
    have h2 : ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = ∑ v ∈ T, Real.log (v (δ : K)) :=
      finsum_eq_sum_of_support_subset (s := T) _
        (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inr hv)))
    have h3 := finsum_log_finitePlace_natCast (K := K) hδ
    rw [h2] at h3
    calc ∑ v ∈ T, ∑ k, ((HermLine.standard n).deg k : ℝ) * Real.log (⨆ i, v (coordVec z k i))
        ≤ ∑ v ∈ T, ∑ _k : ι, -Real.log (v (δ : K)) := by
          refine Finset.sum_le_sum fun v _ ↦ Finset.sum_le_sum fun k _ ↦ ?_
          simp only [HermLine.standard, Int.cast_one, one_mul]
          exact hloc v k
      _ = Fintype.card ι * -(∑ v ∈ T, Real.log (v (δ : K))) := by
          simp [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = Fintype.card ι * (d * Real.log δ) := by rw [h3, neg_neg]

  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> rfl
  have : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  have harchK : ∀ σ : K →+* ℂ, Real.log ((HermLine.standard n).metric
      fun k i ↦ σ (coordVec z k i)) ≤ ∑ k, Real.log (Real.sqrt (n k + 1) * R) := by
    intro σ
    let σ' : AlgebraicClosure ℚ →+* ℂ := ComplexEmbedding.lift (AlgebraicClosure ℚ) σ
    have hσ : ∀ k i, σ (coordVec z k i) = σ' (z k i) := by
      intro k i
      have := ComplexEmbedding.lift_algebraMap_apply (AlgebraicClosure ℚ) σ (coordVec z k i)
      rw [← this]
      rfl
    have hpos : ∀ k, 0 < l2Norm (fun i ↦ σ (coordVec z k i)) := by
      intro k
      obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hz k)
      refine vectorL2Norm_pos (Function.ne_iff.mpr ⟨i0, ?_⟩)
      intro h
      apply hi0
      have h2 := (map_eq_zero σ).mp h
      have := congrArg Subtype.val h2
      simpa [coordVec] using this
    change Real.log (∏ k, l2Norm (fun i ↦ σ (coordVec z k i))) ≤ _
    rw [Real.log_prod (fun k _ ↦ (hpos k).ne')]
    refine Finset.sum_le_sum fun k _ ↦ Real.log_le_log (hpos k) ?_
    have := vectorL2Norm_le_sqrt_card_mul (fun i ↦ σ (coordVec z k i)) hR.le (fun i ↦ by rw [hσ]; exact harch σ' k i)
    simpa using this
  have harchSum : ∑ σ : K →+* ℂ, Real.log ((HermLine.standard n).metric
      fun k i ↦ σ (coordVec z k i)) ≤ d * ∑ k, Real.log (Real.sqrt (n k + 1) * R) := by
    refine (Finset.sum_le_sum fun σ _ ↦ harchK σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]

  set S := ∑ k, Real.log (Real.sqrt (n k + 1) * R) with hS
  unfold height
  rw [← hd_def]
  calc d⁻¹ * (_ + _) ≤ d⁻¹ * (Fintype.card ι * (d * Real.log δ) +
        d * ∑ k, Real.log (Real.sqrt (n k + 1) * R)) :=
        mul_le_mul_of_nonneg_left (add_le_add hfin harchSum) (inv_pos.mpr hd).le
    _ = ∑ k, (Real.log δ + Real.log (Real.sqrt (n k + 1) * R)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hS]
        field_simp

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem exists_rootsOfUnity_eval_ne_zero {s : ℕ} {c : MvPolynomial (Fin s) ℚ} (hc : c ≠ 0) :
    ∃ (N : ℕ) (y : Fin s → AlgebraicClosure ℚ), 0 < N ∧ (∀ j, y j ^ N = 1) ∧ aeval y c ≠ 0 := by
  classical
  set N := c.totalDegree + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos _
  have : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hNpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  set S := Polynomial.nthRootsFinset N (1 : AlgebraicClosure ℚ)
  have hS : S.card = N := hζ.card_nthRootsFinset
  set c' := MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)) c
  have hc' : c' ≠ 0 := by
    intro h
    apply hc
    exact MvPolynomial.map_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective
      (h.trans (map_zero _).symm)
  by_contra hcon
  push Not at hcon
  apply hc'
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset c' (fun _ ↦ S) (fun i ↦ ?_) ?_
  · rw [hS]
    calc c'.degreeOf i = c.degreeOf i := by
          simp only [c', MvPolynomial.degreeOf_def,
            MvPolynomial.degrees_map_of_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective]
      _ ≤ c.totalDegree := MvPolynomial.degreeOf_le_totalDegree c i
      _ < N := Nat.lt_succ_self _
  · intro x hx
    have hx' : ∀ j, x j ^ N = 1 := fun j ↦ (Polynomial.mem_nthRootsFinset hNpos 1).mp (hx j)
    have := hcon N x hNpos hx'
    rw [MvPolynomial.eval_map]
    rw [MvPolynomial.aeval_def] at this
    exact this

theorem exists_algHom_rootsOfUnity_ne_zero {B : Type*} [CommRing B] [IsDomain B] [Algebra ℚ B]
    {s : ℕ} (g0 : MvPolynomial (Fin s) ℚ →ₐ[ℚ] B) (hinj : Function.Injective g0)
    (hint : g0.IsIntegral) {g : B} (hg : g ≠ 0) :
    ∃ ψ : B →ₐ[ℚ] AlgebraicClosure ℚ, ψ g ≠ 0 ∧
      ∀ j, ∃ N : ℕ, 0 < N ∧ ψ (g0 (MvPolynomial.X j)) ^ N = 1 := by
  classical
  let : Algebra (MvPolynomial (Fin s) ℚ) B := g0.toRingHom.toAlgebra
  have hmap : ∀ a, algebraMap (MvPolynomial (Fin s) ℚ) B a = g0 a := fun _ ↦ rfl
  have hInt : Algebra.IsIntegral (MvPolynomial (Fin s) ℚ) B := ⟨hint⟩

  have hI : (Ideal.span {g}).comap (algebraMap (MvPolynomial (Fin s) ℚ) B) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hg (Ideal.mem_span_singleton_self g)
      (Algebra.IsIntegral.isIntegral g)
  obtain ⟨c, hcI, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hcI)

  obtain ⟨N, y, hNpos, hy, hcy⟩ := exists_rootsOfUnity_eval_ne_zero hc0
  set ev : MvPolynomial (Fin s) ℚ →+* AlgebraicClosure ℚ := (aeval y).toRingHom with hev
  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  have hker : RingHom.ker (algebraMap (MvPolynomial (Fin s) ℚ) B) ≤ RingHom.ker ev := by
    intro a ha
    rw [RingHom.mem_ker, hmap] at ha
    have : a = 0 := hinj (ha.trans (map_zero g0).symm)
    rw [this]
    exact (RingHom.ker ev).zero_mem
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (RingHom.ker ev) hker
  have := hQ
  set p := Q.comap (algebraMap (MvPolynomial (Fin s) ℚ) B) with hp
  have : p.IsPrime := Ideal.comap_isPrime _ Q

  have hvan : ∀ a ∈ p, ev a = 0 := fun a ha ↦ by
    rw [hQc] at ha
    exact RingHom.mem_ker.mp ha
  let evq : MvPolynomial (Fin s) ℚ ⧸ p →+* AlgebraicClosure ℚ := Ideal.Quotient.lift p ev hvan
  have hevq : Function.Injective evq :=
    RingHom.lift_injective_of_ker_le_ideal p hvan (by rw [hQc])
  let : Algebra (MvPolynomial (Fin s) ℚ ⧸ p) (AlgebraicClosure ℚ) := evq.toAlgebra
  have : Module.IsTorsionFree (MvPolynomial (Fin s) ℚ ⧸ p) (AlgebraicClosure ℚ) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hevq
  have : Module.IsTorsionFree (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr Ideal.algebraMap_quotient_injective
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q) := Algebra.IsIntegral.quotient
  let ψq : (B ⧸ Q) →ₐ[MvPolynomial (Fin s) ℚ ⧸ p] AlgebraicClosure ℚ := IsAlgClosed.lift
  let ψ0 : B →+* AlgebraicClosure ℚ := ψq.toRingHom.comp (Ideal.Quotient.mk Q)
  have hψ0 : ∀ a, ψ0 (g0 a) = aeval y a := by
    intro a
    have h1 : Ideal.Quotient.mk Q (g0 a) =
        algebraMap (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q) (Ideal.Quotient.mk p a) := rfl
    change ψq (Ideal.Quotient.mk Q (g0 a)) = aeval y a
    rw [h1, ψq.commutes]
    rfl
  refine ⟨ψ0.toRatAlgHom, ?_, fun j ↦ ⟨N, hNpos, ?_⟩⟩
  · intro h0
    apply hcy
    rw [← hψ0, ← hmap, ← hb]
    rw [map_mul]
    change ψ0 b * ψ0.toRatAlgHom g = 0
    rw [h0, mul_zero]
  · change ψ0 (g0 (X j)) ^ N = 1
    rw [hψ0, aeval_X]
    exact hy j

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem norm_le_of_monic_root {A : Type*} [CommRing A] (p : Polynomial A) (hp : p.Monic)
    (f : A →+* ℂ) (z : ℂ) (hz : p.eval₂ f z = 0) (M : ℕ → ℝ)
    (hM : ∀ j < p.natDegree, ‖f (p.coeff j)‖ ≤ M j) :
    ‖z‖ ≤ max 1 (∑ j ∈ Finset.range p.natDegree, M j) := by
  set m := p.natDegree with hm_def
  by_contra hcon
  rw [not_le] at hcon
  have h1 : 1 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hcon
  have hS : (∑ j ∈ Finset.range m, M j) < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hcon
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, ← hm_def, hp.coeff_natDegree, map_one,
    one_mul] at hz
  have hzm : z ^ m = -∑ j ∈ Finset.range m, f (p.coeff j) * z ^ j := by
    linear_combination hz
  have hm : m ≠ 0 := by
    intro hm0
    rw [hm0, Finset.sum_range_zero, pow_zero, neg_zero] at hzm
    exact one_ne_zero hzm
  have hle : ‖z‖ ^ m ≤ (∑ j ∈ Finset.range m, M j) * ‖z‖ ^ (m - 1) := by
    calc ‖z‖ ^ m = ‖z ^ m‖ := (norm_pow _ _).symm
      _ = ‖∑ j ∈ Finset.range m, f (p.coeff j) * z ^ j‖ := by rw [hzm, norm_neg]
      _ ≤ ∑ j ∈ Finset.range m, ‖f (p.coeff j) * z ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range m, M j * ‖z‖ ^ (m - 1) := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          have hjm : j < m := Finset.mem_range.mp hj
          rw [norm_mul, norm_pow]
          have hj' : j ≤ m - 1 := by omega
          exact mul_le_mul (hM j hjm) (pow_le_pow_right₀ h1.le hj') (by positivity)
            ((norm_nonneg _).trans (hM j hjm))
      _ = _ := by rw [Finset.sum_mul]
  have hsplit : ‖z‖ ^ m = ‖z‖ * ‖z‖ ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit] at hle
  have hpos : 0 < ‖z‖ ^ (m - 1) := by positivity
  have := le_of_mul_le_mul_right hle hpos
  linarith

theorem norm_eval₂_le_of_norm_eq_one {s : ℕ} (q : MvPolynomial (Fin s) ℚ) (z : Fin s → ℂ)
    (hz : ∀ j, ‖z j‖ = 1) :
    ‖eval₂ (algebraMap ℚ ℂ) z q‖ ≤ ∑ μ ∈ q.support, |((q.coeff μ : ℚ) : ℝ)| := by
  rw [eval₂_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ ↦ ?_)
  rw [norm_mul, norm_prod]
  have h1 : ∏ i ∈ μ.support, ‖z i ^ μ i‖ = 1 :=
    Finset.prod_eq_one fun i _ ↦ by rw [norm_pow, hz, one_pow]
  rw [h1, mul_one, eq_ratCast, Complex.norm_ratCast]

def ClearsDen {s : ℕ} (d : ℕ) (q : MvPolynomial (Fin s) ℚ) : Prop :=
  ∀ μ, ∃ k : ℤ, (d : ℚ) * q.coeff μ = k

theorem clearsDen_prod_den {s : ℕ} (q : MvPolynomial (Fin s) ℚ) :
    ClearsDen (∏ μ ∈ q.support, (q.coeff μ).den) q := by
  intro μ
  by_cases hμ : μ ∈ q.support
  · rw [← Finset.mul_prod_erase _ _ hμ]
    refine ⟨(q.coeff μ).num * ∏ ν ∈ q.support.erase μ, ((q.coeff ν).den : ℤ), ?_⟩
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  · rw [MvPolynomial.notMem_support_iff.mp hμ, mul_zero]
    exact ⟨0, by simp⟩

theorem ClearsDen.mul_left {s : ℕ} {d : ℕ} {q : MvPolynomial (Fin s) ℚ} (h : ClearsDen d q) (e : ℕ) :
    ClearsDen (e * d) q := by
  intro μ
  obtain ⟨k, hk⟩ := h μ
  exact ⟨e * k, by push_cast; rw [mul_assoc, hk]⟩

theorem isIntegral_mul_aeval {s : ℕ} {y : Fin s → AlgebraicClosure ℚ}
    (hy : ∀ j, IsIntegral ℤ (y j)) {d : ℕ} {q : MvPolynomial (Fin s) ℚ} (hq : ClearsDen d q) :
    IsIntegral ℤ ((d : AlgebraicClosure ℚ) * aeval y q) := by
  rw [← mem_integralClosure_iff, MvPolynomial.aeval_def, eval₂_eq, Finset.mul_sum]
  refine Subalgebra.sum_mem _ fun μ _ ↦ ?_
  obtain ⟨k, hk⟩ := hq μ
  have h1 : (d : AlgebraicClosure ℚ) * (algebraMap ℚ (AlgebraicClosure ℚ) (q.coeff μ) *
      ∏ i ∈ μ.support, y i ^ μ i) = (k : AlgebraicClosure ℚ) * ∏ i ∈ μ.support, y i ^ μ i := by
    rw [← mul_assoc]
    congr 1
    have h2 : (d : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) (d : ℚ) := by simp
    rw [h2, ← map_mul, hk, map_intCast]
  rw [h1]
  exact Subalgebra.mul_mem _ (intCast_mem _ k)
    (Subalgebra.prod_mem _ fun i _ ↦ Subalgebra.pow_mem _ (by rw [mem_integralClosure_iff]; exact hy i) _)

theorem isIntegral_of_pow_eq_one {x : AlgebraicClosure ℚ} {N : ℕ} (hN : 0 < N) (hx : x ^ N = 1) :
    IsIntegral ℤ x := by
  refine ⟨Polynomial.X ^ N - 1, Polynomial.monic_X_pow_sub_C 1 hN.ne', ?_⟩
  simp [hx]

theorem exists_integral_bound {B : Type*} [CommRing B] [Algebra ℚ B] {s : ℕ}
    (g0 : MvPolynomial (Fin s) ℚ →ₐ[ℚ] B) (hint : g0.IsIntegral) (b : B) :
    ∃ (δ : ℕ) (R : ℝ), 0 < δ ∧ 1 ≤ R ∧ ∀ ψ : B →ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ j, ∃ N : ℕ, 0 < N ∧ ψ (g0 (MvPolynomial.X j)) ^ N = 1) →
      IsIntegral ℤ ((δ : AlgebraicClosure ℚ) * ψ b) ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, ‖σ (ψ b)‖ ≤ R := by
  obtain ⟨p, hpm, hpb⟩ := hint b
  set m := p.natDegree with hm_def
  set δ : ℕ := ∏ j ∈ Finset.range m, ∏ μ ∈ (p.coeff j).support, ((p.coeff j).coeff μ).den with hδ_def
  have hδpos : 0 < δ := Finset.prod_pos fun j _ ↦ Finset.prod_pos fun μ _ ↦ Rat.den_pos _
  have hδ : ∀ j < m, ClearsDen δ (p.coeff j) := by
    intro j hj
    rw [hδ_def, ← Finset.prod_erase_mul _ _ (Finset.mem_range.mpr hj)]
    exact (clearsDen_prod_den (p.coeff j)).mul_left _
  set M : ℕ → ℝ := fun j ↦ ∑ μ ∈ (p.coeff j).support, |(((p.coeff j).coeff μ : ℚ) : ℝ)|
  refine ⟨δ, max 1 (∑ j ∈ Finset.range m, M j), hδpos, le_max_left _ _, fun ψ hψ ↦ ?_⟩
  set φ : MvPolynomial (Fin s) ℚ →ₐ[ℚ] AlgebraicClosure ℚ := ψ.comp g0 with hφ_def
  set y : Fin s → AlgebraicClosure ℚ := fun j ↦ φ (X j) with hy_def
  have hφ : ∀ q, φ q = aeval y q := fun q ↦ by
    conv_lhs => rw [MvPolynomial.aeval_unique φ]
    rfl
  have hy : ∀ j, IsIntegral ℤ (y j) := fun j ↦ by
    obtain ⟨N, hN, h⟩ := hψ j
    exact isIntegral_of_pow_eq_one hN h
  have hw : p.eval₂ (φ : MvPolynomial (Fin s) ℚ →+* AlgebraicClosure ℚ) (ψ b) = 0 := by
    have h := congrArg (ψ : B →+* AlgebraicClosure ℚ) hpb
    rw [map_zero, Polynomial.hom_eval₂] at h
    exact h
  constructor
  ·
    set O := integralClosure ℤ (AlgebraicClosure ℚ)
    set q : Polynomial (AlgebraicClosure ℚ) :=
      (p.map (φ : MvPolynomial (Fin s) ℚ →+* AlgebraicClosure ℚ)).scaleRoots (δ : AlgebraicClosure ℚ)
    have hqm : q.Monic :=
      (Polynomial.monic_scaleRoots_iff _).mpr (hpm.map _)
    have hq0 : q.eval ((δ : AlgebraicClosure ℚ) * ψ b) = 0 := by
      have h := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id (AlgebraicClosure ℚ))
        (s := (δ : AlgebraicClosure ℚ)) (r := ψ b) (p := p.map (φ : MvPolynomial (Fin s) ℚ →+* _))
        (by rw [Polynomial.eval₂_map]; exact hw)
      exact h
    have hnat : (p.map (φ : MvPolynomial (Fin s) ℚ →+* AlgebraicClosure ℚ)).natDegree = m :=
      hpm.natDegree_map _
    have hcoeff : ∀ i, q.coeff i ∈ O := by
      intro i
      rw [Polynomial.coeff_scaleRoots, hnat, Polynomial.coeff_map]
      rcases lt_trichotomy i m with hi | hi | hi
      · obtain ⟨e, he⟩ : ∃ e, m - i = e + 1 := ⟨m - i - 1, by omega⟩
        rw [he, pow_succ, show ∀ a b c : AlgebraicClosure ℚ, a * (b * c) = (c * a) * b from
          fun a b c ↦ by ring]
        refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ (natCast_mem _ δ) _)
        · rw [mem_integralClosure_iff]
          simpa [hφ] using isIntegral_mul_aeval hy (hδ i hi)
      · have hc : p.coeff m = 1 := hpm.coeff_natDegree
        rw [hi, hc, map_one, Nat.sub_self, pow_zero, mul_one]
        exact Subalgebra.one_mem _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul]
        exact Subalgebra.zero_mem _
    have hlifts : q ∈ Polynomial.lifts (algebraMap O (AlgebraicClosure ℚ)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      exact ⟨⟨q.coeff i, hcoeff i⟩, rfl⟩
    obtain ⟨q', hq'map, -, hq'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqm
    have hO : IsIntegral O ((δ : AlgebraicClosure ℚ) * ψ b) :=
      ⟨q', hq'm, by rw [← Polynomial.eval_map, hq'map]; exact hq0⟩
    exact isIntegral_trans _ hO
  · intro σ
    refine norm_le_of_monic_root p hpm
      (σ.comp (φ : MvPolynomial (Fin s) ℚ →+* AlgebraicClosure ℚ)) (σ (ψ b)) ?_ M ?_
    · rw [← Polynomial.hom_eval₂, hw, map_zero]
    · intro j _
      have hz : ∀ i, ‖σ (y i)‖ = 1 := fun i ↦ by
        obtain ⟨N, hN, h⟩ := hψ i
        have h' : y i ^ N = 1 := h
        exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, h', map_one]) hN.ne'
      have h1 : (σ.comp (φ : MvPolynomial (Fin s) ℚ →+* AlgebraicClosure ℚ)) (p.coeff j) =
          eval₂ (algebraMap ℚ ℂ) (fun i ↦ σ (y i)) (p.coeff j) := by
        show σ (φ (p.coeff j)) = _
        rw [hφ, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
        congr 1
        exact Subsingleton.elim _ _
      rw [h1]
      exact norm_eval₂_le_of_norm_eq_one _ _ hz

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem denseBoundedHeight : DenseBoundedHeight.Statement := by
  intro ι _ _ n P
  obtain ⟨c, hc⟩ := P.exists_chart
  obtain ⟨s, g0, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (P.ChartAlg c)
  let b : Coord n → P.ChartAlg c := fun v ↦ (P.chartMap c).rangeRestrict (X v)
  choose δ R hδ hR hbd using fun v ↦ exists_integral_bound g0 hint (b v)
  set Δ : ℕ := ∏ v, δ v with hΔ
  set R0 : ℝ := 1 + ∑ v, R v with hR0
  have hΔpos : 0 < Δ := Finset.prod_pos fun v _ ↦ hδ v
  have hRnn : ∀ v, 0 ≤ R v := fun v ↦ zero_le_one.trans (hR v)
  have hR0pos : 0 < R0 := by
    have := Finset.sum_nonneg fun v (_ : v ∈ Finset.univ) ↦ hRnn v
    linarith
  refine ⟨{z | ∃ ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ j, ∃ N : ℕ, 0 < N ∧ ψ (g0 (X j)) ^ N = 1) ∧ z = P.chartPoint c ψ},
    ∑ k, (Real.log Δ + Real.log (Real.sqrt (n k + 1) * R0)), ?_, ?_, ?_⟩
  · rintro z ⟨ψ, -, rfl⟩
    exact P.chartPoint_mem c hc ψ
  · intro m f hf hvan
    by_contra hfP
    have hg := P.chartMap_ne_zero c hc hf hfP
    obtain ⟨ψ, hψ, hroots⟩ := exists_algHom_rootsOfUnity_ne_zero g0 hinj hint hg
    apply hψ
    rw [← P.evalCone_chartPoint c ψ f]
    exact hvan _ ⟨ψ, hroots, rfl⟩
  · rintro z ⟨ψ, hroots, rfl⟩
    refine height_standard_le _ (P.chartPoint_mem c hc ψ).1 hΔpos hR0pos (fun k i ↦ ?_)
      (fun σ k i ↦ ?_)
    · have h1 := (hbd ⟨k, i⟩ ψ hroots).1
      have h2 : (Δ : AlgebraicClosure ℚ) * P.chartPoint c ψ k i =
          ((∏ w ∈ Finset.univ.erase ⟨k, i⟩, δ w : ℕ) : AlgebraicClosure ℚ) *
            ((δ ⟨k, i⟩ : AlgebraicClosure ℚ) * ψ (b ⟨k, i⟩)) := by
        rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
        rfl
      rw [h2]
      have h3 : IsIntegral ℤ (((∏ w ∈ Finset.univ.erase ⟨k, i⟩, δ w : ℕ) : AlgebraicClosure ℚ)) := by
        have := isIntegral_algebraMap (R := ℤ) (A := AlgebraicClosure ℚ)
          (x := ((∏ w ∈ Finset.univ.erase ⟨k, i⟩, δ w : ℕ) : ℤ))
        simpa using this
      exact h3.mul h1
    · calc ‖σ (P.chartPoint c ψ k i)‖ ≤ R ⟨k, i⟩ := (hbd ⟨k, i⟩ ψ hroots).2 σ
        _ ≤ ∑ v, R v := Finset.single_le_sum (fun v _ ↦ hRnn v) (Finset.mem_univ _)
        _ ≤ R0 := by linarith

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightLowerBound.main : HeightLowerBound.Statement := heightLowerBound

theorem HeightMetricChange.main : HeightMetricChange.Statement := heightMetricChange

theorem HeightLocalAgreement.main : HeightLocalAgreement.Statement := heightLocalAgreement

theorem HeightPullback.main : HeightPullback.Statement := heightPullback

theorem HeightComparison.main : HeightComparison.Statement := heightComparison

theorem DenseBoundedHeight.main : DenseBoundedHeight.Statement := denseBoundedHeight

theorem SlopeMaxExtension.main : SlopeMaxExtension.Statement := slopeMaxExtension

theorem FlagDegreeBound.main : FlagDegreeBound.Statement := flagDegreeBound

end GroundTheory.Heights₂.Heights
end
