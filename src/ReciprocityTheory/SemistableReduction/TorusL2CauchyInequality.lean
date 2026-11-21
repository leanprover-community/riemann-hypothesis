import ReciprocityTheory.SemistableReduction.SJCore
import ReciprocityTheory.SemistableReduction.SjHolds
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import Lemmata.GeneralBFactLeftExtra.Imports
import ReciprocityTheory.SemistableReduction.HeightLowerBound
import ReciprocityTheory.SemistableReduction.IntCores
import ReciprocityTheory.SemistableReduction.TorusMean
import ReciprocityTheory.SemistableReduction.TorusLex
import ReciprocityTheory.SemistableReduction.GramOfLinearOrder
import ReciprocityTheory.SemistableReduction.SphereTorusC

section
namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

section Gauss

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

theorem coeff_le_gauss_abs (w : FinitePlace K) (f : MvPolynomial σ K) (s : σ →₀ ℕ) :
    w (f.coeff s) ≤ gaussAbs w f := by
  unfold gaussAbs
  by_cases hs : s ∈ f.support
  · have h := Finset.le_sup (f := fun s => (w (f.coeff s)).toNNReal) hs
    have h2 : ((w (f.coeff s)).toNNReal : ℝ) ≤ _ := NNReal.coe_le_coe.2 h
    rwa [Real.coe_toNNReal _ (apply_nonneg w _)] at h2
  · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
    exact NNReal.coe_nonneg _

theorem gauss_abs_le_of_coeff_le (w : FinitePlace K) (f : MvPolynomial σ K) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ s, w (f.coeff s) ≤ M) : gaussAbs w f ≤ M := by
  unfold gaussAbs
  have h1 : (f.support.sup fun s => (w (f.coeff s)).toNNReal) ≤ M.toNNReal :=
    Finset.sup_le fun s _ => Real.toNNReal_le_toNNReal (h s)
  have h2 := NNReal.coe_le_coe.2 h1
  rwa [Real.coe_toNNReal _ hM] at h2

theorem gauss_abs_attained_at_coeff (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    ∃ s ∈ f.support, gaussAbs w f = w (f.coeff s) := by
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup f.support
    (MvPolynomial.support_nonempty.2 hf) (fun s => (w (f.coeff s)).toNNReal)
  refine ⟨s, hs, ?_⟩
  unfold gaussAbs
  rw [hsup, Real.coe_toNNReal _ (apply_nonneg w _)]

theorem gauss_abs_pos_of_ne_zero (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    0 < gaussAbs w f := by
  obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
  rw [h]
  exact FinitePlace.pos_iff.2 (MvPolynomial.mem_support_iff.1 hs)

theorem finite_place_sum_le {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ t, w (a i) ≤ M) : w (∑ i ∈ t, a i) ≤ M := by
  first | exact Bl.general_b_fact_left_extra.goal1 .. | (apply Bl.general_b_fact_left_extra.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_extra.goal1 <;> assumption)

theorem finite_place_sum_lt {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 < M) (h : ∀ i ∈ t, w (a i) < M) : w (∑ i ∈ t, a i) < M := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hM
  | insert j t hj ih =>
    rw [Finset.sum_insert hj]
    refine (FinitePlace.add_le w _ _).trans_lt (max_lt (h j (Finset.mem_insert_self j t)) ?_)
    exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)

theorem finite_place_add_eq_of_lt (w : FinitePlace K) (x y : K) (h : w y < w x) : w (x + y) = w x := by
  apply le_antisymm
  · exact (FinitePlace.add_le w x y).trans (max_le le_rfl h.le)
  · have h1 : w x ≤ max (w (x + y)) (w (-y)) := by
      have := FinitePlace.add_le w (x + y) (-y)
      rwa [add_neg_cancel_right] at this
    rw [map_neg_eq_map] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)

theorem gauss_abs_mul_of_monomial_order (m : MonomialOrder σ) (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  classical
  have hGf := gauss_abs_pos_of_ne_zero w f hf
  have hGg := gauss_abs_pos_of_ne_zero w g hg
  apply le_antisymm
  · refine gauss_abs_le_of_coeff_le w _ (mul_nonneg hGf.le hGg.le) fun u => ?_
    rw [MvPolynomial.coeff_mul]
    refine finite_place_sum_le w _ _ (mul_nonneg hGf.le hGg.le) fun x _ => ?_
    rw [map_mul]
    exact mul_le_mul (coeff_le_gauss_abs w f _) (coeff_le_gauss_abs w g _) (apply_nonneg w _) hGf.le
  ·
    set Sf := f.support.filter (fun s => w (f.coeff s) = gaussAbs w f)
    set Sg := g.support.filter (fun s => w (g.coeff s) = gaussAbs w g)
    have hSf : Sf.Nonempty := by
      obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
      exact ⟨s, Finset.mem_filter.2 ⟨hs, h.symm⟩⟩
    have hSg : Sg.Nonempty := by
      obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w g hg
      exact ⟨s, Finset.mem_filter.2 ⟨hs, h.symm⟩⟩
    obtain ⟨s0, hs0, hs0max⟩ := Finset.exists_max_image Sf (fun s => m.toSyn s) hSf
    obtain ⟨t0, ht0, ht0max⟩ := Finset.exists_max_image Sg (fun s => m.toSyn s) hSg
    have hfs0 : w (f.coeff s0) = gaussAbs w f := (Finset.mem_filter.1 hs0).2
    have hgt0 : w (g.coeff t0) = gaussAbs w g := (Finset.mem_filter.1 ht0).2
    have hbigf : ∀ s, m.toSyn s0 < m.toSyn s → w (f.coeff s) < gaussAbs w f := by
      intro s hs
      refine lt_of_le_of_ne (coeff_le_gauss_abs w f s) fun heq => ?_
      have hmem : s ∈ Sf := by
        refine Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 fun h0 => ?_, heq⟩
        rw [h0, map_zero] at heq
        exact hGf.ne heq
      exact absurd (hs0max s hmem) (not_le.2 hs)
    have hbigg : ∀ t, m.toSyn t0 < m.toSyn t → w (g.coeff t) < gaussAbs w g := by
      intro t ht
      refine lt_of_le_of_ne (coeff_le_gauss_abs w g t) fun heq => ?_
      have hmem : t ∈ Sg := by
        refine Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 fun h0 => ?_, heq⟩
        rw [h0, map_zero] at heq
        exact hGg.ne heq
      exact absurd (ht0max t hmem) (not_le.2 ht)
    have hmemu : (s0, t0) ∈ Finset.HasAntidiagonal.antidiagonal (s0 + t0) := Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    have hrest : w (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (s0 + t0)).erase (s0, t0),
        f.coeff x.1 * g.coeff x.2) < gaussAbs w f * gaussAbs w g := by
      refine finite_place_sum_lt w _ _ (mul_pos hGf hGg) fun x hx => ?_
      obtain ⟨hxne, hxmem⟩ := Finset.mem_erase.1 hx
      have hsum : x.1 + x.2 = s0 + t0 := Finset.HasAntidiagonal.mem_antidiagonal.1 hxmem
      have hsyn : m.toSyn x.1 + m.toSyn x.2 = m.toSyn s0 + m.toSyn t0 := by
        rw [← map_add, ← map_add, hsum]
      rw [map_mul]
      rcases lt_trichotomy (m.toSyn x.1) (m.toSyn s0) with h1 | h1 | h1
      · have h2 : m.toSyn t0 < m.toSyn x.2 := by
          by_contra h2
          have := add_lt_add_of_lt_of_le h1 (not_lt.1 h2)
          rw [hsyn] at this
          exact lt_irrefl _ this
        calc w (f.coeff x.1) * w (g.coeff x.2) ≤ gaussAbs w f * w (g.coeff x.2) :=
              mul_le_mul_of_nonneg_right (coeff_le_gauss_abs w f _) (apply_nonneg w _)
          _ < gaussAbs w f * gaussAbs w g := mul_lt_mul_of_pos_left (hbigg _ h2) hGf
      · exfalso
        have e1 : x.1 = s0 := m.toSyn.injective h1
        have e2 : x.2 = t0 := by
          rw [e1] at hsum
          exact add_left_cancel hsum
        exact hxne (Prod.ext e1 e2)
      · calc w (f.coeff x.1) * w (g.coeff x.2) ≤ w (f.coeff x.1) * gaussAbs w g :=
              mul_le_mul_of_nonneg_left (coeff_le_gauss_abs w g _) (apply_nonneg w _)
          _ < gaussAbs w f * gaussAbs w g := mul_lt_mul_of_pos_right (hbigf _ h1) hGg
    have hcoeff : w ((f * g).coeff (s0 + t0)) = gaussAbs w f * gaussAbs w g := by
      rw [MvPolynomial.coeff_mul, ← Finset.add_sum_erase _ _ hmemu]
      rw [finite_place_add_eq_of_lt w _ _ (by rwa [map_mul, hfs0, hgt0]), map_mul, hfs0, hgt0]
    rw [← hcoeff]
    exact coeff_le_gauss_abs w _ _

theorem gauss_abs_mul [Fintype σ] (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact gauss_abs_mul_of_monomial_order MonomialOrder.lex w f g hf hg

end Gauss

end ReciprocityTheory.MultiplicativeHeights
end

section
namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory NumberField

theorem gauss_abs_log_support_finite {K : Type*} [Field K] [NumberField K] {σ : Type*}
    (f : MvPolynomial σ K) (hf : f ≠ 0) :
    (Function.support fun w : FinitePlace K => Real.log (gaussAbs w f)).Finite := by
  have hfin : (⋃ s ∈ f.support, Function.mulSupport fun w : FinitePlace K => w (f.coeff s)).Finite :=
    Set.Finite.biUnion f.support.finite_toSet fun s hs =>
      FinitePlace.hasFiniteMulSupport (MvPolynomial.mem_support_iff.1 hs)
  refine hfin.subset fun w hw => ?_
  by_contra hnot
  apply hw
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot
  have h1 : gaussAbs w f = 1 := by
    apply le_antisymm
    · refine gauss_abs_le_of_coeff_le w f zero_le_one fun s => ?_
      by_cases hs : s ∈ f.support
      · exact (hnot s hs).le
      · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
        exact zero_le_one
    · obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
      rw [h, hnot s hs]
  simp [h1]

theorem isMultiHomogeneous_map_ring {K : Type*} [Field K] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : IsMultiHomogeneous a f) (φ : K →+* ℂ) :
    IsMultiHomogeneous a (MvPolynomial.map φ f) := by
  unfold IsMultiHomogeneous at hf ⊢
  first
  | exact fun d hd => hf d (by rwa [MvPolynomial.support_map_of_injective _ φ.injective] at hd)
  | exact fun b => (hf b).map φ
  | simpa [MvPolynomial.support_map_of_injective _ φ.injective] using hf
  | (intro d hd
     simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map, ne_eq, map_eq_zero] at hd
     exact hf d (by simpa using hd))

theorem sphere_mean_mul_multihomogeneous (hInt : SphereLogIntegrableStatement) (B n : ℕ) (a a' : Fin B → ℕ)
    (F G : MvPolynomial (Fin B × Fin n) ℂ) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hF : IsMultiHomogeneous a F) (hG : IsMultiHomogeneous a' G) :
    blockSphereMean B n (F * G) = blockSphereMean B n F + blockSphereMean B n G := by
  unfold blockSphereMean
  rw [← integral_add (hInt B n a F hF0 hF) (hInt B n a' G hG0 hG)]
  refine integral_congr_ae ?_
  filter_upwards [ae_blockSphere_eval_ne_zero B n a F hF0 hF, ae_blockSphere_eval_ne_zero B n a' G hG0 hG]
    with z hz1 hz2
  rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hz1) (norm_ne_zero_iff.2 hz2)]

theorem gauss_height_mul_multihomogeneous (hInt : SphereLogIntegrableStatement) {K : Type*} [Field K] [NumberField K]
    (B n : ℕ) (a a' : Fin B → ℕ) (f g : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0)
    (haf : IsMultiHomogeneous a f) (hbg : IsMultiHomogeneous a' g) :
    h0 (f * g) = h0 f + h0 g := by
  unfold h0
  have hfin : ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w (f * g)) =
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) + ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w g) := by
    rw [← finsum_add_distrib (gauss_abs_log_support_finite f hf) (gauss_abs_log_support_finite g hg)]
    refine finsum_congr fun w => ?_
    rw [gauss_abs_mul w f g hf hg, Real.log_mul (gauss_abs_pos_of_ne_zero w f hf).ne'
      (gauss_abs_pos_of_ne_zero w g hg).ne']
  have hinf : ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ (f * g)) =
      ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ f) +
        ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ g) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have hinj := MvPolynomial.map_injective φ φ.injective (σ := Fin B × Fin n)
    rw [map_mul]
    exact sphere_mean_mul_multihomogeneous hInt B n a a' _ _
      (fun h => hf (hinj (by rw [h, map_zero])))
      (fun h => hg (hinj (by rw [h, map_zero])))
      (isMultiHomogeneous_map_ring a f haf φ) (isMultiHomogeneous_map_ring a' g hbg φ)
  rw [hfin, hinf]
  ring

theorem gauss_height_const_eq_zero {K : Type*} [Field K] [NumberField K] (B n : ℕ) (hn : 0 < n) (c : K)
    (hc : c ≠ 0) : h0 (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) = 0 := by
  unfold h0

  have hG : ∀ w : FinitePlace K, gaussAbs w (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) = w c := by
    intro w
    apply le_antisymm
    · refine gauss_abs_le_of_coeff_le w _ (apply_nonneg w c) fun s => ?_
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact le_rfl
      · rw [map_zero]; exact apply_nonneg w c
    · have := coeff_le_gauss_abs w (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) 0
      rwa [MvPolynomial.coeff_C, if_pos rfl] at this
  simp_rw [hG]

  have hP : IsProbabilityMeasure (blockSphereProb B n) := by
    have : NeZero n := ⟨hn.ne'⟩
    have hne : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
      rw [Ne, Measure.measure_univ_eq_zero]
      exact Measure.toSphere_ne_zero _
    have : IsProbabilityMeasure (sphereProb n) := by
      unfold sphereProb
      exact ProbabilityTheory.cond_isProbabilityMeasure hne
    unfold blockSphereProb
    infer_instance
  have hM : ∀ φ : K →+* ℂ, blockSphereMean B n
      (MvPolynomial.map φ (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K)) = Real.log ‖φ c‖ := by
    intro φ
    unfold blockSphereMean
    simp [MvPolynomial.map_C, MvPolynomial.eval_C]
  simp_rw [hM]

  have hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv, neg_add_cancel, zero_div]

theorem gauss_height_add_of_sphere (hInt : SphereLogIntegrableStatement) : HeightAdditiveStatement := by
  intro K _ _ B n a a' f g hn hf hg haf hbg
  refine ⟨gauss_height_mul_multihomogeneous hInt B n a a' f g hf hg haf hbg, fun c hc => ?_⟩
  have hC : IsMultiHomogeneous (fun _ : Fin B => 0) (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) := by
    intro s hs b
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hs
    split_ifs at hs with h
    · subst h; simp
    · exact absurd rfl hs
  have hC0 : (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) ≠ 0 := by
    rwa [Ne, MvPolynomial.C_eq_zero]
  rw [gauss_height_mul_multihomogeneous hInt B n _ a _ f hC0 hf hC haf, gauss_height_const_eq_zero B n hn c hc, zero_add]

end ReciprocityTheory.MultiplicativeHeights
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Polynomial

theorem integral_Ioc_log_eval_eq_logMahlerMeasure (q : ℂ[X]) :
    ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖q.eval (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ =
      q.logMahlerMeasure := by
  rw [logMahlerMeasure_def, Real.circleAverage, ← intervalIntegral.integral_of_le zero_le_one]
  have h2 : (2 * Real.pi) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left
    (fun θ => Real.log ‖eval (circleMap 0 1 θ) q‖) (a := 0) (b := 1) h2
  simp only [mul_zero, mul_one] at this
  rw [← this]
  congr 1
  funext t
  congr 3
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring_nf

theorem logMahlerMeasure_comp_C_mul_X_le (p : ℂ[X]) {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    (p.comp (C c * X)).logMahlerMeasure ≤ p.logMahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  have hq : p.comp (C c * X) ≠ 0 := by
    intro h
    apply hp
    have h' := congrArg (fun r => r.comp (C c⁻¹ * X)) h
    have hX : (C c * X).comp (C c⁻¹ * X) = (X : ℂ[X]) := by
      simp [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc]
    simpa [Polynomial.comp_assoc, hX] using h'
  have key : ∀ s : Multiset ℂ, (((s.map fun a => X - C a).prod).comp (C c * X)).mahlerMeasure ≤
      ((s.map fun a => X - C a).prod).mahlerMeasure := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, mul_comp, mahlerMeasure_mul]
      apply mul_le_mul _ ih (mahlerMeasure_nonneg _) (mahlerMeasure_nonneg _)
      have h1 : (X - C a).comp (C c * X) = C c * X + C (-a) := by
        simp [sub_eq_add_neg]
      rw [h1, mahlerMeasure_C_mul_X_add_C hc, mahlerMeasure_X_sub_C, norm_neg]
      exact max_le_max hc1 le_rfl
  rw [logMahlerMeasure_eq_log_MahlerMeasure, logMahlerMeasure_eq_log_MahlerMeasure]
  apply Real.log_le_log (mahlerMeasure_pos_of_ne_zero hq)
  have hs := (IsAlgClosed.splits p).eq_prod_roots
  rw [hs, mul_comp, C_comp, mahlerMeasure_mul, mahlerMeasure_mul]
  exact mul_le_mul_of_nonneg_left (key _) (mahlerMeasure_nonneg _)

theorem integral_log_eval_mul_le (p : ℂ[X]) {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    ∫ t in Set.Ioc (0 : ℝ) 1,
        Real.log ‖p.eval (c * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ ≤
      ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖p.eval (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ := by
  have h := integral_Ioc_log_eval_eq_logMahlerMeasure (p.comp (C c * X))
  simp only [eval_comp, eval_mul, eval_C, eval_X] at h
  rw [h, integral_Ioc_log_eval_eq_logMahlerMeasure]
  exact logMahlerMeasure_comp_C_mul_X_le p hc hc1

instance isProbabilityMeasure_restrict_Ioc_zero_one :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩

instance isProbabilityMeasure_torusProb_sphere (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (torusProb ι) := by
  unfold torusProb; infer_instance

theorem measurePreserving_update_torus {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) (torusProb ι) := by
  have hm : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) := measurable_update'
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  rw [hpre, Measure.prod_prod, torusProb, Measure.pi_pi,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (s := Finset.univ) (fun j => volume.restrict (Set.Ioc (0 : ℝ) 1) (s j))
      (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem integral_torus_eq_iter {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) {g : (ι → ℝ) → ℝ}
    (hg : Integrable g (torusProb ι)) :
    Integrable (fun x => ∫ t in Set.Ioc (0 : ℝ) 1, g (Function.update x i t)) (torusProb ι) ∧
    ∫ θ, g θ ∂(torusProb ι) =
      ∫ x, (∫ t in Set.Ioc (0 : ℝ) 1, g (Function.update x i t)) ∂(torusProb ι) := by
  have hU := measurePreserving_update_torus (ι := ι) i
  have hgU : Integrable (g ∘ fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (hU.integrable_comp hg.aestronglyMeasurable).mpr hg
  refine ⟨hgU.integral_prod_left, ?_⟩
  have h1 : ∫ θ, g θ ∂(torusProb ι) = ∫ p, g (Function.update p.1 i p.2)
      ∂((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    conv_lhs => rw [← hU.map_eq]
    exact integral_map hU.measurable.aemeasurable (by rw [hU.map_eq]; exact hg.aestronglyMeasurable)
  rw [h1]
  exact integral_prod _ hgU

end ReciprocityTheory.MultiplicativeHeights
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory

def scaledTorusMean {ι : Type*} [Fintype ι] (r : ι → ℂ) (f : MvPolynomial ι ℂ) : ℝ :=
  ∫ θ, Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖ ∂(torusProb ι)

theorem scaledTorusMean_one {ι : Type*} [Fintype ι] (f : MvPolynomial ι ℂ) :
    scaledTorusMean (fun _ => 1) f = torusMean f := by
  unfold scaledTorusMean torusMean
  simp only [one_mul]

theorem eval_update_eq_eval_aeval {ι : Type*} [DecidableEq ι] (w : ι → ℂ) (i : ι) (z : ℂ)
    (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval (Function.update w i z) f =
      (MvPolynomial.aeval (fun j => if j = i then (Polynomial.X : Polynomial ℂ)
        else Polynomial.C (w j)) f).eval z := by
  induction f using MvPolynomial.induction_on
  · simp
  · simp_all
  rename_i p j hp
  simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X, Polynomial.eval_mul, hp]
  congr 1
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Function.update_of_ne h]

theorem eval_bind₁_scale {ι : Type*} (r w : ι → ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval w
        (MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f) =
      MvPolynomial.eval (fun j => r j * w j) f := by
  induction f using MvPolynomial.induction_on
  · simp
  · simp_all
  · simp_all

private theorem bind1_C_mul_X_ne_zero_of_ne_zero {ι : Type} (r : ι → ℂ) (hr : ∀ j, r j ≠ 0)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f ≠ 0 := by
  intro h
  apply hf
  refine MvPolynomial.funext fun v => ?_
  have hv := eval_bind₁_scale r (fun j => v j / r j) f
  rw [h, map_zero] at hv
  have e : (fun j => r j * (v j / r j)) = v := by
    funext j
    first
      | exact mul_div_cancel₀ (v j) (hr j)
      | field_simp [hr j]
      | (rw [mul_comm]; exact div_mul_cancel₀ (v j) (hr j))
  rw [e] at hv
  rw [← hv, map_zero]

theorem integrable_scaled {ι : Type} [Fintype ι] (hBasic : TorusMeanBasicStatement)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ) (hr : ∀ j, r j ≠ 0) :
    Integrable (fun θ => Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖)
      (torusProb ι) := by
  have h := (hBasic ι).1 _ (bind1_C_mul_X_ne_zero_of_ne_zero r hr f hf)
  simpa only [eval_bind₁_scale] using h

theorem scaledTorusMean_le_update {ι : Type} [Fintype ι] [DecidableEq ι]
    (hBasic : TorusMeanBasicStatement) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ)
    (hr : ∀ j, r j ≠ 0) (i : ι) (hri : ‖r i‖ ≤ 1) :
    scaledTorusMean r f ≤ scaledTorusMean (Function.update r i 1) f := by
  have hr' : ∀ j, Function.update r i 1 j ≠ 0 := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · rw [Function.update_of_ne h]; exact hr j
  obtain ⟨hI1, hE1⟩ := integral_torus_eq_iter i (integrable_scaled hBasic f hf r hr)
  obtain ⟨hI2, hE2⟩ := integral_torus_eq_iter i (integrable_scaled hBasic f hf _ hr')
  unfold scaledTorusMean
  rw [hE1, hE2]
  refine integral_mono hI1 hI2 fun x => ?_
  set p : Polynomial ℂ := MvPolynomial.aeval (fun j => if j = i then (Polynomial.X : Polynomial ℂ)
        else Polynomial.C (r j * torusPoint x j)) f
  have key : ∀ (s : ι → ℂ), (∀ j, j ≠ i → s j = r j) → ∀ t : ℝ,
      MvPolynomial.eval (fun j => s j * torusPoint (Function.update x i t) j) f =
        p.eval (s i * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))) := by
    intro s hs t
    rw [← eval_update_eq_eval_aeval]
    refine congrArg (fun w => MvPolynomial.eval w f) (funext fun j => ?_)
    by_cases h : j = i
    · subst h; simp [torusPoint]
    · simp [Function.update_of_ne h, hs j h, torusPoint]
  have k1 := key r (fun _ _ => rfl)
  have k2 := key (Function.update r i 1) (fun j h => Function.update_of_ne h _ _)
  simp only [Function.update_self, one_mul] at k2
  beta_reduce
  simp only [k1, k2]
  exact integral_log_eval_mul_le p (hr i) hri

theorem scaledTorusMean_le_torusMean {ι : Type} [Fintype ι] [DecidableEq ι]
    (hBasic : TorusMeanBasicStatement) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ)
    (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, ‖r j‖ ≤ 1) :
    scaledTorusMean r f ≤ torusMean f := by
  classical
  have key : ∀ s : Finset ι, scaledTorusMean r f ≤
      scaledTorusMean (fun j => if j ∈ s then (1 : ℂ) else r j) f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      refine ih.trans ?_
      have hr' : ∀ j, (fun j => if j ∈ s then (1 : ℂ) else r j) j ≠ 0 := fun j => by
        dsimp only
        split_ifs <;> simp [hr j]
      have hra : ‖(fun j => if j ∈ s then (1 : ℂ) else r j) a‖ ≤ 1 := by
        simp [ha, hr1 a]
      have hle := scaledTorusMean_le_update hBasic f hf _ hr' a hra
      have e : Function.update (fun j => if j ∈ s then (1 : ℂ) else r j) a 1 =
          fun j => if j ∈ insert a s then (1 : ℂ) else r j := by
        funext j
        by_cases hj : j = a
        · subst hj
          simp
        · simp [Finset.mem_insert, hj, Function.update_of_ne hj]
      rw [e] at hle
      exact hle
  have hu := key Finset.univ
  simp only [Finset.mem_univ, if_true] at hu
  rwa [scaledTorusMean_one] at hu

end ReciprocityTheory.MultiplicativeHeights
end
end

section
namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory

theorem sphereTorus_holds (hInt : SphereLogIntegrableStatement) (hBasic : TorusMeanBasicStatement) :
    SphereLeTorusStatement := by
  intro B n a f hn hf hhom
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  haveI : IsProbabilityMeasure (blockSphereProb B n) := by
    unfold blockSphereProb; infer_instance
  haveI : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  haveI : IsProbabilityMeasure (torusProb (Fin B × Fin n)) := by
    unfold torusProb; infer_instance

  have hh : Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
      (blockSphereProb B n) := hInt B n a f hf hhom

  have hslice : ∀ θ : Fin B × Fin n → ℝ,
      Integrable (fun z => Real.log ‖MvPolynomial.eval
        (fun p => blockPoint z p * torusPoint θ p) f‖) (blockSphereProb B n) ∧
      ∫ z, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
        ∂(blockSphereProb B n) = blockSphereMean B n f ∧
      ∫ z, ‖Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖‖
        ∂(blockSphereProb B n) =
        ∫ z, ‖Real.log ‖MvPolynomial.eval (blockPoint z) f‖‖ ∂(blockSphereProb B n) := by
    intro θ
    have hmp := measurePreserving_blockRot (B := B) (n := n) θ
    have e : ∀ z, (fun p => blockPoint z p * torusPoint θ p) = blockPoint (blockRot θ z) := by
      intro z; rw [blockPoint_blockRot]
    simp only [e]
    refine ⟨?_, ?_, ?_⟩
    · have h1 : Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh
      exact h1.comp_measurable hmp.measurable
    · have hA : AEStronglyMeasurable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh.aestronglyMeasurable
      have h2 := integral_map hmp.measurable.aemeasurable hA
      rw [hmp.map_eq] at h2
      exact h2.symm
    · have hA : AEStronglyMeasurable (fun z => ‖Real.log ‖MvPolynomial.eval (blockPoint z) f‖‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh.norm.aestronglyMeasurable
      have h2 := integral_map hmp.measurable.aemeasurable hA
      rw [hmp.map_eq] at h2
      exact h2.symm

  have hcont : Continuous (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f) := by
    refine (MvPolynomial.continuous_eval f).comp (continuous_pi fun p => ?_)
    refine Continuous.mul ?_ ?_
    · unfold blockPoint spherePoint
      fun_prop
    · unfold torusPoint
      fun_prop
  have hgm : AEStronglyMeasurable (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      Real.log ‖MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f‖)
      ((blockSphereProb B n).prod (torusProb (Fin B × Fin n))) :=
    (Real.measurable_log.comp hcont.norm.measurable).aestronglyMeasurable
  have hgi : Integrable (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      Real.log ‖MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f‖)
      ((blockSphereProb B n).prod (torusProb (Fin B × Fin n))) := by
    rw [integrable_prod_iff' hgm]
    refine ⟨Filter.Eventually.of_forall fun θ => (hslice θ).1, ?_⟩
    simp only [fun θ => (hslice θ).2.2]
    exact integrable_const _

  have hae : ∀ᵐ z ∂(blockSphereProb B n), ∀ p, blockPoint z p ≠ 0 := by
    rw [ae_iff]
    simpa [not_forall] using blockSphereProb_coord_zero (B := B) (n := n)
  calc blockSphereMean B n f
      = ∫ θ, ∫ z, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
          ∂(blockSphereProb B n) ∂(torusProb (Fin B × Fin n)) := by
        simp only [fun θ => (hslice θ).2.1]
        simp
    _ = ∫ z, ∫ θ, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
          ∂(torusProb (Fin B × Fin n)) ∂(blockSphereProb B n) :=
        (integral_integral_swap hgi).symm
    _ = ∫ z, scaledTorusMean (blockPoint z) f ∂(blockSphereProb B n) := rfl
    _ ≤ ∫ _z, torusMean f ∂(blockSphereProb B n) := by
        refine integral_mono_ae hgi.integral_prod_left (integrable_const _) ?_
        filter_upwards [hae] with z hz
        exact scaledTorusMean_le_torusMean hBasic f hf (blockPoint z) hz (norm_blockPoint_le z)
    _ = torusMean f := by simp

end ReciprocityTheory.MultiplicativeHeights
end

section
namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem sphereLinLog : SphereLinLogStatement := sjCore_holds

theorem sj : SJStatement := sj_holds sphereLinLog

theorem sphereLogIntegrable : SphereLogIntegrableStatement := sphereLogIntegrable_holds sj

theorem gauss_height_additivity : HeightAdditiveStatement := gauss_height_add_of_sphere sphereLogIntegrable

theorem sphere_height_lower_bound : HeightLowerBoundStatement := heightLowerBound_of_sj_of_sphereLogIntegrable sj sphereLogIntegrable

theorem torusMeanBasic : TorusMeanBasicStatement := torusMean_holds.1

theorem torusCoeff : TorusCoeffStatement := torusMean_holds.2

theorem torusLex : TorusLexStatement := (torusLex_holds torusMeanBasic torusCoeff).1

theorem torus_l2_cauchy_inequality : TorusL2Cauchy := (torusLex_holds torusMeanBasic torusCoeff).2

theorem gram : GramStatement := gram_holds torusMeanBasic torusLex torus_l2_cauchy_inequality

theorem sphereLeTorus : SphereLeTorusStatement := sphereTorus_holds sphereLogIntegrable torusMeanBasic

end ReciprocityTheory.MultiplicativeHeights.Closed
end
