import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS

section
noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G.GI

open PositivityTheory.Rg.Sw

lemma abs_pow_exp (b : ℝ) (hb : 0 < b) (k : ℕ) :
    Integrable fun x : ℝ => |x| ^ k * Real.exp (-b * x ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ))
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  simp_rw [Real.rpow_natCast] at h
  refine h.norm.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) : (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ k ≤ (2 * b) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * b ^ k := mul_pow 2 b k
      _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
          have := pow_nonneg ha k
          gcongr; linarith
  · calc (a + b) ^ k ≤ (2 * a) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * a ^ k := mul_pow 2 a k
      _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
          have := pow_nonneg hb k
          gcongr; linarith

lemma cplx (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Integrable fun z : ℂ => ‖z‖ ^ k * Real.exp (-c * ‖z‖ ^ 2) := by
  have hP : Integrable (fun p : ℝ × ℝ => (2 : ℝ) ^ k * ((|p.1| ^ k * Real.exp (-c * p.1 ^ 2)) *
      Real.exp (-c * p.2 ^ 2) + Real.exp (-c * p.1 ^ 2) * (|p.2| ^ k * Real.exp (-c * p.2 ^ 2)))) := by
    refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · exact (abs_pow_exp c hc k).mul_prod (integrable_exp_neg_mul_sq hc)
    · exact (integrable_exp_neg_mul_sq hc).mul_prod (abs_pow_exp c hc k)
  have hC : Integrable (fun z : ℂ => (2 : ℝ) ^ k * ((|z.re| ^ k * Real.exp (-c * z.re ^ 2)) *
      Real.exp (-c * z.im ^ 2) + Real.exp (-c * z.re ^ 2) * (|z.im| ^ k * Real.exp (-c * z.im ^ 2)))) := by
    have := (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hP
    simpa [Function.comp_def, Complex.measurableEquivRealProd] using this
  refine hC.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have he : Real.exp (-c * ‖z‖ ^ 2) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2) := by
    rw [hz, ← Real.exp_add]; ring_nf
  have h1 : ‖z‖ ^ k ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k) :=
    (pow_le_pow_left₀ (norm_nonneg z) (Complex.norm_le_abs_re_add_abs_im z) k).trans
      (add_pow_le _ _ (abs_nonneg _) (abs_nonneg _) k)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), he]
  have e1 := Real.exp_pos (-c * z.re ^ 2)
  have e2 := Real.exp_pos (-c * z.im ^ 2)
  calc ‖z‖ ^ k * (Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2))
      ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k) * (Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)) := by
        gcongr
    _ = _ := by ring

lemma prodG (m n : ℕ) (c : ℝ) (hc : 0 < c) (D : Fin m → Fin n → ℕ) :
    Integrable fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, (‖x a i‖ ^ D a i * Real.exp (-c * ‖x a i‖ ^ 2)) := by
  refine Integrable.fintype_prod (f := fun a (r : Fin n → ℂ) => ∏ i, (‖r i‖ ^ D a i * Real.exp (-c * ‖r i‖ ^ 2)))
    (μ := fun _ => volume) (fun a => ?_)
  exact Integrable.fintype_prod (f := fun i (z : ℂ) => ‖z‖ ^ D a i * Real.exp (-c * ‖z‖ ^ 2))
    (μ := fun _ => volume) (fun i => cplx c hc _)

abbrev fx {m n : ℕ} (x : Fin m → Fin n → ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

lemma continuous_evX {m n : ℕ} (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  have : Continuous fun x : Fin m → Fin n → ℂ => fx x := by
    refine continuous_pi fun k => ?_
    by_cases h : k.2.2
    · simp only [fx, h, if_true]; fun_prop
    · simp only [fx, h, if_false, Bool.false_eq_true]; fun_prop
  exact (MvPolynomial.continuous_eval P).comp this

lemma continuous_gs {m n : ℕ} (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  unfold gs; fun_prop

lemma norm_gs {m n : ℕ} (c : ℝ) (x : Fin m → Fin n → ℂ) :
    ‖gs c x‖ = ∏ a, ∏ i, Real.exp (-c * ‖x a i‖ ^ 2) := by
  unfold gs
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  have : -(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) = ∑ a, ∑ i, (-c * ‖x a i‖ ^ 2) := by
    simp [Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
  rw [this, Real.exp_sum]
  exact Finset.prod_congr rfl fun a _ => Real.exp_sum _ _

lemma norm_mono {m n : ℕ} (d : (Fin m × Fin n × Bool) →₀ ℕ) (x : Fin m → Fin n → ℂ) :
    ‖evX (monomial d 1) x‖ = ∏ a, ∏ i, ‖x a i‖ ^ (d (a, i, false) + d (a, i, true)) := by
  unfold evX
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, norm_prod]
  simp_rw [norm_pow]
  rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
    simp [Finsupp.notMem_support_iff.mp hk])]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool]
  simp [pow_add, mul_comm]

theorem integP : IntegP := by
  intro m n c hc P
  have key : ∀ d : (Fin m × Fin n × Bool) →₀ ℕ,
      Integrable fun x : Fin m → Fin n → ℂ => evX (monomial d 1) x * gs c x := by
    intro d
    refine (prodG m n c hc (fun a i => d (a, i, false) + d (a, i, true))).mono'
      ((continuous_evX _).mul (continuous_gs c)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    rw [norm_mul, norm_mono, norm_gs, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_mul_distrib]
  have hP : (fun x => evX P x * gs c x) =
      fun x => ∑ d ∈ P.support, coeff d P * (evX (monomial d 1) x * gs c x) := by
    funext x
    simp only [evX]
    rw [MvPolynomial.eval_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, mul_assoc]
  rw [hP]
  exact integrable_finsetSum _ fun d _ => (key d).const_mul _

end PositivityTheory.Rg.Sw.WR.G.GI
end
end

section
noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

theorem integP : IntegP := GI.integP

lemma map_smul_volume {m n : ℕ} (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    Measure.map (fun x : Fin m → Fin n → ℂ => ζ • x) volume = volume := by
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) :=
    ((ζ • LinearMap.id : (Fin m → Fin n → ℂ) →ₗ[ℂ] (Fin m → Fin n → ℂ))).restrictScalars ℝ
  have hdet : LinearMap.det L = 1 := by
    simp only [L]
    rw [LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Algebra.norm_complex_apply, map_pow, Complex.normSq_eq_norm_sq, hζ]
    simp
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → Fin n → ℂ)))
    (f := L) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at this
  calc Measure.map (fun x : Fin m → Fin n → ℂ => ζ • x) volume = Measure.map (⇑L) volume := rfl
    _ = volume := by rw [this]; simp

lemma evX_smul_mono {m n : ℕ} (ζ : ℂ) (d : (Fin m × Fin n × Bool) →₀ ℕ) (hd : ∀ k, k.2.2 = true → d k = 0)
    (x : Fin m → Fin n → ℂ) :
    evX (monomial d 1) (ζ • x) = ζ ^ (d.sum fun _ e => e) * evX (monomial d 1) x := by
  unfold evX
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, one_mul, one_mul, Finsupp.prod, Finsupp.prod,
    Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk2 : k.2.2 = false := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hk) (hd k (by simpa using h))
  simp [hk2, mul_pow]

lemma gs_smul {m n : ℕ} (c : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) : gs c (ζ • x) = gs c x := by
  unfold gs
  simp [hζ]

lemma gramX_smul {m n : ℕ} (ε : Fin m → Bool) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) :
    gramX ε (ζ • x) = gramX ε x := by
  have h1 : (starRingEnd ℂ) ζ * ζ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ]; simp
  have key : ∀ u v : ℂ, (starRingEnd ℂ) (ζ * u) * (ζ * v) = (starRingEnd ℂ) u * v := by
    intro u v
    rw [map_mul]
    linear_combination ((starRingEnd ℂ) u * v) * h1
  ext _i _j
  simp only [gramX, evX, Qp, Qb, map_sub, map_sum, map_mul, MvPolynomial.eval_X]
  congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_ <;>
    simp only [Pi.smul_apply, smul_eq_mul, Bool.false_eq_true, if_true, if_false] <;>
    exact key _ _

lemma continuous_gramX {m n : ℕ} (ε : Fin m → Bool) : Continuous fun x : Fin m → Fin n → ℂ => gramX ε x :=
  continuous_pi fun i => continuous_pi fun j => GI.continuous_evX _

theorem rot : Rot := by
  intro m n ε c t hc b hb d hd hd0
  set N := d.sum fun _ e => e with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply hd0
    ext k
    have := (Finset.sum_eq_zero_iff.mp h) k
    by_cases hk : k ∈ d.support
    · simpa using this hk
    · simpa using hk
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  set ζ : ℂ := Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I) with hζdef
  have hζ : ‖ζ‖ = 1 := by rw [hζdef, Complex.norm_exp_ofReal_mul_I]
  have hζN : ζ ^ N = -1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    have : (N : ℂ) * (((Real.pi / N : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  let F : (Fin m → Fin n → ℂ) → ℂ := fun x =>
    evX (monomial d 1) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
  have hcont : Continuous F :=
    ((GI.continuous_evX _).mul (GI.continuous_gs c)).mul (Complex.continuous_exp.comp
      (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace)))
  have hcomp : (fun x => F (ζ • x)) = fun x => ζ ^ N * F x := by
    funext x
    simp only [F, evX_smul_mono ζ d hd, gs_smul c ζ hζ, gramX_smul ε ζ hζ]
    ring
  have hint : ∫ x, F (ζ • x) = ∫ x, F x := by
    rw [← integral_map (μ := volume) (φ := fun x : Fin m → Fin n → ℂ => ζ • x)
      (continuous_const_smul ζ).measurable.aemeasurable
      (by rw [map_smul_volume ζ hζ]; exact hcont.aestronglyMeasurable), map_smul_volume ζ hζ]
  have h2 : ∫ x, F x = -∫ x, F x := by
    conv_lhs => rw [← hint, hcomp, integral_const_mul, hζN, neg_one_mul]
  show ∫ x, F x = 0
  linear_combination (1 / 2 : ℂ) * h2

end PositivityTheory.Rg.Sw.WR.G
end
end
