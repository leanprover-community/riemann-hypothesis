import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import Mathlib

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

def monomialOfMultiindex {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) : ℂ :=
  ∏ i ∈ α.support, z i ^ α i

theorem fa1Mono_eq {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α z = ∏ i, z i ^ α i := by
  unfold monomialOfMultiindex
  exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]

theorem fa1Mono_continuous {g : ℕ} (α : Fin g →₀ ℕ) : Continuous (monomialOfMultiindex α) := by
  have h : monomialOfMultiindex α = fun z : EuclideanSpace ℂ (Fin g) => ∏ i, z i ^ α i := funext (fa1Mono_eq α)
  rw [h]
  exact continuous_finsetProd _ fun i _ => (PiLp.continuous_apply 2 _ i).pow _

theorem fa1Mono_norm_le {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) :
    ‖monomialOfMultiindex α z‖ ≤ ‖z‖ ^ (∑ i, α i) := by
  rw [fa1Mono_eq, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le z i) _

theorem fa1Mono_smul {g : ℕ} (α : Fin g →₀ ℕ) (r : ℝ) (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (r • z) = (r : ℂ) ^ (∑ i, α i) * monomialOfMultiindex α z := by
  rw [fa1Mono_eq, fa1Mono_eq, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [PiLp.smul_apply, Complex.real_smul, mul_pow]

theorem pow_mul_exp_neg_mul_sq_le (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-b * t ^ 2) ≤
      (1 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
  have hx : 0 ≤ b / 2 * t ^ 2 := by positivity
  have h1 : 1 ≤ Real.exp (b / 2 * t ^ 2) := Real.one_le_exp hx
  have h2 : (b / 2 * t ^ 2) ^ n / n.factorial ≤ Real.exp (b / 2 * t ^ 2) :=
    Real.pow_div_factorial_le_exp (x := b / 2 * t ^ 2) hx n
  have h3 : t ^ n ≤ 1 + t ^ (2 * n) := by
    rcases le_total t 1 with h | h
    · have : t ^ n ≤ 1 := pow_le_one₀ ht h
      linarith [pow_nonneg ht (2 * n)]
    · have : t ^ n ≤ t ^ (2 * n) := pow_le_pow_right₀ h (by omega)
      linarith
  have h4 : t ^ (2 * n) = (2 / b) ^ n * (b / 2 * t ^ 2) ^ n := by
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h5 : t ^ (2 * n) ≤ n.factorial * (2 / b) ^ n * Real.exp (b / 2 * t ^ 2) := by
    rw [h4]
    have h2' := (div_le_iff₀ hfac).mp h2
    have hb2 : 0 ≤ (2 / b) ^ n := by positivity
    nlinarith
  have hexp : Real.exp (b / 2 * t ^ 2) * Real.exp (-b * t ^ 2) = Real.exp (-(b / 2) * t ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h6 : t ^ n ≤ (1 + n.factorial * (2 / b) ^ n) * Real.exp (b / 2 * t ^ 2) := by
    nlinarith
  calc t ^ n * Real.exp (-b * t ^ 2)
      ≤ (1 + n.factorial * (2 / b) ^ n) * Real.exp (b / 2 * t ^ 2) * Real.exp (-b * t ^ 2) :=
        mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
    _ = (1 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
        rw [mul_assoc, hexp]

theorem integrable_exp_neg_mul_norm_sq_euclidean {g : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => Real.exp (-b * ‖z‖ ^ 2)) := by
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℂ (Fin g))
    (b := (b : ℂ)) (by simpa using hb) 0 0
  refine hc.norm.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero]
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

theorem integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean {g : ℕ} (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)) := by
  have hb2 : 0 < b / 2 := by positivity
  refine ((integrable_exp_neg_mul_norm_sq_euclidean (g := g) hb2).const_mul (1 + n.factorial * (2 / b) ^ n)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_mul_exp_neg_mul_sq_le n hb (norm_nonneg z)

theorem integrable_of_norm_le_gaussian {g : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : EuclideanSpace ℂ (Fin g) → E} (hf : Continuous f) (n : ℕ) {b C : ℝ} (hb : 0 < b)
    (h : ∀ z, ‖f z‖ ≤ C * (‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2))) : Integrable f := by
  exact ((integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean n hb).const_mul C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall h)

theorem integrable_monomial_mul_conj_gaussian {g : ℕ} (α β : Fin g →₀ ℕ) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) :=
    ((fa1Mono_continuous α).mul (Complex.continuous_conj.comp (fa1Mono_continuous β))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_norm.pow 2).neg))
  refine integrable_of_norm_le_gaussian hcont (∑ i, α i + ∑ i, β i) one_pos (C := 1) fun z => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), one_mul, neg_one_mul, pow_add]
  have h1 := fa1Mono_norm_le α z
  have h2 := fa1Mono_norm_le β z
  have he := (Real.exp_pos (-‖z‖ ^ 2)).le
  gcongr

theorem integrable_norm_monomial_sq_gaussian {g : ℕ} (α : Fin g →₀ ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2)) := by
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2) :=
    ((fa1Mono_continuous α).norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  refine integrable_of_norm_le_gaussian hcont (2 * ∑ i, α i) hb (C := 1) fun z => ?_
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_mul']
  have h1 := fa1Mono_norm_le α z
  gcongr

noncomputable def coordinateRotation {g : ℕ} (j : Fin g) (u : Circle) :
    EuclideanSpace ℂ (Fin g) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin g) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = j then rotation u else LinearIsometryEquiv.refl ℝ ℂ)

theorem fa1Rot_apply {g : ℕ} (j : Fin g) (u : Circle) (z : EuclideanSpace ℂ (Fin g)) (i : Fin g) :
    coordinateRotation j u z i = (if i = j then (u : ℂ) else 1) * z i := by
  simp only [coordinateRotation, LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs with h
  · simp [rotation_apply]
  · simp

theorem fa1Mono_rot {g : ℕ} (α : Fin g →₀ ℕ) (j : Fin g) (u : Circle)
    (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (coordinateRotation j u z) = (u : ℂ) ^ (α j) * monomialOfMultiindex α z := by
  rw [fa1Mono_eq, fa1Mono_eq]
  simp only [fa1Rot_apply, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem integral_monomial_mul_conj_gaussian_eq_zero {g : ℕ} {α β : Fin g →₀ ℕ} (h : α ≠ β) :
    ∫ z : EuclideanSpace ℂ (Fin g),
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
    by_contra hcon
    exact h (Finsupp.ext fun j => not_not.mp fun hne => hcon ⟨j, hne⟩)
  have hm : ((α j : ℝ) - β j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
  set u : Circle := Circle.exp (Real.pi / ((α j : ℝ) - β j)) with hu
  set F : EuclideanSpace ℂ (Fin g) → ℂ := fun z =>
    monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) with hF
  have hc : (u : ℂ) ^ (α j) * (starRingEnd ℂ) ((u : ℂ) ^ (β j)) = -1 := by
    rw [hu, Circle.coe_exp, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    have hm' : ((α j : ℂ) - β j) ≠ 0 := by exact_mod_cast hm
    have : (α j : ℂ) * (↑(Real.pi / ((α j : ℝ) - β j)) * Complex.I) +
        (β j : ℂ) * (starRingEnd ℂ) (↑(Real.pi / ((α j : ℝ) - β j)) * Complex.I) =
        Real.pi * Complex.I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_pi_mul_I]
  have hrot : ∀ z, F (coordinateRotation j u z) =
      ((u : ℂ) ^ (α j) * (starRingEnd ℂ) ((u : ℂ) ^ (β j))) * F z := by
    intro z
    simp only [hF, fa1Mono_rot, LinearIsometryEquiv.norm_map, map_mul]
    ring
  have hint : ∫ z, F (coordinateRotation j u z) = ∫ z, F z :=
    (coordinateRotation j u).measurePreserving.integral_comp (coordinateRotation j u).toHomeomorph.measurableEmbedding F
  simp_rw [hrot, hc] at hint
  rw [integral_const_mul] at hint
  linear_combination (-1 / 2 : ℂ) * hint

theorem integral_norm_monomial_sq_gaussian_pos {g : ℕ} (α : Fin g →₀ ℕ) :
    0 < ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  set f : EuclideanSpace ℂ (Fin g) → ℝ := fun z => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) with hf
  have hcont : Continuous f :=
    ((fa1Mono_continuous α).norm.pow 2).mul (Real.continuous_exp.comp (continuous_norm.pow 2).neg)
  have hint : Integrable f := by
    have := integrable_norm_monomial_sq_gaussian α one_pos
    simpa [neg_one_mul] using this
  have hnn : 0 ≤ f := fun z => by
    simp only [Pi.zero_apply, hf]
    positivity
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  let z₀ : EuclideanSpace ℂ (Fin g) := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have hz₁ : monomialOfMultiindex α z₀ = 1 := by
    rw [fa1Mono_eq]
    simp [z₀]
  have hz₀ : f z₀ ≠ 0 := by
    simp only [hf, hz₁, norm_one, one_pow, one_mul]
    exact (Real.exp_pos _).ne'
  exact hcont.isOpen_support.measure_pos _ ⟨z₀, hz₀⟩

theorem integral_norm_monomial_sq_gaussian_half {g : ℕ} (α : Fin g →₀ ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      2 ^ (g + ∑ i, α i) *
        ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpt : ∀ x : EuclideanSpace ℂ (Fin g),
      ‖monomialOfMultiindex α (Real.sqrt 2 • x)‖ ^ 2 * Real.exp (-(1 / 2) * ‖Real.sqrt 2 • x‖ ^ 2) =
        2 ^ (∑ i, α i) * (‖monomialOfMultiindex α x‖ ^ 2 * Real.exp (-‖x‖ ^ 2)) := by
    intro x
    rw [fa1Mono_smul, norm_mul, norm_pow, Complex.norm_real, norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_pow, mul_pow, ← pow_mul,
      mul_comm (∑ i, α i) 2, pow_mul, hs2, show -(1 / 2) * (2 * ‖x‖ ^ 2) = -‖x‖ ^ 2 by ring]
    ring
  have e1 : ∫ x : EuclideanSpace ℂ (Fin g),
      ‖monomialOfMultiindex α (Real.sqrt 2 • x)‖ ^ 2 * Real.exp (-(1 / 2) * ‖Real.sqrt 2 • x‖ ^ 2) =
        2 ^ (∑ i, α i) * ∫ x : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α x‖ ^ 2 * Real.exp (-‖x‖ ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hdim : |(Real.sqrt 2 ^ Module.finrank ℝ (EuclideanSpace ℂ (Fin g)))⁻¹| = ((2 : ℝ) ^ g)⁻¹ := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin, pow_mul, hs2,
      abs_of_pos (by positivity)]
  have e2 := MeasureTheory.Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℂ (Fin g)))
    (fun z => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) (Real.sqrt 2)
  beta_reduce at e2
  rw [hdim, smul_eq_mul, e1] at e2
  have h2g : (2 : ℝ) ^ g ≠ 0 := by positivity
  rw [pow_add, mul_assoc, e2, ← mul_assoc, mul_inv_cancel₀ h2g, one_mul]

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

noncomputable def fa1M {g : ℕ} (α : Fin g →₀ ℕ) : ℝ :=
  (Real.pi ^ g)⁻¹ * ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)

theorem monomialMass_pos {g : ℕ} (α : Fin g →₀ ℕ) : 0 < fa1M α :=
  mul_pos (by positivity) (integral_norm_monomial_sq_gaussian_pos α)

theorem integral_norm_monomial_sq_gaussian_eq {g : ℕ} (α : Fin g →₀ ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.pi ^ g * fa1M α := by
  unfold fa1M
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ Real.pi_ne_zero), one_mul]

noncomputable def fa1K {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) : ℝ :=
  ∑ α ∈ p.support, ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α

noncomputable def fa1N {g : ℕ} (p : MvPolynomial (Fin g) ℂ) : ℝ :=
  ∑ α ∈ p.support, ‖MvPolynomial.coeff α p‖ ^ 2 * fa1M α

theorem monomialKernel_nonneg {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    0 ≤ fa1K p z := by
  unfold fa1K
  exact Finset.sum_nonneg fun α _ => div_nonneg (by positivity) (monomialMass_pos α).le

theorem coeffNormSq_nonneg {g : ℕ} (p : MvPolynomial (Fin g) ℂ) : 0 ≤ fa1N p := by
  unfold fa1N
  exact Finset.sum_nonneg fun α _ => mul_nonneg (by positivity) (monomialMass_pos α).le

theorem eval_eq_sum_coeff_mul_monomial {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    MvPolynomial.eval (fun i => z i) p = ∑ α ∈ p.support, MvPolynomial.coeff α p * monomialOfMultiindex α z := by
  first
  | (simp [MvPolynomial.eval_eq', monomialOfMultiindex]; done)
  | (simp [MvPolynomial.eval_eq, monomialOfMultiindex, Finsupp.prod]; done)
  | (rw [MvPolynomial.eval_eq']; unfold monomialOfMultiindex; done)

theorem norm_eval_sq_le {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    ‖MvPolynomial.eval (fun i => z i) p‖ ^ 2 ≤ fa1N p * fa1K p z := by
  rw [eval_eq_sum_coeff_mul_monomial]
  have hM : ∀ α : Fin g →₀ ℕ, 0 < fa1M α := monomialMass_pos
  have h1 : ‖∑ α ∈ p.support, MvPolynomial.coeff α p * monomialOfMultiindex α z‖ ≤
      ∑ α ∈ p.support, (‖MvPolynomial.coeff α p‖ * Real.sqrt (fa1M α)) *
        (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α)) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun α _ => ?_))
    have hs : Real.sqrt (fa1M α) ≠ 0 := (Real.sqrt_pos.mpr (hM α)).ne'
    rw [norm_mul]
    first
    | (field_simp; done)
    | (field_simp; ring)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq p.support
    (fun α => ‖MvPolynomial.coeff α p‖ * Real.sqrt (fa1M α)) (fun α => ‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α))
  have h3 : ∀ α, (‖MvPolynomial.coeff α p‖ * Real.sqrt (fa1M α)) ^ 2 = ‖MvPolynomial.coeff α p‖ ^ 2 * fa1M α :=
    fun α => by rw [mul_pow, Real.sq_sqrt (hM α).le]
  have h4 : ∀ α, (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α)) ^ 2 = ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α :=
    fun α => by rw [div_pow, Real.sq_sqrt (hM α).le]
  simp only [h3, h4] at h2
  unfold fa1N fa1K
  calc _ ≤ (∑ α ∈ p.support, (‖MvPolynomial.coeff α p‖ * Real.sqrt (fa1M α)) *
        (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α))) ^ 2 := by gcongr
    _ ≤ _ := h2

theorem integrable_monomialKernel_mul_gaussian {g : ℕ} (p : MvPolynomial (Fin g) ℂ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K p z * Real.exp (-b * ‖z‖ ^ 2)) := by
  simp only [fa1K, Finset.sum_mul]
  refine integrable_finsetSum _ (fun α _ => ?_)
  have := (integrable_norm_monomial_sq_gaussian α hb).const_mul (fa1M α)⁻¹
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only; ring

theorem integral_monomialKernel_mul_gaussian {g : ℕ} (p : MvPolynomial (Fin g) ℂ) :
    ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-‖z‖ ^ 2) = Real.pi ^ g * p.support.card := by
  have hint : ∀ α : Fin g →₀ ℕ,
      MeasureTheory.Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    intro α
    by_contra h
    apply (monomialMass_pos α).ne'
    unfold fa1M
    rw [MeasureTheory.integral_undef h, mul_zero]
  unfold fa1K
  have hfun : (fun z : EuclideanSpace ℂ (Fin g) =>
      (∑ α ∈ p.support, ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α) * Real.exp (-‖z‖ ^ 2)) =
      fun z => ∑ α ∈ p.support, (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    funext z
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  rw [hfun, MeasureTheory.integral_finset_sum _ (fun α _ => (hint α).const_mul _)]
  have h2 : ∀ α ∈ p.support,
      ∫ z, (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) = Real.pi ^ g := by
    intro α _
    rw [MeasureTheory.integral_const_mul, integral_norm_monomial_sq_gaussian_eq, mul_comm (Real.pi ^ g), ← mul_assoc,
      inv_mul_cancel₀ (monomialMass_pos α).ne', one_mul]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
  ring

theorem integral_monomialKernel_mul_gaussian_half {g : ℕ} (p : MvPolynomial (Fin g) ℂ) :
    ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      Real.pi ^ g * ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) := by
  simp only [fa1K, Finset.sum_mul]
  rw [integral_finsetSum _ (fun α _ => ?_)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    have : ∀ z : EuclideanSpace ℂ (Fin g),
        ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
        (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := fun z => by ring
    simp only [this]
    rw [integral_const_mul, integral_norm_monomial_sq_gaussian_half, integral_norm_monomial_sq_gaussian_eq]
    have := (monomialMass_pos α).ne'
    field_simp
  · have := (integrable_norm_monomial_sq_gaussian α (b := 1 / 2) (by norm_num)).const_mul (fa1M α)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only; ring

theorem integral_mul_conj_gaussian_eq_coeffNormSq {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (F : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : ∀ z, F z = MvPolynomial.eval (fun i => z i) p) :
    (((Real.pi ^ g)⁻¹ : ℝ) : ℂ) * ∫ z, F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
      ((fa1N p : ℝ) : ℂ) := by
  have hexp : ∀ z, F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
      ∑ α ∈ p.support, ∑ β ∈ p.support,
        (MvPolynomial.coeff α p * (starRingEnd ℂ) (MvPolynomial.coeff β p)) *
          (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    intro z
    rw [hF, eval_eq_sum_coeff_mul_monomial, map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [map_mul]; ring
  simp only [hexp]
  have hint : ∀ α β : Fin g →₀ ℕ, Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      (MvPolynomial.coeff α p * (starRingEnd ℂ) (MvPolynomial.coeff β p)) *
        (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :=
    fun α β => (integrable_monomial_mul_conj_gaussian α β).const_mul _
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ => hint α β))]
  have hin : ∀ α ∈ p.support, ∫ z : EuclideanSpace ℂ (Fin g), ∑ β ∈ p.support,
      (MvPolynomial.coeff α p * (starRingEnd ℂ) (MvPolynomial.coeff β p)) *
        (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) =
      (((‖MvPolynomial.coeff α p‖ ^ 2 * (Real.pi ^ g * fa1M α)) : ℝ) : ℂ) := by
    intro α hα
    rw [integral_finsetSum _ (fun β _ => hint α β)]
    rw [Finset.sum_eq_single_of_mem α hα (fun β _ hβ => by
      rw [integral_const_mul, integral_monomial_mul_conj_gaussian_eq_zero (Ne.symm hβ), mul_zero])]
    rw [integral_const_mul]
    have h1 : ∀ z : EuclideanSpace ℂ (Fin g),
        monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex α z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
          ((‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
      intro z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    simp only [h1]
    rw [integral_complex_ofReal, integral_norm_monomial_sq_gaussian_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [Finset.sum_congr rfl hin, fa1N]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have : (Real.pi : ℂ) ^ g ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  field_simp

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

open Complex in

noncomputable def fockIP {g : ℕ} (F G : EuclideanSpace ℂ (Fin g) → ℂ) : ℂ :=
  ((Real.pi ^ g)⁻¹ : ℝ) * ∫ z, F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)

open Complex in

noncomputable def fockU {g : ℕ} (a : EuclideanSpace ℂ (Fin g)) (F : EuclideanSpace ℂ (Fin g) → ℂ) :
    EuclideanSpace ℂ (Fin g) → ℂ :=
  fun z => cexp ((∑ i, z i * (starRingEnd ℂ) (a i)) - (‖a‖ ^ 2 / 2 : ℝ)) * F (z - a)

def IsPolyLE {g : ℕ} (c : ℕ) (F : EuclideanSpace ℂ (Fin g) → ℂ) : Prop :=
  ∃ p : MvPolynomial (Fin g) ℂ, p.totalDegree ≤ c ∧ ∀ z, F z = MvPolynomial.eval (fun i => z i) p

theorem mul_le_sqrt_mul_sqrt_mul_avg {u v A B P Q t : ℝ} (hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ht : 0 < t) (huP : u ^ 2 ≤ A * P) (hvQ : v ^ 2 ≤ B * Q) :
    u * v ≤ Real.sqrt A * Real.sqrt B * ((t * P + Q / t) / 2) := by
  have hu : |u| ≤ Real.sqrt A * Real.sqrt P := by
    rw [← Real.sqrt_mul hA, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt huP
  have hv' : v ≤ Real.sqrt B * Real.sqrt Q := by
    rw [← Real.sqrt_mul hB, ← Real.sqrt_sq hv]
    exact Real.sqrt_le_sqrt hvQ
  have hPQ : Real.sqrt P * Real.sqrt Q ≤ (t * P + Q / t) / 2 := by
    have key : 2 * t * (Real.sqrt P * Real.sqrt Q) ≤ t ^ 2 * P + Q := by
      nlinarith [sq_nonneg (t * Real.sqrt P - Real.sqrt Q), Real.sq_sqrt hP, Real.sq_sqrt hQ]
    have e : (t * P + Q / t) / 2 = (t ^ 2 * P + Q) / (2 * t) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  calc u * v ≤ |u| * v := mul_le_mul_of_nonneg_right (le_abs_self u) hv
    _ ≤ (Real.sqrt A * Real.sqrt P) * (Real.sqrt B * Real.sqrt Q) :=
        mul_le_mul hu hv' hv (by positivity)
    _ = Real.sqrt A * Real.sqrt B * (Real.sqrt P * Real.sqrt Q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hPQ (by positivity)


theorem fockInner_self_re_eq_coeffNormSq {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (F : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : ∀ z, F z = MvPolynomial.eval (fun i => z i) p) : (fockIP F F).re = fa1N p := by
  unfold fockIP
  rw [integral_mul_conj_gaussian_eq_coeffNormSq p F hF, Complex.ofReal_re]

theorem card_support_le_and_sum_two_pow_le {g c : ℕ} (p : MvPolynomial (Fin g) ℂ) (hp : p.totalDegree ≤ c) :
    (p.support.card : ℝ) ≤ 2 ^ (g + c) ∧
      ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) ≤ 2 ^ (g + c) * 2 ^ (g + c) := by
  have hdeg : ∀ α ∈ p.support, ∑ i, α i ≤ c := fun α hα => by
    have := MvPolynomial.le_totalDegree hα
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact this.trans hp
  have h1 : (p.support.card : ℝ) ≤ ∑ α ∈ p.support, (2 : ℝ) ^ c * ∏ i, (1 / 2 : ℝ) ^ α i := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun α hα => ?_
    rw [Nat.cast_one, Finset.prod_pow_eq_pow_sum, one_div, inv_pow, ← div_eq_mul_inv,
      one_le_div (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (hdeg α hα)
  have hsub : p.support.image (fun α : Fin g →₀ ℕ => (α : Fin g → ℕ)) ⊆
      Fintype.piFinset (fun _ : Fin g => Finset.range (c + 1)) := by
    intro x hx
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hx
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)).trans
      (hdeg α hα)
  have h2 : ∑ α ∈ p.support, ∏ i, (1 / 2 : ℝ) ^ α i ≤
      ∏ _i : Fin g, ∑ k ∈ Finset.range (c + 1), (1 / 2 : ℝ) ^ k := by
    calc ∑ α ∈ p.support, ∏ i, (1 / 2 : ℝ) ^ α i
        = ∑ x ∈ p.support.image (fun α : Fin g →₀ ℕ => (α : Fin g → ℕ)),
            ∏ i, (1 / 2 : ℝ) ^ x i :=
          (Finset.sum_image (f := fun x : Fin g → ℕ => ∏ i, (1 / 2 : ℝ) ^ x i) (s := p.support)
            (g := fun α : Fin g →₀ ℕ => (α : Fin g → ℕ))
            (fun a _ b _ h => Finsupp.ext (congrFun h))).symm
      _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : Fin g => Finset.range (c + 1)),
            ∏ i, (1 / 2 : ℝ) ^ x i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = _ := (Finset.prod_univ_sum _ _).symm
  have hcard : (p.support.card : ℝ) ≤ 2 ^ (g + c) := by
    calc (p.support.card : ℝ) ≤ ∑ α ∈ p.support, (2 : ℝ) ^ c * ∏ i, (1 / 2 : ℝ) ^ α i := h1
      _ = 2 ^ c * ∑ α ∈ p.support, ∏ i, (1 / 2 : ℝ) ^ α i := by rw [Finset.mul_sum]
      _ ≤ 2 ^ c * ∏ _i : Fin g, ∑ k ∈ Finset.range (c + 1), (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 2 ^ c * ∏ _i : Fin g, (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => by positivity)
            (fun _ _ => sum_geometric_two_le _)) (by positivity)
      _ = 2 ^ (g + c) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_add]
          ring
  refine ⟨hcard, ?_⟩
  calc ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) ≤ ∑ α ∈ p.support, (2 : ℝ) ^ (g + c) :=
        Finset.sum_le_sum fun α hα => pow_le_pow_right₀ (by norm_num) (by have := hdeg α hα; omega)
    _ = p.support.card * 2 ^ (g + c) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (g + c) * 2 ^ (g + c) := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem fockU_coeff_le {g c : ℕ} (a : EuclideanSpace ℂ (Fin g)) (F G : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : IsPolyLE c F) (hG : IsPolyLE c G) :
    ‖fockIP (fockU a F) G‖ ≤ 2 ^ (1 + 3 * ((g : ℝ) + c) / 2) * Real.exp (-‖a‖ ^ 2 / 16) *
      Real.sqrt (fockIP F F).re * Real.sqrt (fockIP G G).re := by
  obtain ⟨p, hpc, hp⟩ := hF
  obtain ⟨q, hqc, hq⟩ := hG
  rw [fockInner_self_re_eq_coeffNormSq p F hp, fockInner_self_re_eq_coeffNormSq q G hq]
  have hNF := coeffNormSq_nonneg p
  have hNG := coeffNormSq_nonneg q

  have hre : ∀ z : EuclideanSpace ℂ (Fin g), (∑ i, z i * (starRingEnd ℂ) (a i)).re =
      (‖z‖ ^ 2 + ‖a‖ ^ 2 - ‖z - a‖ ^ 2) / 2 := by
    intro z
    have h1 : (∑ i, z i * (starRingEnd ℂ) (a i)) = inner ℂ a z := by
      simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    have h2 := norm_sub_sq (𝕜 := ℂ) z a
    have h3 := inner_re_symm (𝕜 := ℂ) z a
    simp only [RCLike.re_to_complex] at h2 h3
    rw [h1]
    linarith
  have hI : ∀ z : EuclideanSpace ℂ (Fin g),
      ‖fockU a F z * (starRingEnd ℂ) (G z) * ((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ =
        ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) := by
    intro z
    simp only [fockU, norm_mul, Complex.norm_exp, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Complex.sub_re, Complex.ofReal_re, hre z]
    have e : Real.exp ((‖z‖ ^ 2 + ‖a‖ ^ 2 - ‖z - a‖ ^ 2) / 2 - ‖a‖ ^ 2 / 2) *
        Real.exp (-‖z‖ ^ 2) = Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← e]
    ring
  have hmain : ∀ M : EuclideanSpace ℂ (Fin g) → ℝ, Integrable M →
      (∀ z, ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) ≤ M z) →
      ‖fockIP (fockU a F) G‖ ≤ (Real.pi ^ g)⁻¹ * ∫ z, M z := by
    intro M hM hle
    unfold fockIP
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hM
      (Filter.Eventually.of_forall fun z => (hI z).le.trans (hle z))) (by positivity)
  have hexp2 : ∀ x : ℝ, Real.exp (x / 2) ^ 2 = Real.exp x := by
    intro x
    rw [sq, ← Real.exp_add]
    ring_nf
  have hs : 0 ≤ Real.sqrt (fa1N p) * Real.sqrt (fa1N q) := by positivity
  obtain ⟨hcp, hsp⟩ := card_support_le_and_sum_two_pow_le p hpc
  obtain ⟨hcq, hsq⟩ := card_support_le_and_sum_two_pow_le q hqc
  have hi1p : Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K p z * Real.exp (-‖z‖ ^ 2)) := by
    simpa using integrable_monomialKernel_mul_gaussian p (b := 1) one_pos
  have hi1q : Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K q z * Real.exp (-‖z‖ ^ 2)) := by
    simpa using integrable_monomialKernel_mul_gaussian q (b := 1) one_pos
  have hi2p : Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := integrable_monomialKernel_mul_gaussian p (by norm_num)
  have hi2q : Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      fa1K q z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := integrable_monomialKernel_mul_gaussian q (by norm_num)

  have hB1 : ‖fockIP (fockU a F) G‖ ≤
      Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * 2 ^ (g + c) := by
    have hM : Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
        Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * ((fa1K p (z - a) * Real.exp (-‖z - a‖ ^ 2) +
          fa1K q z * Real.exp (-‖z‖ ^ 2)) / 2)) :=
      (((hi1p.comp_sub_right a).add hi1q).div_const 2).const_mul _
    refine (hmain _ hM (fun z => ?_)).trans ?_
    · have hu : (‖F (z - a)‖ * Real.exp (-‖z - a‖ ^ 2 / 2)) ^ 2 ≤
          fa1N p * (fa1K p (z - a) * Real.exp (-‖z - a‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hp]; exact norm_eval_sq_le p (z - a)) (Real.exp_pos _).le
      have hv : (‖G z‖ * Real.exp (-‖z‖ ^ 2 / 2)) ^ 2 ≤
          fa1N q * (fa1K q z * Real.exp (-‖z‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hq]; exact norm_eval_sq_le q z) (Real.exp_pos _).le
      have hab := mul_le_sqrt_mul_sqrt_mul_avg (by positivity) hNF hNG
        (mul_nonneg (monomialKernel_nonneg p _) (Real.exp_pos _).le)
        (mul_nonneg (monomialKernel_nonneg q _) (Real.exp_pos _).le) one_pos hu hv
      calc ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2)
          = (‖F (z - a)‖ * Real.exp (-‖z - a‖ ^ 2 / 2)) * (‖G z‖ * Real.exp (-‖z‖ ^ 2 / 2)) := by
            rw [show -‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2 = -‖z - a‖ ^ 2 / 2 + -‖z‖ ^ 2 / 2 by ring,
              Real.exp_add]
            ring
        _ ≤ _ := hab
        _ = _ := by ring
    · have hT : ∫ z : EuclideanSpace ℂ (Fin g), fa1K p (z - a) * Real.exp (-‖z - a‖ ^ 2) =
          ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-‖z‖ ^ 2) :=
        integral_sub_right_eq_self (fun z => fa1K p z * Real.exp (-‖z‖ ^ 2)) a
      rw [integral_const_mul, integral_div, integral_add (hi1p.comp_sub_right a) hi1q, hT,
        integral_monomialKernel_mul_gaussian, integral_monomialKernel_mul_gaussian]
      have hpi : 0 < Real.pi ^ g := by positivity
      have e : (Real.pi ^ g)⁻¹ * (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
          ((Real.pi ^ g * p.support.card + Real.pi ^ g * q.support.card) / 2)) =
          Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * ((p.support.card + q.support.card) / 2) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) hs

  have hB2 : ‖fockIP (fockU a F) G‖ ≤ Real.exp (-‖a‖ ^ 2 / 8) *
      (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * (2 ^ (g + c) * 2 ^ (g + c))) := by
    have hM : Integrable (fun z : EuclideanSpace ℂ (Fin g) => Real.exp (-‖a‖ ^ 2 / 8) *
        (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
          ((fa1K p (z - a) * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2) +
            fa1K q z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) / 2))) :=
      ((((hi2p.comp_sub_right a).add hi2q).div_const 2).const_mul _).const_mul _
    refine (hmain _ hM (fun z => ?_)).trans ?_
    · have hu : (‖F (z - a)‖ * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2)) ^ 2 ≤
          fa1N p * (fa1K p (z - a) * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hp]; exact norm_eval_sq_le p (z - a)) (Real.exp_pos _).le
      have hv : (‖G z‖ * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2)) ^ 2 ≤
          fa1N q * (fa1K q z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hq]; exact norm_eval_sq_le q z) (Real.exp_pos _).le
      have hab := mul_le_sqrt_mul_sqrt_mul_avg (by positivity) hNF hNG
        (mul_nonneg (monomialKernel_nonneg p _) (Real.exp_pos _).le)
        (mul_nonneg (monomialKernel_nonneg q _) (Real.exp_pos _).le) one_pos hu hv
      have hpar : ‖a‖ ^ 2 ≤ 2 * (‖z - a‖ ^ 2 + ‖z‖ ^ 2) := by
        have h := norm_sub_le z (z - a)
        rw [sub_sub_cancel] at h
        nlinarith [norm_nonneg a, norm_nonneg z, norm_nonneg (z - a), sq_nonneg (‖z‖ - ‖z - a‖)]
      have hexpb : Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) ≤ Real.exp (-‖a‖ ^ 2 / 8) *
          (Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2) * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith)
      calc ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2)
          ≤ ‖F (z - a)‖ * ‖G z‖ * (Real.exp (-‖a‖ ^ 2 / 8) *
            (Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2) * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2))) :=
            mul_le_mul_of_nonneg_left hexpb (by positivity)
        _ = Real.exp (-‖a‖ ^ 2 / 8) * ((‖F (z - a)‖ * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2)) *
            (‖G z‖ * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hab (Real.exp_pos _).le
        _ = _ := by ring
    · have hT : ∫ z : EuclideanSpace ℂ (Fin g), fa1K p (z - a) * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2) =
          ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2) :=
        integral_sub_right_eq_self (fun z => fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) a
      rw [integral_const_mul, integral_const_mul, integral_div,
        integral_add (hi2p.comp_sub_right a) hi2q, hT, integral_monomialKernel_mul_gaussian_half, integral_monomialKernel_mul_gaussian_half]
      have hpi : 0 < Real.pi ^ g := by positivity
      have e : (Real.pi ^ g)⁻¹ * (Real.exp (-‖a‖ ^ 2 / 8) * (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
          ((Real.pi ^ g * ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) +
            Real.pi ^ g * ∑ α ∈ q.support, (2 : ℝ) ^ (g + ∑ i, α i)) / 2))) =
          Real.exp (-‖a‖ ^ 2 / 8) * (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
            ((∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) +
              ∑ α ∈ q.support, (2 : ℝ) ^ (g + ∑ i, α i)) / 2)) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hs)
        (Real.exp_pos _).le

  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (2 : ℝ) ^ (((g : ℝ) + c) / 2) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by
    rw [hy]
    positivity
  have hyT : y ^ 2 = (2 : ℝ) ^ (g + c) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show ((g : ℝ) + c) / 2 * ((2 : ℕ) : ℝ) = ((g + c : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hR : (2 : ℝ) ^ (1 + 3 * ((g : ℝ) + c) / 2) = 2 * y ^ 3 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_add (by norm_num),
      Real.rpow_one, show 3 * ((g : ℝ) + c) / 2 = ((g : ℝ) + c) / 2 * ((3 : ℕ) : ℝ) by push_cast; ring]
  have hE : Real.exp (-‖a‖ ^ 2 / 16) ^ 2 = Real.exp (-‖a‖ ^ 2 / 8) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hX0 := norm_nonneg (fockIP (fockU a F) G)
  rw [hR]
  have key : ‖fockIP (fockU a F) G‖ ^ 2 ≤ (2 * y ^ 3 * Real.exp (-‖a‖ ^ 2 / 16) *
      Real.sqrt (fa1N p) * Real.sqrt (fa1N q)) ^ 2 := by
    have h12 := mul_le_mul hB1 hB2 hX0 (by positivity)
    have e1 : Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * 2 ^ (g + c) * (Real.exp (-‖a‖ ^ 2 / 8) *
        (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * (2 ^ (g + c) * 2 ^ (g + c)))) =
        Real.sqrt (fa1N p) ^ 2 * Real.sqrt (fa1N q) ^ 2 * y ^ 6 * Real.exp (-‖a‖ ^ 2 / 8) := by
      rw [← hyT]
      ring
    have e2 : (2 * y ^ 3 * Real.exp (-‖a‖ ^ 2 / 16) * Real.sqrt (fa1N p) * Real.sqrt (fa1N q)) ^ 2 =
        4 * (Real.sqrt (fa1N p) ^ 2 * Real.sqrt (fa1N q) ^ 2 * y ^ 6 * Real.exp (-‖a‖ ^ 2 / 8)) := by
      rw [← hE]
      ring
    rw [sq, e2]
    rw [e1] at h12
    have : 0 ≤ Real.sqrt (fa1N p) ^ 2 * Real.sqrt (fa1N q) ^ 2 * y ^ 6 * Real.exp (-‖a‖ ^ 2 / 8) := by
      positivity
    linarith
  exact (pow_le_pow_iff_left₀ hX0 (by positivity) two_ne_zero).1 key

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

def paW (q : ℕ) (v : EuclideanSpace ℂ ι) : ℝ := Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)

def paIP (q : ℕ) (F G : EuclideanSpace ℂ ι → ℂ) : ℂ :=
  ∫ v, F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ)

def paN (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : ℝ := Real.sqrt (paIP q F F).re

def paPF (p : MvPolynomial ι ℂ) : EuclideanSpace ℂ ι → ℂ := fun v => MvPolynomial.eval (fun i => v i) p

def paMono (α : ι →₀ ℕ) : EuclideanSpace ℂ ι → ℂ := paPF (MvPolynomial.monomial α 1)

def paS (c : ℕ) : Finset (ι →₀ ℕ) :=
  ((Fintype.piFinset fun _ : ι => Finset.range (c + 1)).map
    (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)).symm.toEmbedding).filter (fun α => α.degree ≤ c)

def paPoly (c : ℕ) : Submodule ℂ (EuclideanSpace ℂ ι → ℂ) :=
  Submodule.span ℂ (paMono '' ((paS (ι := ι) c : Finset (ι →₀ ℕ)) : Set (ι →₀ ℕ)))

def paU (q : ℕ) (a : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun v => cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)

def paD (α : ι →₀ ℕ) (H : EuclideanSpace ℂ ι → ℂ) : ℂ :=
  polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) H 0

def paFact (α : ι →₀ ℕ) : ℕ := ∏ i, (α i).factorial

def paJet (c : ℕ) (H : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  ∑ α ∈ paS c, (paD α H / paFact α) • paMono α

theorem mem_paS {c : ℕ} {α : ι →₀ ℕ} : α ∈ paS c ↔ α.degree ≤ c := by
  simp only [paS, Finset.mem_filter, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_range,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨⟨α, fun i => ?_, by simp⟩, h⟩
    have := Finsupp.le_degree i α
    omega

theorem paS_deg {c : ℕ} {α : ι →₀ ℕ} (h : α ∈ paS c) : α.degree ≤ c := mem_paS.1 h

theorem sum_eq_degree (s : ι →₀ ℕ) : (s.sum fun _ e => e) = s.degree := by
  rw [Finsupp.degree_apply]; rfl

theorem paPF_eq_sum (p : MvPolynomial ι ℂ) :
    paPF p = ∑ m ∈ p.support, p.coeff m • paMono m := by
  funext v
  conv_lhs => rw [paPF, p.as_sum, map_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, paMono, paPF, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun m _ => by ring

theorem paMono_mem {c : ℕ} {α : ι →₀ ℕ} (h : α ∈ paS c) : paMono α ∈ paPoly c :=
  Submodule.subset_span ⟨α, h, rfl⟩

theorem paPF_mem_paPoly {c : ℕ} {p : MvPolynomial ι ℂ} (hp : p.totalDegree ≤ c) :
    paPF p ∈ paPoly c := by
  rw [paPF_eq_sum]
  refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (paMono_mem (mem_paS.2 ?_))
  have := MvPolynomial.le_totalDegree hm
  rw [sum_eq_degree] at this
  omega

theorem paPF_add (p r : MvPolynomial ι ℂ) : paPF (p + r) = paPF p + paPF r := by
  funext v; simp [paPF]

theorem paPF_smul (a : ℂ) (p : MvPolynomial ι ℂ) : paPF (MvPolynomial.C a * p) = a • paPF p := by
  funext v; simp [paPF]

theorem paPoly_exists {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ p : MvPolynomial ι ℂ, p.totalDegree ≤ c ∧ F = paPF p := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    refine ⟨MvPolynomial.monomial α 1, ?_, rfl⟩
    calc (MvPolynomial.monomial α (1 : ℂ)).totalDegree ≤ α.sum (fun _ => id) :=
          MvPolynomial.totalDegree_monomial_le _ _
      _ = α.degree := sum_eq_degree α
      _ ≤ c := paS_deg hα
  | zero => exact ⟨0, by simp, by funext v; simp [paPF]⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨r, hr, rfl⟩ := hy
    exact ⟨p + r, (MvPolynomial.totalDegree_add _ _).trans (max_le hp hr), (paPF_add p r).symm⟩
  | smul a x _ hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨MvPolynomial.C a * p, ?_, (paPF_smul a p).symm⟩
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simpa using hp

theorem paJet_mem (c : ℕ) (H : EuclideanSpace ℂ ι → ℂ) : paJet c H ∈ paPoly c :=
  Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ (paMono_mem hα)

theorem paPoly_fd (c : ℕ) : FiniteDimensional ℂ (paPoly (ι := ι) c) :=
  FiniteDimensional.span_of_finite ℂ ((paS c).finite_toSet.image _)

theorem paPF_continuous (p : MvPolynomial ι ℂ) : Continuous (paPF p) := by
  unfold paPF
  exact (MvPolynomial.continuous_eval p).comp (by fun_prop)

theorem paPoly_continuous {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) : Continuous F := by
  obtain ⟨p, -, rfl⟩ := paPoly_exists hF
  exact paPF_continuous p

theorem paMono_norm_le (α : ι →₀ ℕ) (v : EuclideanSpace ℂ ι) : ‖paMono α v‖ ≤ ‖v‖ ^ α.degree := by
  simp only [paMono, paPF, MvPolynomial.eval_monomial, one_mul, Finsupp.prod, norm_prod, norm_pow]
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun i _ => by positivity)
    (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le v i) _)

theorem paPoly_growth {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖F v‖ ≤ C * (1 + ‖v‖) ^ c := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    refine ⟨1, zero_le_one, fun v => ?_⟩
    rw [one_mul]
    refine (paMono_norm_le α v).trans ?_
    calc ‖v‖ ^ α.degree ≤ (1 + ‖v‖) ^ α.degree := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
      _ ≤ (1 + ‖v‖) ^ c := pow_le_pow_right₀ (by linarith [norm_nonneg v]) (paS_deg hα)
  | zero => exact ⟨0, le_rfl, fun v => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C1, h1, hC1⟩ := hx
    obtain ⟨C2, h2, hC2⟩ := hy
    exact ⟨C1 + C2, by positivity, fun v => (norm_add_le _ _).trans (by
      have := hC1 v; have := hC2 v; nlinarith)⟩
  | smul a x _ hx =>
    obtain ⟨C, h, hC⟩ := hx
    refine ⟨‖a‖ * C, by positivity, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC v) (norm_nonneg _)

theorem paW_pos (q : ℕ) (v : EuclideanSpace ℂ ι) : 0 < paW q v := Real.exp_pos _

theorem paW_continuous (q : ℕ) : Continuous (paW (ι := ι) q) := by
  unfold paW; fun_prop

theorem pa_gauss_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : EuclideanSpace ℂ ι => Real.exp (-b * ‖v‖ ^ 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℂ ι) (b := (b : ℂ)) (by simpa using hb) 0 0).norm
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem pa_one_add_pow_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + t ^ n) := by
        have : 0 ≤ t ^ n := pow_nonneg ht n
        nlinarith [pow_pos (two_pos (α := ℝ)) n]
  · calc (1 + t) ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * t ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (1 + t ^ n) := by nlinarith [pow_pos (two_pos (α := ℝ)) n]

theorem pa_pow_gauss_le (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    (1 + t) ^ n * Real.exp (-b * t ^ 2) ≤
      2 ^ n * (2 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
  have h1 := pow_mul_exp_neg_mul_sq_le n hb ht
  have h2 : Real.exp (-b * t ^ 2) ≤ Real.exp (-(b / 2) * t ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
  have h3 := pa_one_add_pow_le n ht
  have hE : 0 ≤ Real.exp (-b * t ^ 2) := (Real.exp_pos _).le
  calc (1 + t) ^ n * Real.exp (-b * t ^ 2) ≤ 2 ^ n * (1 + t ^ n) * Real.exp (-b * t ^ 2) :=
        mul_le_mul_of_nonneg_right h3 hE
    _ = 2 ^ n * (Real.exp (-b * t ^ 2) + t ^ n * Real.exp (-b * t ^ 2)) := by ring
    _ ≤ 2 ^ n * (Real.exp (-(b / 2) * t ^ 2) + (1 + n.factorial * (2 / b) ^ n) *
        Real.exp (-(b / 2) * t ^ 2)) := by gcongr
    _ = _ := by ring

theorem pa_integrable_of_le {E' : Type*} [NormedAddCommGroup E'] {f : EuclideanSpace ℂ ι → E'}
    (hf : Continuous f) (n : ℕ) {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (h : ∀ v, ‖f v‖ ≤ C * ((1 + ‖v‖) ^ n * Real.exp (-b * ‖v‖ ^ 2))) : Integrable f := by
  refine ((pa_gauss_integrable (ι := ι) (half_pos hb)).const_mul
    (C * (2 ^ n * (2 + n.factorial * (2 / b) ^ n)))).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  refine (h v).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (pa_pow_gauss_le n hb (norm_nonneg v)) hC

theorem pa_bound2 {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖F v‖ * ‖G v‖ * paW q v ≤
      C * ((1 + ‖v‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)) := by
  obtain ⟨C1, h1, hC1⟩ := paPoly_growth hF
  obtain ⟨C2, h2, hC2⟩ := paPoly_growth hG
  refine ⟨C1 * C2, by positivity, fun v => ?_⟩
  have hw := (paW_pos q v).le
  have e : (1 + ‖v‖) ^ (2 * c) = (1 + ‖v‖) ^ c * (1 + ‖v‖) ^ c := by rw [two_mul, pow_add]
  rw [e, paW]
  have := mul_le_mul (hC1 v) (hC2 v) (norm_nonneg _) (by positivity)
  have hw' := Real.exp_pos (-(q * Real.pi) * ‖v‖ ^ 2)
  nlinarith

theorem gaussianInner_integrable {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) :
    Integrable (fun v => F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ)) := by
  obtain ⟨C, hC, h⟩ := pa_bound2 hq hF hG
  have hb : 0 < (q : ℝ) * Real.pi := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    positivity
  refine pa_integrable_of_le (by
    have := paPoly_continuous hF; have := paPoly_continuous hG; have := paW_continuous (ι := ι) q
    fun_prop) (2 * c) hb hC (fun v => ?_)
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (paW_pos q v).le]
  simpa [neg_mul] using h v

theorem gaussianInner_integrable_norm {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) : Integrable (fun v => ‖F v‖ * ‖G v‖ * paW q v) := by
  have := (gaussianInner_integrable hq hF hG).norm
  refine this.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (paW_pos q v).le]

theorem gaussianInner_add_left {q c : ℕ} (hq : 1 ≤ q) {F G H : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) (hH : H ∈ paPoly c) : paIP q (F + G) H = paIP q F H + paIP q G H := by
  unfold paIP
  rw [← integral_add (gaussianInner_integrable hq hF hH) (gaussianInner_integrable hq hG hH)]
  congr 1; funext v; simp only [Pi.add_apply]; ring

theorem gaussianInner_smul_left (q : ℕ) (a : ℂ) (F G : EuclideanSpace ℂ ι → ℂ) :
    paIP q (a • F) G = a * paIP q F G := by
  unfold paIP
  rw [← integral_const_mul]
  congr 1; funext v; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem gaussianInner_conj_symm (q : ℕ) (F G : EuclideanSpace ℂ ι → ℂ) :
    paIP q G F = (starRingEnd ℂ) (paIP q F G) := by
  unfold paIP
  rw [← integral_conj]
  congr 1; funext v
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

theorem gaussianInner_self (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) :
    paIP q F F = ((∫ v, ‖F v‖ ^ 2 * paW q v : ℝ) : ℂ) := by
  unfold paIP
  rw [← integral_complex_ofReal]
  congr 1; funext v
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

theorem gaussianInner_self_re (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) :
    paIP q F F = ((paIP q F F).re : ℂ) ∧ 0 ≤ (paIP q F F).re := by
  rw [gaussianInner_self, Complex.ofReal_re]
  exact ⟨rfl, integral_nonneg fun v => by have := paW_pos q v; positivity⟩

theorem pa_cs_real {X A B : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → 2 * t * X ≤ t ^ 2 * A + B) : X ≤ Real.sqrt A * Real.sqrt B := by
  rw [← Real.sqrt_mul hA]
  rcases hX.lt_or_eq with hX | hX
  · rcases hA.lt_or_eq with hA' | hA'
    · have := h (X / A) (div_pos hX hA')
      have e : (X / A) ^ 2 * A = X * (X / A) := by field_simp
      rw [e] at this
      have h2 : X * X ≤ A * B := by
        have : X * (X / A) ≤ B := by nlinarith
        rw [mul_div_assoc', div_le_iff₀ hA'] at this
        linarith
      exact Real.le_sqrt_of_sq_le (by nlinarith)
    · exfalso
      have := h ((B + 1) / X) (by positivity)
      rw [← hA'] at this
      have e : 2 * ((B + 1) / X) * X = 2 * (B + 1) := by field_simp
      rw [e] at this
      linarith
  · rw [← hX]; exact Real.sqrt_nonneg _

theorem norm_gaussianInner_le {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) : ‖paIP q F G‖ ≤ paN q F * paN q G := by
  have hA : (paIP q F F).re = ∫ v, ‖F v‖ * ‖F v‖ * paW q v := by
    rw [gaussianInner_self, Complex.ofReal_re]; congr 1; funext v; ring
  have hB : (paIP q G G).re = ∫ v, ‖G v‖ * ‖G v‖ * paW q v := by
    rw [gaussianInner_self, Complex.ofReal_re]; congr 1; funext v; ring
  have h1 : ‖paIP q F G‖ ≤ ∫ v, ‖F v‖ * ‖G v‖ * paW q v := by
    unfold paIP
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext v
    simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (paW_pos q v).le]
  refine h1.trans ?_
  unfold paN
  rw [hA, hB]
  refine pa_cs_real (integral_nonneg fun v => by have := paW_pos q v; positivity)
    (integral_nonneg fun v => by have := paW_pos q v; positivity)
    (integral_nonneg fun v => by have := paW_pos q v; positivity) fun t ht => ?_
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((gaussianInner_integrable_norm hq hF hF).const_mul _) (gaussianInner_integrable_norm hq hG hG)]
  refine integral_mono ((gaussianInner_integrable_norm hq hF hG).const_mul _)
    (((gaussianInner_integrable_norm hq hF hF).const_mul _).add (gaussianInner_integrable_norm hq hG hG)) fun v => ?_
  have := (paW_pos q v).le
  have h2 : 0 ≤ (t * ‖F v‖ - ‖G v‖) ^ 2 * paW q v := by positivity
  simp only
  nlinarith

theorem paN_eq_zero {q c : ℕ} (hq : 1 ≤ q) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (h0 : paN q F = 0) : F = 0 := by
  obtain ⟨-, hre⟩ := gaussianInner_self_re q F
  have hz : (paIP q F F).re = 0 := by
    unfold paN at h0
    have := Real.sqrt_eq_zero'.mp h0
    linarith
  rw [gaussianInner_self, Complex.ofReal_re] at hz
  have hi : Integrable (fun v => ‖F v‖ ^ 2 * paW q v) := by
    have := gaussianInner_integrable_norm hq hF hF
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only; ring
  have hc : Continuous (fun v => ‖F v‖ ^ 2 * paW q v) := by
    have := paPoly_continuous hF; have := paW_continuous (ι := ι) q; fun_prop
  have hae := (integral_eq_zero_iff_of_nonneg (fun v => by have := paW_pos q v; positivity) hi).1 hz
  have heq := (Continuous.ae_eq_iff_eq volume hc continuous_const).1 hae
  funext v
  have := congrFun heq v
  simp only [Pi.zero_apply] at this ⊢
  have hw := paW_pos q v
  have : ‖F v‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp this)

theorem pa_tm_inj {a b : ι →₀ ℕ} (h : Finsupp.toMultiset a = Finsupp.toMultiset b) : a = b := by
  rw [← Finsupp.toMultiset_toFinsupp a, h, Finsupp.toMultiset_toFinsupp]

def paPD : (n : ℕ) → (Fin n → ι) → MvPolynomial ι ℂ → MvPolynomial ι ℂ
  | 0, _, p => p
  | n + 1, m, p => paPD n (Fin.init m) (MvPolynomial.pderiv (m (Fin.last n)) p)

theorem paPF_X_mul (p : MvPolynomial ι ℂ) (j : ι) :
    paPF (p * MvPolynomial.X j) = paPF p * fun v : EuclideanSpace ℂ ι => v j := by
  funext v; simp [paPF]

theorem paPF_diff (p : MvPolynomial ι ℂ) : Differentiable ℂ (paPF p) ∧
    ∀ (j : ι) (y : EuclideanSpace ℂ ι),
      fderiv ℂ (paPF p) y (EuclideanSpace.single j 1) = paPF (MvPolynomial.pderiv j p) y := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : paPF (MvPolynomial.C a) = fun _ : EuclideanSpace ℂ ι => a := by funext v; simp [paPF]
    rw [e]
    refine ⟨differentiable_const a, fun j y => ?_⟩
    simp [paPF]
  | add p r hp hr =>
    rw [paPF_add]
    refine ⟨hp.1.add hr.1, fun j y => ?_⟩
    rw [fderiv_add (hp.1 y) (hr.1 y), ContinuousLinearMap.add_apply, hp.2, hr.2, map_add, paPF_add]
    rfl
  | mul_X p k hp =>
    have hd : Differentiable ℂ (fun v : EuclideanSpace ℂ ι => v k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ).differentiable
    rw [paPF_X_mul]
    refine ⟨hp.1.mul hd, fun j y => ?_⟩
    rw [fderiv_mul (hp.1 y) (hd y)]
    have e1 : fderiv ℂ (fun v : EuclideanSpace ℂ ι => v k) y =
        (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ) :=
      (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ).fderiv
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      e1, hp.2, Derivation.leibniz, MvPolynomial.pderiv_X]
    simp only [EuclideanSpace.coe_proj, EuclideanSpace.single_apply, smul_eq_mul, paPF, map_add,
      map_mul, MvPolynomial.eval_X, Pi.single_apply]
    by_cases h : j = k
    · subst h; simp <;> ring
    · simp [h, Ne.symm h] <;> ring

theorem paPF_contDiff (p : MvPolynomial ι ℂ) : ContDiff ℂ (⊤ : ℕ∞) (paPF p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : paPF (MvPolynomial.C a) = fun _ : EuclideanSpace ℂ ι => a := by funext v; simp [paPF]
    rw [e]; exact contDiff_const
  | add p r hp hr => rw [paPF_add]; exact hp.add hr
  | mul_X p k hp =>
    rw [paPF_X_mul]
    exact hp.mul (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ).contDiff

theorem paPF_iter (n : ℕ) : ∀ (p : MvPolynomial ι ℂ) (m : Fin n → ι) (x : EuclideanSpace ℂ ι),
    iteratedFDeriv ℂ n (paPF p) x (fun k => EuclideanSpace.single (m k) 1) = paPF (paPD n m p) x := by
  induction n with
  | zero => intro p m x; simp [paPD]
  | succ n ih =>
    intro p m x
    rw [iteratedFDeriv_succ_apply_right]
    have hc : ContDiff ℂ (⊤ : ℕ∞) (fderiv ℂ (paPF p)) :=
      (paPF_contDiff p).fderiv_right (by simp)
    rw [← iteratedFDeriv_clm_apply_const_apply hc (by exact_mod_cast le_top)]
    have e : (fun y => fderiv ℂ (paPF p) y (EuclideanSpace.single (m (Fin.last n)) 1)) =
        paPF (MvPolynomial.pderiv (m (Fin.last n)) p) := by
      funext y; exact (paPF_diff p).2 _ y
    rw [e]
    exact ih _ (Fin.init m) x

theorem paFact_succ (β : ι →₀ ℕ) (i : ι) (h : 1 ≤ β i) :
    (paFact β : ℂ) = (β i : ℂ) * paFact (β - Finsupp.single i 1) := by
  unfold paFact
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have e : ∏ x ∈ Finset.univ.erase i, (β x).factorial =
      ∏ x ∈ Finset.univ.erase i, ((β - Finsupp.single i 1 : ι →₀ ℕ) x).factorial := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hx).symm, Nat.sub_zero]
  rw [e, Finsupp.tsub_apply, Finsupp.single_eq_same]
  obtain ⟨k, hk⟩ : ∃ k, β i = k + 1 := ⟨β i - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast; ring

theorem paPD_monomial (n : ℕ) : ∀ (m : Fin n → ι) (β : ι →₀ ℕ) (a : ℂ),
    MvPolynomial.constantCoeff (paPD n m (MvPolynomial.monomial β a)) =
      if Finsupp.toMultiset β = (List.ofFn m : Multiset ι) then a * paFact β else 0 := by
  induction n with
  | zero =>
    intro m β a
    simp only [paPD, MvPolynomial.constantCoeff_monomial, List.ofFn_zero, Multiset.coe_nil]
    by_cases h : β = 0
    · subst h; simp [paFact]
    · rw [if_neg h, if_neg]
      intro h2; exact h (pa_tm_inj (by rw [h2, Finsupp.toMultiset_zero]))
  | succ n ih =>
    intro m β a
    simp only [paPD, MvPolynomial.pderiv_monomial]
    rw [ih]
    set i := m (Fin.last n)
    have hl : ((List.ofFn m : List ι) : Multiset ι) = (List.ofFn (Fin.init m) : Multiset ι) + {i} := by
      rw [List.ofFn_succ', List.concat_eq_append, ← Multiset.coe_add]
      rfl
    rw [hl]
    by_cases hb : β i = 0
    · rw [hb]
      simp only [Nat.cast_zero, mul_zero, zero_mul, ite_self]
      rw [if_neg]
      intro h
      have := congrArg (Multiset.count i) h
      rw [Finsupp.count_toMultiset, hb, Multiset.count_add, Multiset.count_singleton_self] at this
      omega
    · have hb1 : 1 ≤ β i := Nat.one_le_iff_ne_zero.mpr hb
      have hle : Finsupp.single i 1 ≤ β := Finsupp.single_le_iff.mpr hb1
      have hsplit : Finsupp.toMultiset β = Finsupp.toMultiset (β - Finsupp.single i 1) + {i} := by
        conv_lhs => rw [← tsub_add_cancel_of_le hle]
        rw [map_add, Finsupp.toMultiset_single, one_nsmul]
      rw [hsplit]
      by_cases hc : Finsupp.toMultiset (β - Finsupp.single i 1) = (List.ofFn (Fin.init m) : Multiset ι)
      · rw [if_pos hc, if_pos (by rw [hc]), paFact_succ β i hb1]; ring
      · rw [if_neg hc, if_neg (fun h => hc (add_right_cancel h))]

theorem paPF_zero (p : MvPolynomial ι ℂ) : paPF p 0 = MvPolynomial.constantCoeff p := by
  have : (fun i => (0 : EuclideanSpace ℂ ι) i) = 0 := by funext i; simp
  show MvPolynomial.eval (fun i => (0 : EuclideanSpace ℂ ι) i) p = _
  rw [this, MvPolynomial.eval_zero]

theorem paD_mono (α β : ι →₀ ℕ) : paD α (paMono β) = if α = β then (paFact α : ℂ) else 0 := by
  unfold paD polyDeriv
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
  have := paPF_iter _ (MvPolynomial.monomial β 1)
    (fun k => (Finsupp.toMultiset α).toList.get (k.cast (Multiset.length_toList _).symm)) 0
  simp only at this ⊢
  rw [paMono, this, paPF_zero, paPD_monomial]
  have hl : List.ofFn (fun k : Fin (Multiset.card (Finsupp.toMultiset α)) =>
      (Finsupp.toMultiset α).toList.get (k.cast (Multiset.length_toList _).symm)) =
      (Finsupp.toMultiset α).toList := by
    apply List.ext_get (by simp)
    intro k h1 h2; simp
  rw [hl, Multiset.coe_toList]
  by_cases h : α = β
  · subst h; simp
  · rw [if_neg (fun h' => h (pa_tm_inj h').symm), if_neg h]

end

end ReciprocityTheory.ChartRestriction.G.I2
end
