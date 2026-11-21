import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.MonoNormSq
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDefs

section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory

section helpers

open Set Complex

theorem conj_pow_mul_pow_polar (r θ : ℝ) (a b : ℕ) :
    starRingEnd ℂ (((r : ℂ) * Complex.exp (θ * I)) ^ a) * ((r : ℂ) * Complex.exp (θ * I)) ^ b =
      ((r ^ (a + b) : ℝ) : ℂ) * Complex.exp ((((b : ℂ) - a) * I) * θ) := by
  rw [map_pow, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have : Complex.exp (((b : ℂ) - a) * I * θ) =
      Complex.exp (a * (θ * -I)) * Complex.exp (b * (θ * I)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]; push_cast; ring

theorem integral_conj_pow_mul_pow_mul_exp_eq_polar (a b : ℕ) (t : ℝ) :
    ∫ z : ℂ, starRingEnd ℂ (z ^ a) * z ^ b * (Real.exp (-(t * ‖z‖ ^ 2)) : ℂ) =
      ((∫ r in Ioi (0 : ℝ), r ^ (a + b + 1) * Real.exp (-(t * r ^ 2)) : ℝ) : ℂ) *
        ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((((b : ℂ) - a) * I) * θ) := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hm : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  rw [setIntegral_congr_fun hm (g := fun p : ℝ × ℝ =>
      ((p.1 ^ (a + b + 1) * Real.exp (-(t * p.1 ^ 2)) : ℝ) : ℂ) *
        Complex.exp ((((b : ℂ) - a) * I) * p.2))]
  · rw [Measure.volume_eq_prod]
    refine (setIntegral_prod_mul (μ := volume) (ν := volume)
      (fun r : ℝ => ((r ^ (a + b + 1) * Real.exp (-(t * r ^ 2)) : ℝ) : ℂ))
      (fun θ : ℝ => Complex.exp ((((b : ℂ) - a) * I) * θ)) _ _).trans ?_
    rw [integral_complex_ofReal]
  · rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr : 0 < r := hr
    have hw : Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp (θ * I) := by
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
    have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [norm_polarCoord_symm, abs_of_pos hr]
    simp only
    rw [hn, hw, conj_pow_mul_pow_polar, Complex.real_smul]
    push_cast; ring

theorem integral_exp_mul_I_of_ne {a b : ℕ} (hab : a ≠ b) :
    ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((((b : ℂ) - a) * I) * θ) = 0 := by
  have hc : ((b : ℂ) - a) * I ≠ 0 := by
    refine mul_ne_zero ?_ I_ne_zero
    rw [sub_ne_zero]; exact_mod_cast (Ne.symm hab)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos]), integral_exp_mul_complex hc]
  have : Complex.exp (((b : ℂ) - a) * I * (Real.pi : ℝ)) =
      Complex.exp (((b : ℂ) - a) * I * ((-Real.pi : ℝ) : ℂ)) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨(b : ℤ) - a, ?_⟩
    push_cast; ring
  rw [this, sub_self, zero_div]

theorem integral_exp_mul_I_self (a : ℕ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((((a : ℂ) - a) * I) * θ) = 2 * Real.pi := by
  simp only [sub_self, zero_mul, Complex.exp_zero]
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
  simp; ring

theorem integral_Ioi_pow_mul_exp_neg_mul_sq (a : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ r in Ioi (0 : ℝ), r ^ (a + a + 1) * Real.exp (-(t * r ^ 2)) =
      (a.factorial : ℝ) / (2 * t ^ (a + 1)) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((a + a + 1 : ℕ) : ℝ)) (b := t)
    two_pos (by have := (Nat.cast_nonneg (a + a + 1) : (0 : ℝ) ≤ _); linarith) ht
  have e : ∫ r in Ioi (0 : ℝ), r ^ (a + a + 1) * Real.exp (-(t * r ^ 2)) =
      ∫ r in Ioi (0 : ℝ), r ^ (((a + a + 1 : ℕ) : ℝ)) * Real.exp (-t * r ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    rw [Real.rpow_natCast, Real.rpow_two, neg_mul]
  rw [e, h]
  have g : ((((a + a + 1 : ℕ) : ℝ)) + 1) / 2 = (a : ℝ) + 1 := by push_cast; ring
  have g2 : -((((a + a + 1 : ℕ) : ℝ)) + 1) / 2 = -(((a + 1 : ℕ) : ℝ)) := by push_cast; ring
  rw [g, g2, Real.Gamma_nat_eq_factorial, Real.rpow_neg ht.le, Real.rpow_natCast]
  field_simp

theorem integrable_conj_pow_mul_pow_mul_exp (a b : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable fun z : ℂ => starRingEnd ℂ (z ^ a) * z ^ b * (Real.exp (-(t * ‖z‖ ^ 2)) : ℂ) := by
  have hf : Integrable (fun z : ℂ => (fun y : ℝ => y ^ (a + b) * Real.exp (-(t * y ^ 2))) ‖z‖)
      volume := by
    refine (integrable_fun_norm_addHaar (volume : Measure ℂ)
      (f := fun y : ℝ => y ^ (a + b) * Real.exp (-(t * y ^ 2)))).mpr ?_
    have h := integrableOn_rpow_mul_exp_neg_mul_sq ht (s := ((a + b + 1 : ℕ) : ℝ))
      (by have := (Nat.cast_nonneg (a + b + 1) : (0 : ℝ) ≤ _); linarith)
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy : 0 < y := hy
    simp only [Complex.finrank_real_complex, smul_eq_mul]
    rw [Real.rpow_natCast]; ring_nf
  refine hf.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  simp only [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [pow_add]

theorem integral_conj_pow_mul_pow_mul_exp_of_ne {a b : ℕ} (hab : a ≠ b) (t : ℝ) :
    ∫ z : ℂ, starRingEnd ℂ (z ^ a) * z ^ b * (Real.exp (-(t * ‖z‖ ^ 2)) : ℂ) = 0 := by
  rw [integral_conj_pow_mul_pow_mul_exp_eq_polar, integral_exp_mul_I_of_ne hab, mul_zero]

theorem integral_norm_pow_mul_exp (a : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ z : ℂ, ‖z‖ ^ (a + a) * Real.exp (-(t * ‖z‖ ^ 2)) =
      Real.pi * (a.factorial : ℝ) / t ^ (a + 1) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : (fun z : ℂ => ((‖z‖ ^ (a + a) * Real.exp (-(t * ‖z‖ ^ 2)) : ℝ) : ℂ)) =
      fun z : ℂ => starRingEnd ℂ (z ^ a) * z ^ a * (Real.exp (-(t * ‖z‖ ^ 2)) : ℂ) := by
    funext z
    rw [Complex.conj_mul', norm_pow]
    push_cast; ring
  rw [e, integral_conj_pow_mul_pow_mul_exp_eq_polar, integral_Ioi_pow_mul_exp_neg_mul_sq a ht, integral_exp_mul_I_self]
  have : t ^ (a + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem gs_prod {N : ℕ} (a b : Fin N → ℕ) (t : ℝ) (z : Fin N → ℂ) :
    starRingEnd ℂ (monoC a z) * monoC b z * (Real.exp (-(t * sqN z)) : ℂ) =
      ∏ i, (starRingEnd ℂ (z i ^ a i) * z i ^ b i * (Real.exp (-(t * ‖z i‖ ^ 2)) : ℂ)) := by
  rw [monoC, monoC, sqN, map_prod, Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum,
    Complex.ofReal_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

theorem gs_prod_sq {N : ℕ} (a : Fin N → ℕ) (t : ℝ) (z : Fin N → ℂ) :
    ‖monoC a z‖ ^ 2 * Real.exp (-(t * sqN z)) =
      ∏ i, (‖z i‖ ^ (a i + a i) * Real.exp (-(t * ‖z i‖ ^ 2))) := by
  rw [monoC, sqN, norm_prod, ← Finset.prod_pow, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_pow, ← pow_mul, mul_two]

end helpers

theorem integrable_mono_mul_exp {N : ℕ} (a b : Fin N → ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable fun z : Fin N → ℂ =>
      starRingEnd ℂ (monoC a z) * monoC b z * (Real.exp (-(t * sqN z)) : ℂ) := by
  simp_rw [gs_prod]
  exact Integrable.fintype_prod (f := fun i (w : ℂ) =>
    starRingEnd ℂ (w ^ a i) * w ^ b i * (Real.exp (-(t * ‖w‖ ^ 2)) : ℂ))
    (μ := fun _ => volume) fun i => integrable_conj_pow_mul_pow_mul_exp (a i) (b i) ht

theorem integral_mono_mul_exp_of_ne {N : ℕ} {a b : Fin N → ℕ} (hab : a ≠ b) {t : ℝ} (ht : 0 < t) :
    ∫ z : Fin N → ℂ, starRingEnd ℂ (monoC a z) * monoC b z * (Real.exp (-(t * sqN z)) : ℂ) = 0 := by
  simp_rw [gs_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun i (w : ℂ) =>
    starRingEnd ℂ (w ^ a i) * w ^ b i * (Real.exp (-(t * ‖w‖ ^ 2)) : ℂ))]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  exact Finset.prod_eq_zero (Finset.mem_univ i) (integral_conj_pow_mul_pow_mul_exp_of_ne hi t)

theorem integral_mono_sq_mul_exp {N : ℕ} (a : Fin N → ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ z : Fin N → ℂ, ‖monoC a z‖ ^ 2 * Real.exp (-(t * sqN z)) =
      Real.pi ^ N * ((∏ i, (a i).factorial : ℕ) : ℝ) / t ^ ((∑ i, a i) + N) := by
  simp_rw [gs_prod_sq]
  rw [integral_fintype_prod_volume_eq_prod (fun i (w : ℂ) =>
    ‖w‖ ^ (a i + a i) * Real.exp (-(t * ‖w‖ ^ 2)))]
  simp_rw [integral_norm_pow_mul_exp _ ht]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_prod, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

instance isProbabilityMeasure_gaussC (N : ℕ) : IsProbabilityMeasure (gaussC N) := by
  have e1 : (fun z : Fin N → ℂ => ‖monoC (0 : Fin N → ℕ) z‖ ^ 2 * Real.exp (-(1 * sqN z))) =
      fun z => Real.exp (-sqN z) := by
    funext z; simp [monoC]
  have hval := integral_mono_sq_mul_exp (N := N) 0 one_pos
  rw [e1] at hval
  simp only [Pi.zero_apply, Nat.factorial_zero, Finset.prod_const_one, Nat.cast_one, mul_one,
    Finset.sum_const_zero, zero_add, one_pow, div_one] at hval
  have hint : Integrable fun z : Fin N → ℂ => Real.exp (-sqN z) := by
    refine (integrable_mono_mul_exp (N := N) 0 0 one_pos).norm.congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp [monoC, Complex.norm_exp]
  constructor
  rw [gaussC, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
      (Filter.Eventually.of_forall fun z => by positivity),
    integral_const_mul, hval, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

end ReciprocityTheory.GeometryOfNumbersTheory
end

section
noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Metric Set

section polar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem sphMonom_polar_mul (μ : Measure E) [μ.IsAddHaarMeasure] (G : E → ℂ) (φ : ℝ → ℝ) :
    ∫ x, G (‖x‖⁻¹ • x) * (φ ‖x‖ : ℂ) ∂μ =
      (∫ u : sphere (0 : E) 1, G u ∂μ.toSphere) *
        ((∫ r : Ioi (0 : ℝ), φ r ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) : ℝ) : ℂ) := by
  have hpres := (Measure.measurePreserving_homeomorphUnitSphereProd μ).integral_comp
    (Homeomorph.measurableEmbedding _)
    (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => G (p.1 : E) * ((φ p.2 : ℝ) : ℂ))
  calc ∫ x, G (‖x‖⁻¹ • x) * (φ ‖x‖ : ℂ) ∂μ
      = ∫ x in ({0}ᶜ : Set E), G (‖x‖⁻¹ • x) * (φ ‖x‖ : ℂ) ∂μ := by
        rw [restrict_compl_singleton]
    _ = ∫ x : ({0}ᶜ : Set E), G (‖(x : E)‖⁻¹ • (x : E)) * (φ ‖(x : E)‖ : ℂ)
          ∂(Measure.comap Subtype.val μ) :=
        (integral_subtype_comap (measurableSet_singleton 0).compl _).symm
    _ = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), G (p.1 : E) * ((φ p.2 : ℝ) : ℂ)
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
        refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) hpres
        simp [homeomorphUnitSphereProd]
    _ = _ := by
        rw [integral_prod_mul (fun u : sphere (0 : E) 1 => G (u : E))
          (fun r : Ioi (0 : ℝ) => ((φ r : ℝ) : ℂ)), integral_complex_ofReal]

end polar

theorem sphMonom_volumeIoiPow_integral (m : ℕ) (φ : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), φ r ∂(Measure.volumeIoiPow m) = ∫ r in Ioi (0 : ℝ), r ^ m * φ r := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul
    ((measurable_subtype_coe.pow_const m).ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [integral_subtype_comap measurableSet_Ioi (fun r : ℝ => (ENNReal.ofReal (r ^ m)).toReal • φ r)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hr) m)]

theorem sphMonom_radial (m k : ℕ) :
    ∫ r : Ioi (0 : ℝ), r.1 ^ k * Real.exp (-(r.1 ^ 2)) ∂(Measure.volumeIoiPow m) =
      Real.Gamma ((((m + k : ℕ) : ℝ) + 1) / 2) / 2 := by
  have hv := sphMonom_volumeIoiPow_integral m (fun x : ℝ => x ^ k * Real.exp (-(x ^ 2)))
  rw [hv]
  have hq : (-1 : ℝ) < ((m + k : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((m + k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h2 := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((m + k : ℕ) : ℝ)) (by norm_num) hq
  calc ∫ r in Ioi (0 : ℝ), r ^ m * (r ^ k * Real.exp (-(r ^ 2)))
      = ∫ x in Ioi (0 : ℝ), x ^ (((m + k : ℕ) : ℝ)) * Real.exp (-x ^ (2 : ℝ)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        simp only [Real.rpow_natCast, Real.rpow_two]
        ring
    _ = 1 / 2 * Real.Gamma ((((m + k : ℕ) : ℝ) + 1) / 2) := h2
    _ = _ := by ring

section eucl

variable (N : ℕ)

def sphMonomL : (Fin N → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin N) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℂ)).symm

def sphMonomMu : Measure (EuclideanSpace ℂ (Fin N)) :=
  (volume : Measure (Fin N → ℂ)).map (sphMonomL N)

instance sphMonomMu_isAddHaar : (sphMonomMu N).IsAddHaarMeasure := by
  unfold sphMonomMu; infer_instance

theorem norm_sphMonomL (z : Fin N → ℂ) : ‖sphMonomL N z‖ = Real.sqrt (sqN z) := by
  rw [EuclideanSpace.norm_eq]
  rfl

theorem integral_sphMonomMu (g : EuclideanSpace ℂ (Fin N) → ℂ) :
    ∫ x, g x ∂(sphMonomMu N) = ∫ z, g (sphMonomL N z) :=
  (sphMonomL N).toHomeomorph.measurableEmbedding.integral_map g

theorem finrank_sphMonomE : Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) = 2 * N := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

end eucl

section key

variable {N : ℕ}

theorem sphMonom_sqN_nonneg (z : Fin N → ℂ) : 0 ≤ sqN z :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem sphMonom_key [NeZero N] {k : ℕ} (f : (Fin N → ℂ) → ℂ)
    (hf : ∀ (r : ℝ) (z : Fin N → ℂ), f (r • z) = (r : ℂ) ^ k * f z) :
    (∫ z, f z * (Real.exp (-sqN z) : ℂ)) *
        ((Real.Gamma ((((2 * N - 1 + 0 : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) =
      (∫ z, f ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ)) *
        ((Real.Gamma ((((2 * N - 1 + k : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  have hzs : ∀ z : Fin N → ℂ, z = Real.sqrt (sqN z) • ((Real.sqrt (sqN z))⁻¹ • z) := by
    intro z
    by_cases hs : Real.sqrt (sqN z) = 0
    · have h0 : sqN z = 0 := by
        have := Real.sqrt_eq_zero'.1 hs
        linarith [sphMonom_sqN_nonneg z]
      have hz : z = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖z j‖)).1 h0 i (Finset.mem_univ i)
        simpa using this
      rw [hs, zero_smul]
      exact hz
    · rw [smul_inv_smul₀ hs]
  have hhom : ∀ z, f z = ((Real.sqrt (sqN z) : ℝ) : ℂ) ^ k * f ((Real.sqrt (sqN z))⁻¹ • z) := by
    intro z
    conv_lhs => rw [hzs z]
    exact hf _ _
  have hexp : ∀ z : Fin N → ℂ, Real.exp (-sqN z) = Real.exp (-(Real.sqrt (sqN z)) ^ 2) := by
    intro z
    rw [Real.sq_sqrt (sphMonom_sqN_nonneg z)]
  let G : EuclideanSpace ℂ (Fin N) → ℂ := fun y => f ((sphMonomL N).symm y)
  have hG : ∀ z, G (‖sphMonomL N z‖⁻¹ • sphMonomL N z) = f ((Real.sqrt (sqN z))⁻¹ • z) := by
    intro z
    simp only [G, map_smul, ContinuousLinearEquiv.symm_apply_apply, norm_sphMonomL]
  have hrad : ∀ j, ∫ r : Ioi (0 : ℝ), r.1 ^ j * Real.exp (-(r.1 ^ 2))
      ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) - 1)) =
        Real.Gamma ((((2 * N - 1 + j : ℕ) : ℝ) + 1) / 2) / 2 := by
    intro j
    rw [finrank_sphMonomE]
    exact sphMonom_radial (2 * N - 1) j
  have hpol : ∀ j, ∫ x, G (‖x‖⁻¹ • x) * (((‖x‖ ^ j * Real.exp (-(‖x‖ ^ 2)) : ℝ)) : ℂ) ∂(sphMonomMu N) =
      (∫ u : sphere (0 : EuclideanSpace ℂ (Fin N)) 1, G u ∂(sphMonomMu N).toSphere) *
        ((Real.Gamma ((((2 * N - 1 + j : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) := by
    intro j
    refine (sphMonom_polar_mul (sphMonomMu N) G (fun r => r ^ j * Real.exp (-(r ^ 2)))).trans ?_
    congr 1
    exact_mod_cast hrad j
  have hL1 : ∫ z, f z * (Real.exp (-sqN z) : ℂ) =
      ∫ x, G (‖x‖⁻¹ • x) * (((‖x‖ ^ k * Real.exp (-(‖x‖ ^ 2)) : ℝ)) : ℂ) ∂(sphMonomMu N) := by
    rw [integral_sphMonomMu]
    congr 1
    funext z
    rw [hG z, norm_sphMonomL, hhom z, hexp z]
    push_cast
    ring
  have hL2 : ∫ z, f ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ) =
      ∫ x, G (‖x‖⁻¹ • x) * (((‖x‖ ^ 0 * Real.exp (-(‖x‖ ^ 2)) : ℝ)) : ℂ) ∂(sphMonomMu N) := by
    rw [integral_sphMonomMu]
    congr 1
    funext z
    rw [hG z, norm_sphMonomL, hexp z]
    push_cast
    ring
  rw [hL1, hL2, hpol k, hpol 0]
  ring

theorem sphMonom_continuous_sqN : Continuous (fun z : Fin N → ℂ => sqN z) := by
  unfold sqN
  exact continuous_finset_sum _ fun i _ => (continuous_norm.comp (continuous_apply i)).pow 2

theorem sphMonom_measurable_normalize :
    Measurable (fun z : Fin N → ℂ => (((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z) :=
  (Complex.measurable_ofReal.comp (sphMonom_continuous_sqN.measurable.sqrt.inv)).smul measurable_id

theorem sphMonom_integral_sphProb (g : (Fin N → ℂ) → ℂ) (hg : Continuous g) :
    ∫ z, g z ∂(sphProb N) =
      ((Real.pi ^ N)⁻¹ : ℂ) * ∫ z, g ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ) := by
  have hm := sphMonom_measurable_normalize (N := N)
  have hmeas : Measurable fun z : Fin N → ℂ => ENNReal.ofReal ((Real.pi ^ N)⁻¹ * Real.exp (-sqN z)) :=
    Measurable.ennreal_ofReal (measurable_const.mul
      (Real.measurable_exp.comp (sphMonom_continuous_sqN.measurable.neg)))
  rw [sphProb, integral_map hm.aemeasurable hg.aestronglyMeasurable, gaussC,
    integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  congr 1
  funext z
  have hsm : (((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z = (Real.sqrt (sqN z))⁻¹ • z := by
    funext i
    simp [Complex.real_smul]
  rw [ENNReal.toReal_ofReal (by positivity), hsm, Complex.real_smul]
  push_cast
  ring

theorem sphMonom_monoC_smul (a : Fin N → ℕ) (r : ℝ) (z : Fin N → ℂ) :
    monoC a (r • z) = (r : ℂ) ^ (∑ i, a i) * monoC a z := by
  simp only [monoC, Pi.smul_apply, Complex.real_smul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

theorem sphMonom_f_smul (a b : Fin N → ℕ) (r : ℝ) (z : Fin N → ℂ) :
    starRingEnd ℂ (monoC a (r • z)) * monoC b (r • z) =
      (r : ℂ) ^ ((∑ i, a i) + ∑ i, b i) * (starRingEnd ℂ (monoC a z) * monoC b z) := by
  simp only [sphMonom_monoC_smul, map_mul, map_pow, Complex.conj_ofReal]
  ring

theorem sphMonom_continuous_f (a b : Fin N → ℕ) :
    Continuous fun z : Fin N → ℂ => starRingEnd ℂ (monoC a z) * monoC b z := by
  have hm : ∀ c : Fin N → ℕ, Continuous fun z : Fin N → ℂ => monoC c z := fun c =>
    continuous_finset_prod _ fun i _ => (continuous_apply i).pow _
  exact (Complex.continuous_conj.comp (hm a)).mul (hm b)

theorem sphMonom_sqN_smul (c : ℂ) (z : Fin N → ℂ) : sqN (c • z) = ‖c‖ ^ 2 * sqN z := by
  simp only [sqN, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem sphMonom_sqN_normalize (z : Fin N → ℂ) (hz : z ≠ 0) :
    sqN ((((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z) = 1 := by
  have hs : sqN z ≠ 0 := by
    intro h
    apply hz
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖z j‖)).1 h i (Finset.mem_univ i)
    simpa using this
  rw [sphMonom_sqN_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (sphMonom_sqN_nonneg z), inv_mul_cancel₀ hs]

theorem sphMonom_gamma (D n k : ℕ) (h : k = n + n) :
    Real.Gamma ((((2 * (D + 1) - 1 + k : ℕ) : ℝ) + 1) / 2) = ((D + n).factorial : ℝ) := by
  subst h
  rw [show 2 * (D + 1) - 1 + (n + n) = 2 * (D + n) + 1 by omega,
    show ((((2 * (D + n) + 1 : ℕ) : ℝ) + 1) / 2) = ((D + n : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]

end key

end ReciprocityTheory.GeometryOfNumbersTheory
end
end

section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory

instance isProbabilityMeasure_sphProb (N : ℕ) : IsProbabilityMeasure (sphProb N) := by
  unfold sphProb
  exact Measure.isProbabilityMeasure_map sphMonom_measurable_normalize.aemeasurable

theorem sphProb_compl_sphere (D : ℕ) : sphProb (D + 1) {z | sqN z = 1}ᶜ = 0 := by
  unfold sphProb
  rw [Measure.map_apply sphMonom_measurable_normalize
    ((isClosed_eq sphMonom_continuous_sqN continuous_const).measurableSet.compl)]
  apply measure_mono_null (t := {0})
  · intro z hz
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq] at hz
    rw [Set.mem_singleton_iff]
    by_contra h0
    exact hz (sphMonom_sqN_normalize z h0)
  · unfold gaussC
    exact withDensity_absolutelyContinuous _ _ (measure_singleton 0)

theorem integral_mono_sphProb_of_ne {D : ℕ} {a b : Fin (D + 1) → ℕ} (hab : a ≠ b) :
    ∫ z, starRingEnd ℂ (monoC a z) * monoC b z ∂(sphProb (D + 1)) = 0 := by
  have hk := sphMonom_key (N := D + 1) (k := (∑ i, a i) + ∑ i, b i)
    (fun z => starRingEnd ℂ (monoC a z) * monoC b z) (sphMonom_f_smul a b)
  beta_reduce at hk
  have hG := integral_mono_mul_exp_of_ne hab one_pos
  simp only [one_mul] at hG
  rw [hG, zero_mul] at hk
  rw [sphMonom_integral_sphProb _ (sphMonom_continuous_f a b)]
  rcases mul_eq_zero.mp hk.symm with h | h
  · rw [h, mul_zero]
  · exfalso
    norm_cast at h
    exact (div_pos (Real.Gamma_pos_of_pos (by positivity)) two_pos).ne' h

theorem integral_mono_sq_sphProb {D : ℕ} (a : Fin (D + 1) → ℕ) :
    ∫ z, ‖monoC a z‖ ^ 2 ∂(sphProb (D + 1)) = monoNormSq a := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ z : Fin (D + 1) → ℂ,
      ((‖monoC a z‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ (monoC a z) * monoC a z := fun z => by
    rw [Complex.conj_mul']; push_cast; rfl
  simp only [e]
  rw [sphMonom_integral_sphProb _ (sphMonom_continuous_f a a)]
  have hk := sphMonom_key (N := D + 1) (k := (∑ i, a i) + ∑ i, a i)
    (fun z => starRingEnd ℂ (monoC a z) * monoC a z) (sphMonom_f_smul a a)
  beta_reduce at hk
  have hG := integral_mono_sq_mul_exp a one_pos
  simp only [one_mul, one_pow, div_one] at hG
  have hG' : ∫ z, starRingEnd ℂ (monoC a z) * monoC a z * (Real.exp (-sqN z) : ℂ) =
      ((Real.pi ^ (D + 1) * ((∏ i, (a i).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← hG, ← integral_complex_ofReal]
    congr 1; funext z
    rw [Complex.ofReal_mul, e]
  rw [hG', sphMonom_gamma D 0 0 rfl, sphMonom_gamma D (∑ i, a i) _ rfl] at hk
  have hR : (((((D + ∑ i, a i).factorial : ℕ) : ℝ) / 2 : ℝ) : ℂ) ≠ 0 := by
    norm_cast; positivity
  simp only [Nat.add_zero] at hk
  rw [eq_div_of_mul_eq hR hk.symm]
  unfold monoNormSq
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : (((D + ∑ i, a i).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [add_comm (∑ i, a i) D]
  push_cast
  field_simp

end ReciprocityTheory.GeometryOfNumbersTheory
end

section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory

theorem supSt_adt_eq (D n : ℕ) :
    Finset.Nat.antidiagonalTuple (D + 1) n = Finset.piAntidiag Finset.univ n := by
  ext a
  simp [Finset.mem_piAntidiag, Finset.Nat.mem_antidiagonalTuple]

theorem supSt_term {D n : ℕ} (a : Fin (D + 1) → ℕ) (ha : ∑ i, a i = n) (z : Fin (D + 1) → ℂ) :
    ‖monoC a z‖ ^ 2 / monoNormSq a =
      ((n + D).choose D : ℝ) * ((Nat.multinomial Finset.univ a : ℕ) *
        ∏ i, (‖z i‖ ^ 2) ^ a i) := by
  have hnorm : ‖monoC a z‖ ^ 2 = ∏ i, (‖z i‖ ^ 2) ^ a i := by
    simp only [monoC, norm_prod, norm_pow, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by ring
  have hP : ((∏ i, (a i).factorial : ℕ) : ℝ) ≠ 0 := by
    have : 0 < ∏ i, (a i).factorial := Finset.prod_pos fun i _ => Nat.factorial_pos _
    exact_mod_cast this.ne'
  have hspec := Nat.multinomial_spec Finset.univ a
  rw [ha] at hspec
  have hm : ((Nat.multinomial Finset.univ a : ℕ) : ℝ) =
      (n.factorial : ℝ) / ((∏ i, (a i).factorial : ℕ) : ℝ) := by
    rw [eq_div_iff hP, mul_comm]
    exact_mod_cast hspec
  have hc : ((n + D).choose D : ℝ) = ((n + D).factorial : ℝ) / ((n.factorial : ℝ) * (D.factorial : ℝ)) := by
    rw [eq_div_iff (by positivity), ← mul_assoc]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n D
  rw [hnorm, monoNormSq, ha, hm, hc]
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (D.factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((n + D).factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem sum_mono_sq_div (D n : ℕ) (z : Fin (D + 1) → ℂ) :
    ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, ‖monoC a z‖ ^ 2 / monoNormSq a =
      ((n + D).choose D : ℝ) * sqN z ^ n := by
  rw [Finset.sum_congr rfl (fun a ha => supSt_term a (Finset.Nat.mem_antidiagonalTuple.mp ha) z),
    ← Finset.mul_sum, supSt_adt_eq, sqN, Finset.sum_pow_eq_sum_piAntidiag]

theorem supSt_norm_mono_le {D : ℕ} (a : Fin (D + 1) → ℕ) (z : Fin (D + 1) → ℂ) (h : sqN z = 1) :
    ‖monoC a z‖ ≤ 1 := by
  simp only [monoC, norm_prod, norm_pow]
  apply Finset.prod_le_one (fun i _ => by positivity)
  intro i _
  have h1 : ‖z i‖ ^ 2 ≤ sqN z := by
    unfold sqN
    exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  rw [h] at h1
  have h2 : ‖z i‖ ≤ 1 := by nlinarith [norm_nonneg (z i)]
  exact pow_le_one₀ (norm_nonneg _) h2

theorem supSt_integrable {D : ℕ} (a b : Fin (D + 1) → ℕ) :
    Integrable (fun z => starRingEnd ℂ (monoC a z) * monoC b z) (sphProb (D + 1)) := by
  have hae : ∀ᵐ z ∂(sphProb (D + 1)), sqN z = 1 := mem_ae_iff.mpr (sphProb_compl_sphere D)
  refine Integrable.of_bound (sphMonom_continuous_f a b).aestronglyMeasurable 1 ?_
  filter_upwards [hae] with z hz
  rw [norm_mul, RCLike.norm_conj]
  have h1 := supSt_norm_mono_le a z hz
  have h2 := supSt_norm_mono_le b z hz
  nlinarith [norm_nonneg (monoC a z), norm_nonneg (monoC b z)]

theorem supSt_gram {D : ℕ} (a b : Fin (D + 1) → ℕ) :
    ∫ z, starRingEnd ℂ (monoC a z) * monoC b z ∂(sphProb (D + 1)) =
      if a = b then (monoNormSq a : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have hz : ∀ z, starRingEnd ℂ (monoC a z) * monoC a z = ((‖monoC a z‖ ^ 2 : ℝ) : ℂ) := by
      intro z
      rw [Complex.conj_mul']
      push_cast
      ring
    simp_rw [hz]
    rw [integral_complex_ofReal, integral_mono_sq_sphProb]
  · exact integral_mono_sphProb_of_ne h

theorem integral_form_sq (D n : ℕ) (c : (Fin (D + 1) → ℕ) → ℂ) :
    ∫ z, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a z‖ ^ 2 ∂(sphProb (D + 1)) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, ‖c a‖ ^ 2 * monoNormSq a := by
  set T := Finset.Nat.antidiagonalTuple (D + 1) n
  have key : ∀ z, ((‖∑ a ∈ T, c a * monoC a z‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ T, ∑ b ∈ T, (starRingEnd ℂ (c a) * c b) * (starRingEnd ℂ (monoC a z) * monoC b z) := by
    intro z
    push_cast
    rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  have hI : ∫ z, ‖∑ a ∈ T, c a * monoC a z‖ ^ 2 ∂(sphProb (D + 1)) =
      (∫ z, ((‖∑ a ∈ T, c a * monoC a z‖ ^ 2 : ℝ) : ℂ) ∂(sphProb (D + 1))).re := by
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have inner : ∀ a ∈ T, ∫ z, ∑ b ∈ T, (starRingEnd ℂ (c a) * c b) *
      (starRingEnd ℂ (monoC a z) * monoC b z) ∂(sphProb (D + 1)) =
      ((‖c a‖ ^ 2 * monoNormSq a : ℝ) : ℂ) := by
    intro a ha
    rw [integral_finset_sum _ (fun b _ => (supSt_integrable a b).const_mul _)]
    simp_rw [integral_const_mul, supSt_gram]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, ha, if_true]
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [hI]
  simp_rw [key]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => (supSt_integrable a b).const_mul _)),
    Finset.sum_congr rfl inner, ← Complex.ofReal_sum, Complex.ofReal_re]

theorem supSt_monoNormSq_pos {D : ℕ} (a : Fin (D + 1) → ℕ) : 0 < monoNormSq a := by
  unfold monoNormSq
  have : 0 < ∏ i, (a i).factorial := Finset.prod_pos fun i _ => Nat.factorial_pos _
  have h1 : (0 : ℝ) < ((∏ i, (a i).factorial : ℕ) : ℝ) := by exact_mod_cast this
  positivity

theorem form_sq_le (D n : ℕ) (c : (Fin (D + 1) → ℕ) → ℂ) (z : Fin (D + 1) → ℂ) :
    ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a z‖ ^ 2 ≤
      ((n + D).choose D : ℝ) * sqN z ^ n *
        ∫ w, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a w‖ ^ 2
          ∂(sphProb (D + 1)) := by
  set T := Finset.Nat.antidiagonalTuple (D + 1) n
  have hN : ∀ a : Fin (D + 1) → ℕ, 0 < Real.sqrt (monoNormSq a) := fun a => Real.sqrt_pos.mpr (supSt_monoNormSq_pos a)
  have h1 : ‖∑ a ∈ T, c a * monoC a z‖ ≤
      ∑ a ∈ T, (‖c a‖ * Real.sqrt (monoNormSq a)) * (‖monoC a z‖ / Real.sqrt (monoNormSq a)) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
    rw [norm_mul]
    field_simp [(hN a).ne']
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq T (fun a => ‖c a‖ * Real.sqrt (monoNormSq a))
    (fun a => ‖monoC a z‖ / Real.sqrt (monoNormSq a))
  have e1 : ∑ a ∈ T, (‖c a‖ * Real.sqrt (monoNormSq a)) ^ 2 = ∑ a ∈ T, ‖c a‖ ^ 2 * monoNormSq a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, Real.sq_sqrt (supSt_monoNormSq_pos a).le]
  have e2 : ∑ a ∈ T, (‖monoC a z‖ / Real.sqrt (monoNormSq a)) ^ 2 = ∑ a ∈ T, ‖monoC a z‖ ^ 2 / monoNormSq a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [div_pow, Real.sq_sqrt (supSt_monoNormSq_pos a).le]
  rw [e1, e2, sum_mono_sq_div] at h2
  rw [integral_form_sq]
  calc ‖∑ a ∈ T, c a * monoC a z‖ ^ 2
      ≤ (∑ a ∈ T, (‖c a‖ * Real.sqrt (monoNormSq a)) * (‖monoC a z‖ / Real.sqrt (monoNormSq a))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ a ∈ T, ‖c a‖ ^ 2 * monoNormSq a) * (((n + D).choose D : ℝ) * sqN z ^ n) := h2
    _ = ((n + D).choose D : ℝ) * sqN z ^ n * ∑ a ∈ T, ‖c a‖ ^ 2 * monoNormSq a := by ring

end ReciprocityTheory.GeometryOfNumbersTheory
end
