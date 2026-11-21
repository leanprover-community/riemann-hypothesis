import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LinIndToLp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.FixOfPerp

section
noncomputable section

open Matrix InnerProductSpace
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

variable {n m : ℕ}

theorem gram_det_zero (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : ¬ LinearIndependent ℂ w) :
    (GS.gram w).det = 0 := by
  rw [Fintype.not_linearIndependent_iff] at hw
  obtain ⟨g, hg, i, hi⟩ := hw
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨g, fun h => hi (congrFun h i), ?_⟩
  funext a
  simp only [mulVec, dotProduct, GS.gram, Matrix.of_apply, Pi.zero_apply]
  have hs : ∑ b, inner ℂ (w a) (w b) * g b = inner ℂ (w a) (∑ b, g b • w b) := by
    rw [inner_sum]
    congr 1
    funext b
    rw [inner_smul_right]
    ring
  rw [hs, hg, inner_zero_right]

theorem gram_re_det_le (v : Fin m → EuclideanSpace ℂ (Fin n)) (M : ℝ) (hM : ∀ j, ‖v j‖ ≤ M) :
    (GS.gram v).det.re ≤ (M ^ 2) ^ m := by
  by_cases hv : LinearIndependent ℂ v
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac v hv
    rw [det_gram_of v u τ hu hτ hwe, Complex.ofReal_re]
    have hτj : ∀ j, ‖τ j j‖ ≤ M := by
      intro j
      have h1 : inner ℂ (u j) (v j) = τ j j := by
        rw [hwe j]; exact hu.inner_right_fintype (fun b => τ b j) j
      rw [← h1]
      calc ‖inner ℂ (u j) (v j)‖ ≤ ‖u j‖ * ‖v j‖ := norm_inner_le_norm _ _
        _ = ‖v j‖ := by rw [hu.1 j, one_mul]
        _ ≤ M := hM j
    calc ∏ j, ‖τ j j‖ ^ 2 ≤ ∏ _j : Fin m, M ^ 2 :=
          Finset.prod_le_prod (fun j _ => by positivity) fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hτj j) 2
      _ = (M ^ 2) ^ m := by simp
  · rw [gram_det_zero v hv, Complex.zero_re]
    by_cases hm : m = 0
    · subst hm; simp
    · exact pow_nonneg (sq_nonneg M) m

end ReciprocityTheory.ChartRestriction.DS.Xi.GSB

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

def linA {k r : ℕ} (A : Mat k r) :
    EuclideanSpace ℂ (Fin (2 * r + k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
  (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.toLin' A ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap

theorem linA_apply {k r : ℕ} (A : Mat k r) (x : EuclideanSpace ℂ (Fin (2 * r + k + 1))) :
    linA A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

theorem gram_one {m n : ℕ} (u : Fin m → EuclideanSpace ℂ (Fin n)) (hu : Orthonormal ℂ u) : GS.gram u = 1 := by
  ext a b
  simp only [GS.gram, Matrix.of_apply, Matrix.one_apply]
  exact orthonormal_iff_ite.mp hu a b

theorem ga_mul_le (k r : ℕ) (A : Mat k r) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (gN A ^ 2) ^ (l.val + 1) * Ga k r l Y := by
  rw [ga_eq, ga_eq]
  set w : Fin (l.val + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    fun a => WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) with hwdef
  have hAw : (fun a : Fin (l.val + 1) =>
      (WithLp.toLp 2 (A *ᵥ Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) =
      fun a => linA A (w a) := by
    funext a; rw [linA_apply]
  rw [hAw]
  by_cases hw : LinearIndependent ℂ w
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac w hw
    have h1 : (fun a => linA A (w a)) = fun a => ∑ b, τ b a • linA A (u b) := by
      funext a; rw [hwe a, map_sum]; simp only [map_smul]
    have hgw : (GS.gram w).det = (τᴴ).det * τ.det := by
      rw [show w = (fun a => ∑ b, τ b a • u b) from funext hwe, gram_comb, gram_one u hu, Matrix.mul_one, det_mul]
    have hv : ∀ b, ‖linA A (u b)‖ ≤ gN A := by
      intro b
      have := norm_mulVec_le A (WithLp.ofLp (u b))
      rw [WithLp.toLp_ofLp, hu.1 b, mul_one] at this
      rw [linA_apply]; exact this
    have hle := gram_re_det_le (fun b => linA A (u b)) (gN A) hv
    have hX := det_gram_of w u τ hu hτ hwe
    rw [h1, gram_comb, det_mul, det_mul]
    have e1 : (τᴴ).det * (GS.gram fun b => linA A (u b)).det * τ.det =
        (GS.gram w).det * (GS.gram fun b => linA A (u b)).det := by rw [hgw]; ring
    rw [e1, hX, Complex.re_ofReal_mul]
    have hnn : (0 : ℝ) ≤ ∏ j, ‖τ j j‖ ^ 2 := Finset.prod_nonneg fun j _ => by positivity
    rw [Complex.ofReal_re, mul_comm]
    exact mul_le_mul_of_nonneg_right hle hnn
  · have hw' : ¬ LinearIndependent ℂ (fun a => linA A (w a)) := fun h => hw (h.of_comp (linA A))
    rw [gram_det_zero _ hw', gram_det_zero _ hw, Complex.zero_re, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Xi.GSB
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem H_es (k r : ℕ) (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  have ha := a.isLt
  funext i
  have hi := i.isLt
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega) | omega

theorem row_fix {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (a : Fin r)
    (j : Fin (2 * r + k + 1)) : h (eI k r a) j = if j = eI k r a then 1 else 0 := by
  obtain ⟨hU, hfix, -⟩ := hm
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have h1 : hᴴ *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
    have := congrArg (fun M => M *ᵥ bvec (esI k r a)) hU'
    simp only [← Matrix.mulVec_mulVec, (hfix a).2, H_es] at this
    exact this
  have h2 := congrFun h1 j
  simp only [bvec, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  have h3 := congrArg star h2
  rw [star_star] at h3
  rw [h3]
  split_ifs <;> simp

theorem row_apply {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (a : Fin r)
    (v : Fin (2 * r + k + 1) → ℂ) : (h *ᵥ v) (eI k r a) = v (eI k r a) := by
  simp only [Matrix.mulVec, dotProduct, row_fix hm a, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem inv_fix {k r : ℕ} {h : Mat k r} (hu : IsUnit h.det) {v : Fin (2 * r + k + 1) → ℂ} (hv : h *ᵥ v = v) :
    h⁻¹ *ᵥ v = v := by
  calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem conj_apply {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (n : Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : h⁻¹ *ᵥ v = v) (a : Fin r) :
    ((h * n * h⁻¹) *ᵥ v) (eI k r a) = (n *ᵥ v) (eI k r a) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, row_apply hm a]

theorem lam_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z)
    (hu : IsUnit h.det) (n : Mat k r) : lam k r z (h * n * h⁻¹) = lam k r z n := by
  have hent : ∀ (g : Mat k r) (i j : Fin (2 * r + k + 1)), g i j = (g *ᵥ bvec j) i := by
    intro g i j
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hz : h⁻¹ *ᵥ z = z := inv_fix hu hm.2.2
  have hell : ell k r z (h * n * h⁻¹) = ell k r z n := by
    unfold ell
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with hlt
    · rw [hent (h * n * h⁻¹), hent n]
      exact conj_apply hm n _ (inv_fix hu (hm.2.1 _).1) a
    · exact conj_apply hm n z hz a
  simp only [lam, hell]

end ReciprocityTheory.ChartRestriction.DS.Xi.XI

namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS ReciprocityTheory.ChartRestriction.DS.Xi.GSB

theorem ga_nonneg (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : 0 ≤ Ga k r l Y := by
  unfold Ga
  let M : Matrix (Fin (2 * r + k + 1)) (Fin (l.val + 1)) ℂ := fun i b => Y (Fin.castLE (by omega) b) i
  have key : 0 ≤ ((Mᴴ * M).det).re := by
    open scoped ComplexOrder in
    have h0 := Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self M).det_nonneg
    rw [Complex.zero_re] at h0
    exact h0.1
  convert key using 3
  ext a b
  first
    | rfl
    | (simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply, M]; rfl)

theorem rpow_bd (a b K s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 1 ≤ K) (hs : 0 ≤ s) (h1 : b ≤ K * a)
    (h2 : a ≤ K * b) : a ^ (-s) ≤ K ^ s * b ^ (-s) := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have hb0 : b = 0 := le_antisymm (by simpa using h1) hb
    subst hb0
    have h3 : 1 ≤ K ^ s := Real.one_le_rpow hK hs
    have h4 : 0 ≤ (0:ℝ) ^ (-s) := Real.rpow_nonneg le_rfl _
    nlinarith
  · have hbpos : 0 < b := by
      by_contra hc
      push_neg at hc
      nlinarith
    rw [Real.rpow_neg ha, Real.rpow_neg hb]
    have hbs : b ^ s ≤ K ^ s * a ^ s := by
      rw [← Real.mul_rpow (by linarith) ha]
      exact Real.rpow_le_rpow hb h1 hs
    have hapos : 0 < a ^ s := Real.rpow_pos_of_pos hpos s
    have hbpos' : 0 < b ^ s := Real.rpow_pos_of_pos hbpos s
    rw [← div_eq_mul_inv, inv_eq_one_div]
    first
      | (rw [div_le_div_iff_of_pos hapos hbpos']; linarith)
      | (rw [div_le_div_iff₀ hapos hbpos']; linarith)

theorem gN_nonneg {k r : ℕ} (g : Mat k r) : 0 ≤ gN g := Real.sqrt_nonneg _

theorem ga_two {k r : ℕ} (A : Mat k r) (K : ℝ) (hA : gN A ≤ K) (l : Fin (r + 1))
    (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (K ^ (l.val + 1)) ^ 2 * Ga k r l Y := by
  refine (ga_mul_le k r A l Y).trans (mul_le_mul_of_nonneg_right ?_ (ga_nonneg k r l Y))
  rw [← pow_mul, ← pow_mul, mul_comm]
  exact pow_le_pow_left₀ (gN_nonneg A) hA _

theorem xi_bd {k r : ℕ} (s : Fin (r + 1) → ℝ) (hs : ∀ l, 0 ≤ s l) (h : Mat k r) (hu : IsUnit h.det) (K : ℝ)
    (hK : 1 ≤ K) (h1 : gN h ≤ K) (h2 : gN h⁻¹ ≤ K) (m : Mat k r) :
    xiR k r s (h * m) ≤ (∏ l, (K ^ (l.val + 1)) ^ s l) * xiR k r s m := by
  unfold xiR
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro l _
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  · intro l _
    have hK0 : 0 ≤ K ^ (l.val + 1) := pow_nonneg (by linarith) _
    have hK' : 1 ≤ K ^ (l.val + 1) := one_le_pow₀ hK
    have e1 : Ga k r l (fun a => (h * m) *ᵥ phiV k r a) ≤
        (K ^ (l.val + 1)) ^ 2 * Ga k r l (fun a => m *ᵥ phiV k r a) := by
      have := ga_two h K h1 l (fun a => m *ᵥ phiV k r a)
      simp only [Matrix.mulVec_mulVec] at this
      exact this
    have e2 : Ga k r l (fun a => m *ᵥ phiV k r a) ≤
        (K ^ (l.val + 1)) ^ 2 * Ga k r l (fun a => (h * m) *ᵥ phiV k r a) := by
      have := ga_two h⁻¹ K h2 l (fun a => (h * m) *ᵥ phiV k r a)
      simp only [Matrix.mulVec_mulVec, ← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul] at this
      exact this
    have d1 : Del k r l (h * m) ≤ K ^ (l.val + 1) * Del k r l m := by
      have := Real.sqrt_le_sqrt e1
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0] at this
      exact this
    have d2 : Del k r l m ≤ K ^ (l.val + 1) * Del k r l (h * m) := by
      have := Real.sqrt_le_sqrt e2
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0] at this
      exact this
    exact rpow_bd _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hK' (hs l) d2 d1

theorem cont_gN {k r : ℕ} : Continuous (gN : Mat k r → ℝ) := by
  unfold gN
  refine Continuous.sqrt ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp (continuous_id.matrix_elem i j)

theorem cont_ga {k r : ℕ} (l : Fin (r + 1)) :
    Continuous fun x : Mt k r => Ga k r l (fun a => Matrix.of x *ᵥ phiV k r a) := by
  unfold Ga
  refine Complex.continuous_re.comp ?_
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun a b => ?_
  simp only [Matrix.of_apply]
  have hx : Continuous fun x : Mt k r => Matrix.of x := continuous_id
  first
    | exact ((hx.matrix_mulVec continuous_const).star).dotProduct (hx.matrix_mulVec continuous_const)
    | (simp only [dotProduct]; exact continuous_finset_sum _ fun i _ => ((continuous_apply i).comp (hx.matrix_mulVec continuous_const).star).mul ((continuous_apply i).comp (hx.matrix_mulVec continuous_const)))
    | (simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]; fun_prop)

theorem meas_xi (k r : ℕ) (s : Fin (r + 1) → ℝ) : Measurable fun x : Mt k r => xiN k r s (Matrix.of x) := by
  unfold xiN xiR
  refine Measurable.real_toNNReal ?_
  refine Finset.measurable_prod _ fun l _ => ?_
  refine Measurable.pow_const ?_ _
  exact ((cont_ga l).sqrt).measurable

end ReciprocityTheory.ChartRestriction.DS.Xi.XI
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.XI

namespace XI

private theorem lintegral_prod_le_lintegral_lintegral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α × β → ℝ≥0∞) :
    ∫⁻ p, f p ∂(μ.prod ν) ≤ ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  obtain ⟨g, hgm, hgle, hgeq⟩ := exists_measurable_le_lintegral_eq (μ.prod ν) f
  rw [hgeq]
  have e : μ.prod ν = Measure.bind μ (fun x => Measure.map (Prod.mk x) ν) := by
    first
      | exact Measure.prod_def μ ν
      | rw [Measure.prod_def]
      | rw [Measure.prod]
  rw [e]
  first
    | rw [Measure.bind, Measure.lintegral_join hgm.aemeasurable]
    | (unfold Measure.bind; rw [Measure.lintegral_join hgm.aemeasurable])
    | rw [Measure.bind, Measure.lintegral_join hgm]
  calc ∫⁻ m, ∫⁻ p, g p ∂m ∂(Measure.map (fun x => Measure.map (Prod.mk x) ν) μ)
      ≤ ∫⁻ x, ∫⁻ p, g p ∂(Measure.map (Prod.mk x) ν) ∂μ :=
        lintegral_map_le (fun m : Measure (α × β) => ∫⁻ p, g p ∂m) _
    _ ≤ ∫⁻ x, ∫⁻ y, g (x, y) ∂ν ∂μ := lintegral_mono fun x => lintegral_map_le g (Prod.mk x)
    _ ≤ ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
        lintegral_mono fun x => lintegral_mono fun y => hgle (x, y)

private theorem side {k r : ℕ} (s : Fin (r + 1) → ℝ) (hs : ∀ l, 0 ≤ s l) (z : Fin (2 * r + k + 1) → ℂ)
    (μW μN : Measure (Mt k r)) (hW : IsHaarOn (UWset k r z) μW)
    (hconj : ∀ h₀ ∈ UWset k r z, μN.map (conjM h₀) = μN) (hcomp : IsCompact (UWset k r z))
    (hcl : IsClosedSubgroup (UWset k r z)) (hI : IInt μN z s (1 / 2) < ∞) :
    (∫⁻ p : Mt k r × Mt k r, (xiN k r s (Matrix.of p.2 * Matrix.of p.1) : ℝ≥0∞) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂(μW.prod μN)) < ∞ := by
  obtain ⟨K₀, hK₀⟩ := hcomp.exists_bound_of_continuousOn (cont_gN (k := k) (r := r)).continuousOn
  obtain ⟨K, hK1, hKb⟩ : ∃ K : ℝ, 1 ≤ K ∧ ∀ g ∈ UWset k r z, gN g ≤ K := by
    refine ⟨max K₀ 1, le_max_right _ _, fun g hg => ?_⟩
    have h1 := hK₀ g hg
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  obtain ⟨C, hC0, hCeq⟩ : ∃ C : ℝ, 0 ≤ C ∧ C = ∏ l : Fin (r + 1), (K ^ (l.val + 1)) ^ s l :=
    ⟨_, Finset.prod_nonneg fun l _ => Real.rpow_nonneg (pow_nonneg (by linarith) _) _, rfl⟩
  have hlam : Continuous (fun m : Mt k r => lam k r z (Matrix.of m)) := by
    unfold lam ell
    refine Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_))
    split_ifs with ha
    · first
        | (simp only [Matrix.of_apply]; fun_prop)
        | fun_prop
        | exact (continuous_apply _).comp (continuous_apply _)
    · first
        | (simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]; fun_prop)
        | (simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply]; fun_prop)
        | exact (continuous_apply _).comp (Continuous.matrix_mulVec continuous_id continuous_const)
  have hWfin : μW Set.univ < ∞ := by
    have h2 : μW Set.univ ≤ μW (UWset k r z) + μW (UWset k r z)ᶜ := by
      first
        | exact measure_univ_le_add_compl _
        | (rw [← Set.union_compl_self (UWset k r z)]; exact measure_union_le _ _)
    rw [hW.conc, add_zero] at h2
    exact lt_of_le_of_lt h2 (hW.finite_compact _ hcomp)
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by
    rw [ae_iff]
    first
      | exact hW.conc
      | exact measure_mono_null (fun a ha => ha) hW.conc
  have hinner : ∀ h ∈ UWset k r z, (∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN) ≤
      ENNReal.ofReal C * IInt μN z s (1 / 2) := by
    intro h hh
    have hu : IsUnit h.det := hcl.unit h hh
    have hinv : h⁻¹ ∈ UWset k r z := hcl.inv_mem h hh
    have hu' : IsUnit h⁻¹.det := hcl.unit _ hinv
    have hii : h⁻¹⁻¹ = h := Matrix.nonsing_inv_nonsing_inv h hu
    have hcm : Measurable (conjM (k := k) (r := r) h⁻¹) := by
      apply Continuous.measurable
      first
        | exact continuous_pi fun i => continuous_pi fun j => by
            simp only [conjM, Matrix.mul_apply, Matrix.of_apply]; fun_prop
        | (unfold conjM; fun_prop)
        | (unfold conjM; exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    have hG : Measurable (fun m : Mt k r => ENNReal.ofReal (xiR k r s (Matrix.of m)) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) := by
      have hm1 : Measurable (fun m : Mt k r => ENNReal.ofReal (xiR k r s (Matrix.of m))) :=
        (meas_xi k r s).coe_nnreal_ennreal
      have hm2 : Measurable (fun m : Mt k r =>
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) :=
        ENNReal.measurable_ofReal.comp ((continuous_const.add hlam.abs).measurable.pow_const _)
      exact hm1.mul hm2
    have hpt : ∀ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) := by
      intro n
      have e : Matrix.of (conjM h⁻¹ n) = h⁻¹ * Matrix.of n * h := by
        show h⁻¹ * Matrix.of n * h⁻¹⁻¹ = _
        rw [hii]
      have hl : lam k r z (h⁻¹ * Matrix.of n * h) = lam k r z (Matrix.of n) := by
        have := lam_conj hinv hu' (Matrix.of n)
        rwa [hii] at this
      have hxi : xiR k r s (Matrix.of n * h) ≤ C * xiR k r s (h⁻¹ * Matrix.of n * h) := by
        have := xi_bd s hs h hu K hK1 (hKb h hh) (hKb h⁻¹ hinv) (h⁻¹ * Matrix.of n * h)
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
          Matrix.one_mul] at this
        rw [hCeq]
        exact this
      have hw : (1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ)) ≤
          (1 + |lam k r z (Matrix.of n)|) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (lam k r z (Matrix.of n))])
          (by norm_num)
      rw [e, hl, ← mul_assoc, ← ENNReal.ofReal_mul hC0]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hxi) (ENNReal.ofReal_le_ofReal hw)
    calc (∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN)
        ≤ ∫⁻ n : Mt k r, ENNReal.ofReal C * (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) ∂μN :=
          lintegral_mono hpt
      _ = ENNReal.ofReal C * ∫⁻ n : Mt k r, (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) ∂μN :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C * ∫⁻ m : Mt k r, (ENNReal.ofReal (xiR k r s (Matrix.of m)) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) ∂(μN.map (conjM h⁻¹)) := by
          rw [lintegral_map hG hcm]
      _ = ENNReal.ofReal C * IInt μN z s (1 / 2) := by
          rw [hconj h⁻¹ hinv]
          try rfl
  calc (∫⁻ p : Mt k r × Mt k r, (xiN k r s (Matrix.of p.2 * Matrix.of p.1) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂(μW.prod μN))
      ≤ ∫⁻ x : Mt k r, ∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * Matrix.of x) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN ∂μW :=
        lintegral_prod_le_lintegral_lintegral μW μN _
    _ ≤ ∫⁻ _x : Mt k r, ENNReal.ofReal C * IInt μN z s (1 / 2) ∂μW :=
        lintegral_mono_ae (hae.mono fun x hx => hinner (Matrix.of x) hx)
    _ = ENNReal.ofReal C * IInt μN z s (1 / 2) * μW Set.univ := lintegral_const _
    _ < ∞ := by
        first
          | exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI) hWfin
          | exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_ne_top hI.ne) hWfin.ne

end XI

theorem xiIntH (hB2 : InductiveHeisenbergInputs) : XiIntStep := by
  unfold InductiveHeisenbergInputs at hB2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hCI, hCW, -, -, -, -, -, -, -, hClW, -, -, -, -, -⟩ := hB2
  intro k r Wp Wq _ _ _ _ _ _ D s hs hI hI'
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hs0 : ∀ l, 0 ≤ s l := by
    intro l
    have h1 := (hs l).2
    have h2 : (1 : ℝ) ≤ s0 k r l := by
      unfold s0
      split_ifs <;> linarith
    linarith
  unfold XiInt
  refine ⟨XI.meas_xi k r s, ?_, ?_⟩
  · exact XI.side s hs0 D.z D.μW D.μN D.haarW
      (fun h₀ hh => hCI k r Wp Wq D h₀ (Set.mem_union_left _ hh))
      (hCW k r D.z D.z_mem D.T_pos) (hClW k r D.z) hI
  · exact XI.side s hs0 D.z' D.μW' D.μN D.haarW'
      (fun h₀ hh => hCI k r Wp Wq D h₀ (Set.mem_union_right _ hh))
      (hCW k r D.z' D.z'_mem D.T'_pos) (hClW k r D.z') hI'

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

theorem exists_K (hk : 1 ≤ k) (c u : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0) :
    ∃ κL : EE k r ≃ₗᵢ[ℂ] EE k r, (∀ a, κL (c a) = u a) ∧ ∀ x, κL (HE k r x) = HE k r (κL x) := by
  have hF : ∀ w : Fin (r + 1) → EE k r, Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) →
      Orthonormal ℂ (Sum.elim w (fun a => HE k r (w a))) := by
    intro w hw hwi
    rw [orthonormal_iff_ite] at hw ⊢
    rintro (a | a) (b | b)
    · simp [hw]
    · simp [hwi]
    · simp [HE_adj, hwi]
    · simp [HE_adj, HE_HE, hw]
  have hcard : Module.finrank ℂ (EE k r) = Fintype.card ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) := by
    simp; omega
  have hres : ∀ w : Fin (r + 1) ⊕ Fin (r + 1) → EE k r, Orthonormal ℂ w →
      Orthonormal ℂ ((Set.range (Sum.inl : _ → (Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1))).restrict
        (Sum.elim w 0)) := by
    intro w hw
    rw [orthonormal_iff_ite] at hw ⊢
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    change inner ℂ (w p) (w q) = _
    rw [hw p q]
    by_cases hpq : p = q
    · subst hpq; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hpq, if_neg]; intro h; exact hpq (Sum.inl_injective (congrArg Subtype.val h))
  obtain ⟨bP, hbP⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF c hc hci))
  obtain ⟨bQ, hbQ⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF u hu hui))
  have hP : ∀ p, bP (Sum.inl p) = Sum.elim c (fun a => HE k r (c a)) p := fun p => hbP _ ⟨p, rfl⟩
  have hQ : ∀ p, bQ (Sum.inl p) = Sum.elim u (fun a => HE k r (u a)) p := fun p => hbQ _ ⟨p, rfl⟩
  set κL := bP.repr.trans bQ.repr.symm with hκL
  have hκb : ∀ i, κL (bP i) = bQ i := fun i => by simp [hκL]
  have hc1 : ∀ a, κL (c a) = u a := fun a => by
    have := hκb (Sum.inl (Sum.inl a)); rwa [hP, hQ] at this
  have hc2 : ∀ a, κL (HE k r (c a)) = HE k r (u a) := fun a => by
    have := hκb (Sum.inl (Sum.inr a)); rwa [hP, hQ] at this
  have hfix : ∀ (b : OrthonormalBasis ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) ℂ (EE k r))
      (w : Fin (r + 1) → EE k r), Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) →
      (∀ p, b (Sum.inl p) = Sum.elim w (fun a => HE k r (w a)) p) →
      ∀ j, HE k r (b (Sum.inr j)) = b (Sum.inr j) := by
    intro b w hw hwi hb j
    refine fix_of_perp w hw hwi _ (fun a => ?_) (fun a => ?_)
    · have := hb (Sum.inl a); simp only [Sum.elim_inl] at this
      rw [← this]; exact b.orthonormal.2 (by simp)
    · have := hb (Sum.inr a); simp only [Sum.elim_inr] at this
      rw [← this]; exact b.orthonormal.2 (by simp)
  refine ⟨κL, hc1, fun x => ?_⟩
  have key : (κL.toLinearEquiv.toLinearMap).comp (HE k r) = (HE k r).comp κL.toLinearEquiv.toLinearMap := by
    refine bP.toBasis.ext fun i => ?_
    simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rcases i with (a | a) | j
    · rw [hP, Sum.elim_inl, hc2, hc1]
    · rw [hP, Sum.elim_inr, HE_HE, hc1, hc2, HE_HE]
    · rw [hfix bP c hc hci hP j, hκb, hfix bQ u hu hui hQ j]
  simpa using LinearMap.congr_fun key x

theorem exists_Kmat (hk : 1 ≤ k) (c u : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0) :
    ∃ κ ∈ Kset k r, ∀ a, (WithLp.toLp 2 (κ *ᵥ (c a).ofLp) : EE k r) = u a := by
  obtain ⟨κL, hκc, hκH⟩ := exists_K hk c u hc hu hci hui
  set κ : Mat k r := Matrix.toEuclideanLin.symm κL.toLinearEquiv.toLinearMap with hκdef
  have hκ : ∀ v, (WithLp.toLp 2 (κ *ᵥ v) : EE k r) = κL (WithLp.toLp 2 v) := by
    intro v
    have h1 : Matrix.toEuclideanLin κ = κL.toLinearEquiv.toLinearMap := LinearEquiv.apply_symm_apply _ _
    have := LinearMap.congr_fun h1 (WithLp.toLp 2 v)
    rw [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp] at this
    exact this
  have hunit : κᴴ * κ = 1 := by
    ext i j
    have h2 : inner ℂ (WithLp.toLp 2 (κ *ᵥ Pi.single i 1) : EE k r) (WithLp.toLp 2 (κ *ᵥ Pi.single j 1)) =
        inner ℂ (WithLp.toLp 2 (Pi.single i 1) : EE k r) (WithLp.toLp 2 (Pi.single j 1)) := by
      rw [hκ, hκ, LinearIsometryEquiv.inner_map_map]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct] at h2
    simp only [mul_apply, conjTranspose_apply, one_apply]
    convert h2 using 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      simp [mulVec_single, mul_comm]
    · simp [Pi.single_apply, eq_comm]
  have hv : ∀ v, κ *ᵥ (Hpk k r *ᵥ v) = Hpk k r *ᵥ (κ *ᵥ v) := by
    intro v
    have := hκH (WithLp.toLp 2 v)
    rw [HE_apply, WithLp.ofLp_toLp, ← hκ, ← hκ, HE_apply, WithLp.ofLp_toLp] at this
    simpa using congrArg WithLp.ofLp this
  have hcomm : κ * Hpk k r = Hpk k r * κ := by
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    rw [mulVec_mulVec, mulVec_mulVec] at this
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  refine ⟨κ, ⟨?_, hunit⟩, fun a => ?_⟩
  · show κᴴ * Hpk k r * κ = Hpk k r
    rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
  · rw [hκ, WithLp.toLp_ofLp, hκc]

theorem inner_bvec (i : Fin (2 * r + k + 1)) (v : Fin (2 * r + k + 1) → ℂ) :
    inner ℂ (WithLp.toLp 2 (bvec i) : EE k r) (WithLp.toLp 2 v) = v i := by
  first
    | (simp [bvec, PiLp.inner_apply, Pi.single_apply])
    | (show inner ℂ (EuclideanSpace.single i (1 : ℂ)) (WithLp.toLp 2 v : EE k r) = v i
       rw [EuclideanSpace.inner_single_left]; simp)

theorem phiV_apply (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    phiV k r b i = if b.val < r then (if i.val = 2 * r + k - b.val then 1 else 0) else
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) + (if i.val = r + k then 1 else 0)) := by
  unfold phiV
  by_cases hb : (b : ℕ) < r
  · rw [dif_pos hb, if_pos hb]
    show (Pi.single (esI k r ⟨b.val, hb⟩) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = _
    rw [Pi.single_apply]
    by_cases hi : (i : ℕ) = 2 * r + k - b.val
    · rw [if_pos hi, if_pos (show i = esI k r ⟨b.val, hb⟩ from Fin.ext hi)]
    · rw [if_neg hi, if_neg (show ¬ i = esI k r ⟨b.val, hb⟩ from fun h => hi (congrArg Fin.val h))]
  · rw [dif_neg hb, if_neg hb]
    simp [epsV, bvec, Pi.single_apply, Fin.ext_iff]
    have e1 : ((wI k r 0 : Fin (2 * r + k + 1)) : ℕ) = r := by first | rfl | simp [wI]
    have e2 : ((wI k r (Fin.last k) : Fin (2 * r + k + 1)) : ℕ) = r + k := by first | rfl | simp [wI]
    rw [e1, e2]

theorem toLp_phiV (a : Fin (r + 1)) : (WithLp.toLp 2 (phiV k r a) : EE k r) =
    if a.val < r then WithLp.toLp 2 (bvec ⟨2 * r + k - a.val, by omega⟩) else
      ((Real.sqrt 2)⁻¹ : ℂ) • (WithLp.toLp 2 (bvec ⟨r, by omega⟩) + WithLp.toLp 2 (bvec ⟨r + k, by omega⟩)) := by
  ext i
  by_cases ha : a.val < r
  · simp [ha, phiV_apply, bvec, Pi.single_apply, Fin.ext_iff]
  · simp [ha, phiV_apply, bvec, Pi.single_apply, Fin.ext_iff, mul_add, mul_ite]

theorem hcc : star ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    first
      | (rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _)
      | simp
  rw [hs, ← mul_inv, h2]; norm_num

theorem qe_orth (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV k r a) : EE k r)) := by
  have key : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := hcc
  rw [orthonormal_iff_ite]
  intro a b
  have hA := a.isLt
  have hB := b.isLt
  rw [toLp_phiV]
  by_cases ha : a.val < r
  · rw [if_pos ha, inner_bvec, phiV_apply]
    split_ifs <;> first
      | rfl
      | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)
      | simp
  · rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, phiV_apply, phiV_apply]
    split_ifs <;> first
      | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)
      | (exfalso; exact ‹¬a = b› (Fin.ext (by omega)))
      | (exfalso; simp_all; done)
      | (exfalso; simp_all <;> omega)
      | (simp; done)
      | (simp only [add_zero, zero_add, mul_one]; linear_combination (2 : ℂ) * key)

end ReciprocityTheory.ChartRestriction.DS.Xi.GS
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

theorem pe_eq (a : Fin (r + 1)) :
    (WithLp.toLp 2 (phiV' k r a) : EE k r) = HE k r (WithLp.toLp 2 (phiV k r a)) := by
  rw [HE_apply, WithLp.ofLp_toLp]; rfl

theorem pe_orth (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV' k r a) : EE k r)) := by
  have h := qe_orth (k := k) (r := r) hk
  rw [orthonormal_iff_ite] at h ⊢
  intro a b; simp only [pe_eq, HE_adj, HE_HE]; exact h a b

theorem pe_iso (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    inner ℂ (WithLp.toLp 2 (phiV' k r a) : EE k r) (HE k r (WithLp.toLp 2 (phiV' k r b))) = 0 := by
  rw [pe_eq, pe_eq, HE_HE, HE_adj, HE_apply, WithLp.ofLp_toLp, toLp_phiV a]
  by_cases ha : a.val < r
  · rw [if_pos ha, inner_bvec, hpk_mulVec, phiV_apply]
    simp only [sigI_val, sgnI]
    split_ifs <;> first | rfl | (exfalso; omega) | simp
  · rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, hpk_mulVec, hpk_mulVec,
      phiV_apply, phiV_apply]
    simp only [sigI_val, sgnI, starRingEnd_apply]
    split_ifs <;> first | rfl | (exfalso; omega) | ring | simp

theorem phiV'_linInd' (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) :=
  (pe_orth hk).linearIndependent.map' (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap
    (LinearEquiv.ker _)

theorem phiV'_iso' (hk : 1 ≤ k) (a b : Fin (r + 1)) : herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := by
  rw [herm_eq]; exact pe_iso hk b a

theorem sum_castLE {M : Type*} [AddCommMonoid M] {l : ℕ} (h : l + 1 ≤ r + 1) (f : Fin (r + 1) → M)
    (hf : ∀ b : Fin (r + 1), l < b.val → f b = 0) :
    ∑ b, f b = ∑ b : Fin (l + 1), f (Fin.castLE h b) := by
  rw [show (∑ b : Fin (l + 1), f (Fin.castLE h b)) = ∑ b ∈ Finset.univ.map (Fin.castLEEmb h), f b by rw [Finset.sum_map]; rfl]
  refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => hf b ?_).symm
  by_contra hcon
  exact hb (Finset.mem_map.2 ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem prod_Iic_castLE (l : Fin (r + 1)) (g : Fin (r + 1) → ℝ) :
    ∏ j ∈ Finset.Iic l, g j = ∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j) := by
  rw [show (∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j)) =
      ∏ j ∈ Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)), g j by
    rw [Finset.prod_map]; rfl]
  congr 1
  ext j
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro hj; exact ⟨⟨j.val, by rw [Fin.le_def] at hj; omega⟩, Fin.ext rfl⟩
  · rintro ⟨b, rfl⟩; rw [Fin.le_def]; simp; omega

theorem iw_core (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (hk : 1 ≤ k)
    (hY : LinearIndependent ℂ Y) (hiso : ∀ a b, herm (Hpk k r) (Y a) (Y b) = 0) :
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ j, τ j j ≠ 0) ∧ (∀ a, Y a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l Y := by
  obtain ⟨u, τ, hu, hτ, hd, hwe, hspan⟩ := gs_fac (fun a => (WithLp.toLp 2 (Y a) : EE k r)) (linInd_toLp Y hY)
  have hwi : ∀ a b, inner ℂ (WithLp.toLp 2 (Y a) : EE k r) (HE k r (WithLp.toLp 2 (Y b))) = 0 :=
    fun a b => by rw [← herm_eq]; exact hiso b a
  have hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0 := by
    intro a b
    obtain ⟨ca, hca⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan a)
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan b)
    rw [← hca, ← hcb, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, inner_smul_left, inner_smul_right, hwi, mul_zero, mul_zero]
  obtain ⟨κ, hκK, hκ⟩ := exists_Kmat hk _ u (pe_orth hk) hu (fun a b => pe_iso hk a b) hui
  have hκ' : ∀ b, u b = WithLp.toLp 2 (κ *ᵥ phiV' k r b) := fun b => (hκ b).symm
  refine ⟨κ, hκK, τ, hτ, hd, fun a => ?_, fun l => ?_⟩
  · have h1 : (WithLp.toLp 2 (Y a) : EE k r) = ∑ b, τ b a • (WithLp.toLp 2 (κ *ᵥ phiV' k r b) : EE k r) := by
      rw [hwe a]; simp only [hκ']
    have h2 := congrArg (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)) h1
    rw [map_sum] at h2
    simpa using h2
  · rw [ga_eq]
    have hle : l.val + 1 ≤ r + 1 := by omega
    have hsub : ∀ a : Fin (l.val + 1), (WithLp.toLp 2 (Y (Fin.castLE hle a)) : EE k r) =
        ∑ b : Fin (l.val + 1), (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)) b a • u (Fin.castLE hle b) := by
      intro a
      rw [hwe (Fin.castLE hle a)]
      refine sum_castLE hle _ fun b hb => ?_
      have hlt : Fin.castLE hle a < b := by
        rw [Fin.lt_def, Fin.val_castLE]; have := a.isLt; omega
      rw [show τ b (Fin.castLE hle a) = 0 from hτ hlt, zero_smul]
    have hτl : (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)).BlockTriangular id :=
      fun i j hij => hτ (show Fin.castLE hle j < Fin.castLE hle i from hij)
    have hdet := det_gram_of (fun a : Fin (l.val + 1) => (WithLp.toLp 2 (Y (Fin.castLE hle a)) : EE k r))
      (fun b => u (Fin.castLE hle b)) (τ.submatrix (Fin.castLE hle) (Fin.castLE hle))
      (hu.comp _ (Fin.castLE_injective hle)) hτl hsub
    rw [hdet, Complex.ofReal_re, prod_Iic_castLE]
    rfl

end ReciprocityTheory.ChartRestriction.DS.Xi.GS

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem phiV'_linInd (k r : ℕ) (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) := GS.phiV'_linInd' hk

theorem phiV'_iso (k r : ℕ) (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := GS.phiV'_iso' hk a b

theorem iwB : IW := fun k r Y hk hY hiso => by
  obtain ⟨κ, hκ, τ, h1, -, h3, h4⟩ := GS.iw_core Y hk hY hiso
  exact ⟨κ, hκ, τ, h1, h3, h4⟩

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem herm_UH' [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : g ∈ UH H) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm H u v := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hg']

theorem herm_sum_l {α : Type*} (c : α → ℂ) (s : Finset α) (u : α → ι → ℂ) (w : ι → ℂ) :
    herm H (∑ j ∈ s, c j • u j) w = ∑ j ∈ s, c j * herm H (u j) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [herm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul]

theorem herm_sum_r {α : Type*} (c : α → ℂ) (s : Finset α) (u : ι → ℂ) (w : α → ι → ℂ) :
    herm H u (∑ j ∈ s, c j • w j) = ∑ j ∈ s, star (c j) * herm H u (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [herm, star_add, star_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem mat_eq_of_mulVec' [DecidableEq ι] {A B : Matrix ι ι ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h v])

end herm

section hpk
variable (k r : ℕ)

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [Matrix.mulVec, dotProduct, hpk_out k r h]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro j _ hj
      have hj' : j.val ≠ 2 * r + k - i.val := fun hc => hj (Fin.ext hc)
      simp [hj']
    · simp
  · rw [if_neg h]
    simp only [Matrix.mulVec, dotProduct, hpk_mid k r h]
    rw [Finset.sum_eq_single i]
    · by_cases h2 : i.val = r + k <;> simp [h2]
    · intro j _ hj
      have hj' : j.val ≠ i.val := fun hc => hj (Fin.ext hc)
      simp [hj']
    · simp

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  rw [hpk_mulVec]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, hpk_mulVec, if_pos (by dsimp only; omega)]
    congr 1
    ext
    dsimp only
    omega
  · rw [if_neg h]
    split_ifs with h2
    · rw [hpk_mulVec, if_neg h, if_pos h2, neg_neg]
    · rw [hpk_mulVec, if_neg h, if_neg h2]

theorem hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec' fun v => by rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec]

variable {k r}

theorem uh_inv_mul {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hpk_sq]
  rw [Matrix.inv_eq_left_inv hl, hl]

theorem uh_mul_inv {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (uh_inv_mul hg))

theorem herm_inv {x : Mat k r} (hx : x ∈ GV k r) (g : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((x⁻¹ * g) *ᵥ v) w = herm (Hpk k r) (g *ᵥ v) (x *ᵥ w) := by
  rw [← herm_UH' (Hpk k r) hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, uh_mul_inv hx,
    Matrix.one_mul]

end hpk

section tri

theorem sub_mul_tri {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (A * B).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE h) (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hemb : ∑ l : Fin m, A (Fin.castLE h i) (Fin.castLE h l) * B (Fin.castLE h l) (Fin.castLE h j) =
      ∑ l ∈ Finset.univ.map (Fin.castLEEmb h), A (Fin.castLE h i) l * B l (Fin.castLE h j) := by
    rw [Finset.sum_map]
    rfl
  rw [hemb]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro l _ hl
  have hlm : m ≤ l.val := by
    by_contra hc
    push_neg at hc
    exact hl (Finset.mem_map.mpr ⟨⟨l.val, hc⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hjl : id (Fin.castLE h j) < id l := by
    show (Fin.castLE h j).val < l.val
    have := j.isLt
    simp only [Fin.coe_castLE]
    omega
  rw [hB hjl, mul_zero]

theorem sub_tri_mul {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (Bᴴ * A).submatrix (Fin.castLE h) (Fin.castLE h) =
      (B.submatrix (Fin.castLE h) (Fin.castLE h))ᴴ * A.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hemb : ∑ l : Fin m, star (B (Fin.castLE h l) (Fin.castLE h i)) * A (Fin.castLE h l) (Fin.castLE h j) =
      ∑ l ∈ Finset.univ.map (Fin.castLEEmb h), star (B l (Fin.castLE h i)) * A l (Fin.castLE h j) := by
    rw [Finset.sum_map]
    rfl
  rw [hemb]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro l _ hl
  have hlm : m ≤ l.val := by
    by_contra hc
    push_neg at hc
    exact hl (Finset.mem_map.mpr ⟨⟨l.val, hc⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hil : id (Fin.castLE h i) < id l := by
    show (Fin.castLE h i).val < l.val
    have := i.isLt
    simp only [Fin.coe_castLE]
    omega
  rw [hB hil, star_zero, zero_mul]

theorem tri_sub {n m : ℕ} (h : m ≤ n) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (B.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id :=
  fun i j hij => hB (show (Fin.castLE h j).val < (Fin.castLE h i).val from hij)

end tri

section dl
variable {k r : ℕ}

def Pm (k r : ℕ) (g : Mat k r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun a b => herm (Hpk k r) (g *ᵥ phiV' k r b) (phiV' k r a)

def cl (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : Fin (r + 1)) : ℝ≥0 :=
  ∏ j : Fin (l.val + 1), ‖τ (Fin.castLE (show l.val + 1 ≤ r + 1 by omega) j)
    (Fin.castLE (show l.val + 1 ≤ r + 1 by omega) j)‖₊

theorem dl_eq (l : Fin (r + 1)) (g : Mat k r) :
    Dl k r l g = ((Pm k r g).submatrix (Fin.castLE (show l.val + 1 ≤ r + 1 by omega))
      (Fin.castLE (show l.val + 1 ≤ r + 1 by omega))).det := rfl

theorem pm_left {x κ : Mat k r} (hx : x ∈ GV k r) (hκ : κ ∈ GV k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hY : ∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) (g : Mat k r) :
    Pm k r (x⁻¹ * g) = τᴴ * Pm k r (κ⁻¹ * g) := by
  ext a b
  simp only [Pm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [herm_inv hx, hY a, herm_sum_r]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [herm_inv hκ]

theorem pm_right {y κ : Mat k r} (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hY : ∀ a, y *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) (g : Mat k r) :
    Pm k r (g * y) = Pm k r (g * κ) * τ := by
  ext a b
  simp only [Pm, Matrix.of_apply, Matrix.mul_apply]
  have e : (g * y) *ᵥ phiV' k r b = ∑ c, τ c b • ((g * κ) *ᵥ phiV' k r c) := by
    rw [← Matrix.mulVec_mulVec, hY b, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rw [e, herm_sum_l]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem dl_left {x κ : Mat k r} (hx : x ∈ GV k r) (hκ : κ ∈ GV k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (hY : ∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b))
    (g : Mat k r) (l : Fin (r + 1)) : ‖Dl k r l (x⁻¹ * g)‖₊ = cl τ l * ‖Dl k r l (κ⁻¹ * g)‖₊ := by
  rw [dl_eq, dl_eq, pm_left hx hκ τ hY, sub_tri_mul _ _ _ hτ, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.det_of_upperTriangular (tri_sub _ τ hτ), nnnorm_mul,
    nnnorm_star, nnnorm_prod]
  rfl

theorem dl_right {y κ : Mat k r} (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (hY : ∀ a, y *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b))
    (g : Mat k r) (l : Fin (r + 1)) : ‖Dl k r l (g * y)‖₊ = cl τ l * ‖Dl k r l (g * κ)‖₊ := by
  rw [dl_eq, dl_eq, pm_right τ hY, sub_mul_tri _ _ _ hτ, Matrix.det_mul,
    Matrix.det_of_upperTriangular (tri_sub _ τ hτ), nnnorm_mul, nnnorm_prod, mul_comm]
  rfl

theorem fsE_fac (s : Fin (r + 1) → ℝ) (g1 g2 : Mat k r) (c : Fin (r + 1) → ℝ≥0)
    (h : ∀ l, ‖Dl k r l g1‖₊ = c l * ‖Dl k r l g2‖₊) :
    FsE k r s g1 = (∏ l, ((c l : ℝ≥0∞)) ^ (-s l)) * FsE k r s g2 := by
  unfold FsE
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [h l, ENNReal.coe_mul, ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]

end dl

end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section fs
variable {k r : ℕ}

theorem iic_eq (l : Fin (r + 1)) :
    Finset.Iic l = Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)) := by
  ext c
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and, Fin.le_def]
  constructor
  · intro hc; exact ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩
  · rintro ⟨a, rfl⟩
    have := a.isLt
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    omega

theorem ofReal_fsR (s : Fin (r + 1) → ℝ) (x : Mat k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hGa : ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l (fun a => x *ᵥ phiV' k r a))
    (hpos : ∀ l, 0 < Ga k r l (fun a => x *ᵥ phiV' k r a)) :
    ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  unfold fsR
  rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hpos l).le _)]
  refine Finset.prod_congr rfl fun l _ => ?_
  have ht : Ga k r l (fun a => x *ᵥ phiV' k r a) = ((cl τ l : ℝ)) ^ 2 := by
    rw [← hGa l, iic_eq, Finset.prod_map, Finset.prod_pow, cl, NNReal.coe_prod]
    rfl
  have hc : 0 < (cl τ l : ℝ) := by
    have h0 := hpos l
    rw [ht] at h0
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (fun he => by rw [← he] at h0; simp at h0)
  rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← ENNReal.ofReal_rpow_of_pos hc,
    ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  ring

theorem xphi_linInd (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    LinearIndependent ℂ (fun a => x *ᵥ phiV' k r a) := by
  have hinj : Function.Injective (Matrix.mulVecLin x) := fun u v huv => by
    have h2 := congrArg (fun w => x⁻¹ *ᵥ w) huv
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, uh_inv_mul hx] using h2
  exact (phiV'_linInd k r hk).map' (Matrix.mulVecLin x) (LinearMap.ker_eq_bot.2 hinj)

theorem iw_at (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ s, ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hGa⟩ := hIW k r (fun a => x *ᵥ phiV' k r a) hk (xphi_linInd hk hx)
    (fun a b => by rw [herm_UH' _ hx]; exact phiV'_iso k r hk a b)
  exact ⟨κ, hκ, τ, hτ, hY, fun s => ofReal_fsR s x τ hGa (fun l => GS.ga_pos k r _ (xphi_linInd hk hx) l)⟩

theorem fsE_left (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (x⁻¹ * g) = ENNReal.ofReal (fsR k r s x) * FsE k r s (κ⁻¹ * g) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hf⟩ := iw_at hIW hk hx
  refine ⟨κ, hκ, fun s g => ?_⟩
  rw [hf s]
  exact fsE_fac s _ _ _ (dl_left hx hκ.1 τ hτ hY g)

theorem fsE_right (hIW : IW) (hk : 1 ≤ k) {y : Mat k r} (hy : y ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (g * y) = ENNReal.ofReal (fsR k r s y) * FsE k r s (g * κ) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hf⟩ := iw_at hIW hk hy
  refine ⟨κ, hκ, fun s g => ?_⟩
  rw [hf s]
  exact fsE_fac s _ _ _ (dl_right τ hτ hY g)

theorem fsR_nonneg {k r : ℕ} (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) (s : Fin (r + 1) → ℝ) :
    0 ≤ fsR k r s x :=
  Finset.prod_nonneg fun l _ => Real.rpow_nonneg (GS.ga_pos k r _ (xphi_linInd hk hx) l).le _

end fs

section meas
variable {k r : ℕ}

theorem cont_lmul (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) :=
  Continuous.matrix_mul continuous_const continuous_id

theorem cont_rmul (a : Mat k r) : Continuous (rmulF a : Mt k r → Mt k r) :=
  Continuous.matrix_mul continuous_id continuous_const

def lmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv g := by
    show a⁻¹ * (a * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_inv_mul ha, Matrix.one_mul]; rfl
  right_inv g := by
    show a * (a⁻¹ * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_mul_inv ha, Matrix.one_mul]; rfl
  measurable_toFun := (cont_lmul a).measurable
  measurable_invFun := (cont_lmul a⁻¹).measurable

def rmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulF a
  invFun := rmulF a⁻¹
  left_inv g := by
    show Matrix.of g * a * a⁻¹ = g
    rw [Matrix.mul_assoc, uh_mul_inv ha, Matrix.mul_one]; rfl
  right_inv g := by
    show Matrix.of g * a⁻¹ * a = g
    rw [Matrix.mul_assoc, uh_inv_mul ha, Matrix.mul_one]; rfl
  measurable_toFun := (cont_rmul a).measurable
  measurable_invFun := (cont_rmul a⁻¹).measurable

theorem lmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (lmulM a g) ∂μ = ∫⁻ g, f g ∂μ := by
  have h := lintegral_map_equiv f (lmulE ha) (μ := μ)
  rw [show ⇑(lmulE ha) = lmulM a from rfl, hμ.left a ha] at h
  exact h.symm

theorem rmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (rmulF a g) ∂μ = ∫⁻ g, f g ∂μ := by
  have h := lintegral_map_equiv f (rmulE ha) (μ := μ)
  rw [show ⇑(rmulE ha) = rmulF a from rfl, hμ.right a ha] at h
  exact h.symm

end meas

end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B HermitianLiftIdentities

theorem tLeftH (hIW : IW) (hB2 : InductiveHeisenbergInputs) : TLeft := by
  intro k r s μG Φ hk hμ _ hK x hx
  obtain ⟨κ, hκ, hF⟩ := fsE_left hIW hk hx
  have h1 : ∀ g : Mt k r, κ⁻¹ * Matrix.of (lmulM κ g) = Matrix.of g := fun g => by
    show κ⁻¹ * (κ * Matrix.of g) = Matrix.of g
    rw [← Matrix.mul_assoc, uh_inv_mul hκ.1, Matrix.one_mul]
  calc ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG
      = ∫⁻ g, ENNReal.ofReal (fsR k r s x) * (Φ g * FsE k r s (κ⁻¹ * Matrix.of g)) ∂μG := by
        refine lintegral_congr fun g => ?_
        rw [hF s]; ring
    _ = ENNReal.ofReal (fsR k r s x) * ∫⁻ g, Φ g * FsE k r s (κ⁻¹ * Matrix.of g) ∂μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
        rw [← lmul_int hκ.1 hμ (fun g => Φ g * FsE k r s (κ⁻¹ * Matrix.of g))]
        refine congrArg _ (lintegral_congr fun g => ?_)
        simp only [hK κ hκ g, h1]

theorem tBothH (hIW : IW) (hB2 : InductiveHeisenbergInputs) : TBoth := by
  intro k r s μG Φ hk hμ hΦ hK x hx y hy
  obtain ⟨κ, hκ, hF⟩ := fsE_right hIW hk hy
  have hL := tLeftH hIW hB2 k r s μG Φ hk hμ hΦ (fun κ hκ g => (hK κ hκ g).1) x hx
  have h1 : ∀ g : Mt k r, x⁻¹ * Matrix.of (rmulF κ g) = x⁻¹ * Matrix.of g * κ := fun g => by
    show x⁻¹ * (Matrix.of g * κ) = x⁻¹ * Matrix.of g * κ
    rw [Matrix.mul_assoc]
  calc ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * y) ∂μG
      = ∫⁻ g, ENNReal.ofReal (fsR k r s y) * (Φ g * FsE k r s (x⁻¹ * Matrix.of g * κ)) ∂μG := by
        refine lintegral_congr fun g => ?_
        rw [hF s]; ring
    _ = ENNReal.ofReal (fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * κ) ∂μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG := by
        rw [← rmul_int hκ.1 hμ (fun g => Φ g * FsE k r s (x⁻¹ * Matrix.of g))]
        refine congrArg _ (lintegral_congr fun g => ?_)
        simp only [(hK κ hκ g).2, h1]
    _ = _ := by
        rw [hL, ENNReal.ofReal_mul (fsR_nonneg hk hx s)]
        ring

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.CB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS

variable {k r : ℕ}

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, hpk_apply]
  by_cases h : j = sigI k r i
  · subst h; rw [if_pos (sig_sig i).symm, if_pos rfl, sgn_sig, star_sgn]
  · have h' : ¬ i = sigI k r j := fun h2 => h (by rw [h2, sig_sig])
    rw [if_neg h', if_neg h, star_zero]

theorem hpk_K : Hpk k r ∈ Kset k r := by
  have h2 := HermitianLiftIdentities.hpk_sq (k := k) (r := r)
  refine ⟨?_, ?_⟩
  · show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
    rw [hpk_conjT, Matrix.mul_assoc, h2, Matrix.mul_one]
  · rw [hpk_conjT, h2]

theorem gN_sq (g : Mat k r) : (∑ i, ∑ j, Complex.normSq (g i j)) = (trace (gᴴ * g)).re := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

theorem gN_left {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) : gN (κ * g) = gN g := by
  unfold gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]

theorem gN_right {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) : gN (g * κ) = gN g := by
  have hκ' : κ * κᴴ = 1 := mul_eq_one_comm.mp hκ
  unfold gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hκ', Matrix.mul_one]

theorem conjH_mul (a b : Mat k r) :
    Hpk k r * a * Hpk k r * (Hpk k r * b * Hpk k r) = Hpk k r * (a * b) * Hpk k r := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), HermitianLiftIdentities.hpk_sq, Matrix.one_mul]

theorem dot_H (v w : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ v) ⬝ᵥ (Hpk k r *ᵥ w) = star v ⬝ᵥ w := by
  have h := HE_adj (HE k r (WithLp.toLp 2 v)) (WithLp.toLp 2 w)
  rw [HE_HE] at h
  simp only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp] at h
  rw [dotProduct_comm (star (Hpk k r *ᵥ v)), ← h, dotProduct_comm]

theorem ga_H (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => Hpk k r *ᵥ Y a) = Ga k r l Y := by
  unfold Ga; simp only [dot_H]

theorem fsR_conj (s : Fin (r + 1) → ℝ) (x : Mat k r) :
    fsR k r s (Hpk k r * x * Hpk k r) = xiR k r s x := by
  unfold fsR xiR Del
  refine Finset.prod_congr rfl fun l _ => ?_
  have e : (fun a => (Hpk k r * x * Hpk k r) *ᵥ phiV' k r a) = fun a => Hpk k r *ᵥ (x *ᵥ phiV k r a) := by
    funext a
    rw [phiV', mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (Hpk k r * x), HermitianLiftIdentities.hpk_sq, Matrix.mul_one]
  rw [e, ga_H, Real.sqrt_eq_rpow, ← Real.rpow_mul (XI.ga_nonneg _ _ _ _)]
  congr 1; ring

theorem xiR_nonneg (s : Fin (r + 1) → ℝ) (x : Mat k r) : 0 ≤ xiR k r s x :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _

theorem norm_bd {E : Type*} [NormedAddCommGroup E] (hGN : GNLower) (F : Mat k r → E) (c A : ℝ)
    (hF : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) (h : Mat k r) (hh : h ∈ GV k r) :
    ‖F h‖ₑ ≤ ENNReal.ofReal c * ENNReal.ofReal (gN h ^ (-A)) := by
  have h1 : 1 ≤ gN h := hGN k r h hh
  have hp : 0 < gN h ^ A := Real.rpow_pos_of_pos (by linarith) A
  have hc0 : 0 ≤ c := le_trans (mul_nonneg hp.le (norm_nonneg _)) (hF h hh)
  have h2 : ‖F h‖ ≤ c * gN h ^ (-A) := by
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]; exact hF h hh
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc0]
  exact ENNReal.ofReal_le_ofReal h2

theorem c_nonneg {E : Type*} [NormedAddCommGroup E] (hGN : GNLower) (F : Mat k r → E) (c A : ℝ)
    (hF : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) (h1 : (1 : Mat k r) ∈ GV k r) : 0 ≤ c := by
  have : 0 < gN (1 : Mat k r) ^ A := Real.rpow_pos_of_pos (by linarith [hGN k r 1 h1]) A
  exact le_trans (mul_nonneg this.le (norm_nonneg _)) (hF 1 h1)

theorem sum_le (hk : 1 ≤ k) (s : Fin (r + 1) → ℝ) (hs : SAdm k r s) (A : ℝ) (hA : AB k r ≤ A) :
    ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ A := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s0 k r l :=
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (by linarith [(hs l).1]) (by positivity)
  have h2 : ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s0 k r l ≤ 2 * (r : ℝ) * r + ((r : ℝ) + 1) * k := by
    rw [Fin.sum_univ_castSucc]
    simp only [s0, Fin.coe_castSucc, Fin.is_lt, ite_true, Fin.val_last, lt_self_iff_false, ite_false]
    have h3 : ∑ i : Fin r, ((i.val : ℝ) + 1) * 2 ≤ ∑ i : Fin r, (r : ℝ) * 2 := Finset.sum_le_sum fun i _ => by
      have h := Nat.succ_le_of_lt i.isLt
      have : (i.val : ℝ) + 1 ≤ r := by exact_mod_cast h
      linarith
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    linarith
  have hr : (0 : ℝ) ≤ r := by positivity
  have h4 : 2 * (r : ℝ) * r + ((r : ℝ) + 1) * k ≤ AB k r := by unfold AB; nlinarith
  linarith

theorem s_nonneg (hk : 1 ≤ k) (s : Fin (r + 1) → ℝ) (hs : SAdm k r s) (l : Fin (r + 1)) : 0 ≤ s l := by
  have h1 := (hs l).2
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold s0 at h1; split_ifs at h1 <;> linarith

theorem coefStepC (hB2 : InductiveHeisenbergInputs) (hT : TBoth) (hD : DET) : CoefStep := by
  intro k r Wp Wq _ _ _ _ _ _ D A s hs hA hJ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGN, -, -, -, hCG', -⟩ := hB2
  have hCG := hCG' k r
  have hk := D.k_pos
  have hμ := D.haarG
  have hHK : Hpk k r ∈ Kset k r := hpk_K
  have hHG : Hpk k r ∈ GV k r := hHK.1
  have hH2 : Hpk k r * Hpk k r = 1 := HermitianLiftIdentities.hpk_sq k r
  obtain ⟨CD, hCD⟩ := hD k r s A hk (s_nonneg hk s hs) (sum_le hk s hs A hA)
  have hgc : Continuous fun g : Mt k r => gN (Matrix.of g) := by
    unfold gN
    simp only [Matrix.of_apply]
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
  have hΦm : Measurable fun g : Mt k r => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) :=
    (hgc.measurable.pow_const (-A)).ennreal_ofReal
  have hΦinv : ∀ κ ∈ Kset k r, ∀ g : Mt k r,
      ENNReal.ofReal (gN (Matrix.of (lmulM κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∧
      ENNReal.ofReal (gN (Matrix.of (rmulF κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) :=
    fun κ hκ g => ⟨by rw [show Matrix.of (lmulM κ g) = κ * Matrix.of g from rfl, gN_left _ hκ.2],
      by rw [show Matrix.of (rmulF κ g) = Matrix.of g * κ from rfl, gN_right _ hκ.2]⟩
  refine ⟨CD * (JInt D.μG A s).toReal, fun F F' c c' _ _ hF hF' x hx y hy => ?_⟩
  have hc0 : 0 ≤ c := c_nonneg hGN F c A hF hCG.one_mem
  have hc0' : 0 ≤ c' := c_nonneg hGN F' c' A hF' hCG.one_mem
  have hx' : Hpk k r * x * Hpk k r ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ hHG _ hx) _ hHG
  have hy' : Hpk k r * y * Hpk k r ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ hHG _ hy) _ hHG
  have hxinv : (Hpk k r * x * Hpk k r)⁻¹ = Hpk k r * x⁻¹ * Hpk k r :=
    Matrix.inv_eq_left_inv (by rw [conjH_mul, HermitianLiftIdentities.uh_inv_mul hx, Matrix.mul_one, hH2])
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by rw [ae_iff]; exact hμ.conc
  set K : ℝ≥0∞ := ENNReal.ofReal c * ENNReal.ofReal c' * (CD : ℝ≥0∞) with hK
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    ENNReal.coe_ne_top
  have hpt : ∀ᵐ g ∂D.μG, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ≤
      K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))) := by
    filter_upwards [hae] with g hg
    have hh : x⁻¹ * Matrix.of g * y ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ (hCG.inv_mem _ hx) _ hg) _ hy
    have e1 : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r = (Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r) := by
      rw [hxinv, conjH_mul, conjH_mul]
    have hhH : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r ∈ GV k r :=
      hCG.mul_mem _ (hCG.mul_mem _ hHG _ hh) _ hHG
    have gNe : gN (x⁻¹ * Matrix.of g * y) = gN (Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r) := by
      rw [gN_right _ hHK.2, gN_left _ hHK.2]
    have b1 := norm_bd hGN F c A hF _ hh
    have b2 : ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A)) ≤ (CD : ℝ≥0∞) * FsE k r s
        ((Hpk k r * x * Hpk k r)⁻¹ * (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) := by
      rw [gNe, ← e1]; exact hCD _ hhH
    have b3 := norm_bd hGN F' c' A hF' _ hg
    calc ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ
        ≤ (ENNReal.ofReal c * ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A))) *
          (ENNReal.ofReal c' * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) := mul_le_mul' b1 b3
      _ ≤ (ENNReal.ofReal c * ((CD : ℝ≥0∞) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
            (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)))) *
          (ENNReal.ofReal c' * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) :=
        mul_le_mul' (mul_le_mul' le_rfl b2) le_rfl
      _ = _ := by rw [hK]; ring
  have hsub : (∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG) =
      ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        Matrix.of g * (Hpk k r * y * Hpk k r)) ∂D.μG := by
    rw [← HermitianLiftIdentities.rmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of g * (Hpk k r * y * Hpk k r))),
      ← HermitianLiftIdentities.lmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) g)) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) g) * (Hpk k r * y * Hpk k r)))]
    refine lintegral_congr fun g => ?_
    show _ = ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g))) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g)) *
          (Hpk k r * y * Hpk k r))
    rw [(hΦinv _ hHK _).2, (hΦinv _ hHK _).1]
    rfl
  have hTb := hT k r s D.μG (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) hk hμ hΦm hΦinv _ hx' _ hy'
  calc (∫⁻ g, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g, K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))) ∂D.μG := lintegral_mono_ae hpt
    _ = K * ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG := lintegral_const_mul' _ _ hKt
    _ = K * (ENNReal.ofReal (fsR k r s (Hpk k r * x * Hpk k r) * fsR k r s (Hpk k r * y * Hpk k r)) *
        JInt D.μG A s) := by rw [hsub, hTb]; rfl
    _ = ENNReal.ofReal (CD * (JInt D.μG A s).toReal * c * c') * (xiN k r s x : ℝ≥0∞) *
        (xiN k r s y : ℝ≥0∞) := by
      rw [fsR_conj, fsR_conj, ENNReal.ofReal_mul (xiR_nonneg s x)]
      rw [show (xiN k r s x : ℝ≥0∞) = ENNReal.ofReal (xiR k r s x) from rfl,
        show (xiN k r s y : ℝ≥0∞) = ENNReal.ofReal (xiR k r s y) from rfl]
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg) hc0),
        ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg), ENNReal.ofReal_mul (NNReal.coe_nonneg CD),
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hJ.ne, hK]
      ring

end ReciprocityTheory.ChartRestriction.DS.Xi.CB
end
end

section
noncomputable section

open Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.DetB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem entry_le_gN {k r : ℕ} (h : Mat k r) (m j : Fin (2 * r + k + 1)) : ‖h m j‖ ≤ gN h := by
  unfold gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (h m j) ≤ ∑ j', Complex.normSq (h m j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (h m j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j', Complex.normSq (h i j') :=
        Finset.single_le_sum (f := fun i => ∑ j', Complex.normSq (h i j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ m)

def cst {k r : ℕ} (H : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  ∑ i, ∑ m, ∑ j, ‖w i‖ * ‖H i m‖ * ‖v j‖

theorem cst_nonneg {k r : ℕ} (H : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) : 0 ≤ cst H v w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem herm_le {k r : ℕ} (H h : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    ‖herm H (h *ᵥ v) w‖ ≤ cst H v w * gN h := by
  have hb := entry_le_gN h
  unfold herm cst
  calc ‖star w ⬝ᵥ (H *ᵥ (h *ᵥ v))‖ = ‖∑ i, ∑ m, ∑ j, star (w i) * (H i m * (h m j * v j))‖ := by
        simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    _ ≤ ∑ i, ∑ m, ∑ j, ‖star (w i) * (H i m * (h m j * v j))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun m _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ m, ∑ j, ‖w i‖ * ‖H i m‖ * ‖v j‖ * gN h := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_mul, norm_mul, norm_star]
        calc ‖w i‖ * (‖H i m‖ * (‖h m j‖ * ‖v j‖)) = (‖w i‖ * ‖H i m‖ * ‖v j‖) * ‖h m j‖ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hb m j) (by positivity)
    _ = (∑ i, ∑ m, ∑ j, ‖w i‖ * ‖H i m‖ * ‖v j‖) * gN h := by simp only [Finset.sum_mul]

def K0 (k r : ℕ) : ℝ := ∑ a : Fin (r + 1), ∑ b : Fin (r + 1), cst (Hpk k r) (phiV' k r b) (phiV' k r a)

theorem lipschitzConst_nonneg (k r : ℕ) : 0 ≤ K0 k r :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => cst_nonneg _ _ _

theorem hermForm_phi_le_bound (k r : ℕ) (a b : Fin (r + 1)) :
    cst (Hpk k r) (phiV' k r b) (phiV' k r a) ≤ K0 k r := by
  unfold K0
  calc cst (Hpk k r) (phiV' k r b) (phiV' k r a) ≤ ∑ b', cst (Hpk k r) (phiV' k r b') (phiV' k r a) :=
        Finset.single_le_sum (f := fun b' => cst (Hpk k r) (phiV' k r b') (phiV' k r a))
          (fun _ _ => cst_nonneg _ _ _) (Finset.mem_univ b)
    _ ≤ _ := Finset.single_le_sum (f := fun a' => ∑ b', cst (Hpk k r) (phiV' k r b') (phiV' k r a'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => cst_nonneg _ _ _) (Finset.mem_univ a)

theorem Dl_le (k r : ℕ) (l : Fin (r + 1)) (h : Mat k r) :
    ‖Dl k r l h‖ ≤ (l.val + 1).factorial * (K0 k r * gN h) ^ (l.val + 1) := by
  have hx : ∀ i j, NormedField.toAbsoluteValue ℂ ((Matrix.of fun a b : Fin (l.val + 1) =>
      herm (Hpk k r) (h *ᵥ phiV' k r (Fin.castLE (by omega) b)) (phiV' k r (Fin.castLE (by omega) a))) i j)
        ≤ K0 k r * gN h := by
    intro i j
    show ‖herm (Hpk k r) (h *ᵥ phiV' k r _) (phiV' k r _)‖ ≤ _
    exact (herm_le _ _ _ _).trans (mul_le_mul_of_nonneg_right (hermForm_phi_le_bound _ _ _ _)
      (le_trans (norm_nonneg _) (entry_le_gN h 0 0)))
  have := Matrix.det_le hx
  simp only [Fintype.card_fin, nsmul_eq_mul] at this
  exact this

def cl (k r : ℕ) (l : Fin (r + 1)) : ℝ := (l.val + 1).factorial * K0 k r ^ (l.val + 1) + 1

theorem cl_pos (k r : ℕ) (l : Fin (r + 1)) : 0 < cl k r l := by
  have := lipschitzConst_nonneg k r
  unfold cl; positivity

theorem fac_le (k r : ℕ) (l : Fin (r + 1)) (s : ℝ) (hs : 0 ≤ s) (h : Mat k r) (hM : 1 ≤ gN h) :
    ENNReal.ofReal (gN h ^ (-(((l.val : ℝ) + 1) * s))) ≤
      ENNReal.ofReal (cl k r l ^ s) * (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s) := by
  have hM0 : 0 < gN h := by linarith
  have hc := cl_pos k r l
  have hK := lipschitzConst_nonneg k r
  have hD : ‖Dl k r l h‖ ≤ cl k r l * gN h ^ (l.val + 1) := by
    have := Dl_le k r l h
    rw [mul_pow, ← mul_assoc] at this
    refine this.trans ?_
    unfold cl
    have : 0 ≤ gN h ^ (l.val + 1) := by positivity
    nlinarith
  have hb : 0 < cl k r l * gN h ^ (l.val + 1) := mul_pos hc (pow_pos hM0 _)
  have h1 : (‖Dl k r l h‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (cl k r l * gN h ^ (l.val + 1)) := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]; exact ENNReal.ofReal_le_ofReal hD
  have h2 : ENNReal.ofReal (cl k r l * gN h ^ (l.val + 1)) ^ (-s) ≤ (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow h1 hs)
  refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl h2)
  rw [ENNReal.ofReal_rpow_of_pos hb, ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
  congr 1
  rw [Real.mul_rpow hc.le (pow_nonneg hM0.le _), Real.rpow_neg hc.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hM0.le, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hc s).ne', one_mul]
  congr 1
  push_cast; ring

end ReciprocityTheory.ChartRestriction.DS.Xi.DetB

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 DetB

theorem detH (hB2 : InductiveHeisenbergInputs) : DET := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGN, -⟩ := hB2
  intro k r s A _ hs hA
  refine ⟨∏ l, Real.toNNReal (cl k r l ^ s l), fun h hh => ?_⟩
  have hM : 1 ≤ gN h := hGN k r h hh
  have hM0 : 0 < gN h := by linarith
  calc ENNReal.ofReal (gN h ^ (-A))
        ≤ ENNReal.ofReal (gN h ^ (-∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l)) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hM (neg_le_neg hA))
    _ = ∏ l : Fin (r + 1), ENNReal.ofReal (gN h ^ (-(((l.val : ℝ) + 1) * s l))) := by
        rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hM0,
          ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg hM0.le _)]
    _ ≤ ∏ l : Fin (r + 1), (ENNReal.ofReal (cl k r l ^ s l) * (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s l)) :=
        Finset.prod_le_prod' fun l _ => fac_le k r l (s l) (hs l) h hM
    _ = _ := by
        rw [Finset.prod_mul_distrib, FsE, ENNReal.ofNNReal_finsetProd]; rfl

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem iw : IW := iwB

theorem det_of (hB2 : InductiveHeisenbergInputs) : DET := detH hB2

theorem coefStep_of (hB2 : InductiveHeisenbergInputs) (hT : TBoth) (hD : DET) : CoefStep := CB.coefStepC hB2 hT hD

end ReciprocityTheory.ChartRestriction.DS.Xi
end
