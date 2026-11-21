import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCBounds

open Matrix

noncomputable section

def entrySum {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ := ∑ j, ∑ k, |A j k|

theorem entrySum_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : 0 ≤ entrySum A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem dot_self_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem mul_self_le_dot {ι : Type*} [Fintype ι] (x : ι → ℝ) (j : ι) : x j * x j ≤ x ⬝ᵥ x :=
  Finset.single_le_sum (f := fun i => x i * x i) (fun i _ => mul_self_nonneg (x i))
    (Finset.mem_univ j)

theorem abs_mul_le_dot {ι : Type*} [Fintype ι] (x : ι → ℝ) (j k : ι) :
    |x j| * |x k| ≤ x ⬝ᵥ x := by
  have hj := mul_self_le_dot x j
  have hk := mul_self_le_dot x k
  nlinarith [abs_mul_abs_self (x j), abs_mul_abs_self (x k), sq_nonneg (|x j| - |x k|)]

theorem abs_quad_le {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ entrySum A * (x ⬝ᵥ x) := by
  have h : x ⬝ᵥ (A *ᵥ x) = ∑ j, ∑ k, x j * A j k * x k := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h, entrySum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul]
  calc |x j| * |A j k| * |x k| = |A j k| * (|x j| * |x k|) := by ring
    _ ≤ |A j k| * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_left (abs_mul_le_dot x j k) (abs_nonneg _)

theorem quad_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((∑ j ∈ s, A j) *ᵥ x) = ∑ j ∈ s, x ⬝ᵥ (A j *ᵥ x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, dotProduct_add, ih]

theorem quad_smul_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((l • (1 : Matrix ι ι ℝ) - A) *ᵥ x) = l * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

theorem quad_sub_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((A - l • (1 : Matrix ι ι ℝ)) *ᵥ x) = x ⬝ᵥ (A *ᵥ x) - l * (x ⬝ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

theorem posSemidef_of_real {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A)
    (h : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) : A.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg
    ((conjTranspose_eq_transpose_of_trivial A).trans hs) (by simpa using h)

theorem quad_nonneg {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  simpa using hA.dotProduct_mulVec_nonneg x

theorem transpose_of_posSemidef {ι : Type*} {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : Aᵀ = A :=
  (conjTranspose_eq_transpose_of_trivial A).symm.trans hA.isHermitian

theorem quad_symm {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (u v : ι → ℝ) :
    v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hs]

theorem quad_cs {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (u v : ι → ℝ) :
    (u ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) := by
  have hvu := quad_symm (transpose_of_posSemidef hA) u v
  have key : ∀ t : ℝ, 0 ≤ (v ⬝ᵥ (A *ᵥ v)) * (t * t) + (2 * (u ⬝ᵥ (A *ᵥ v))) * t +
      u ⬝ᵥ (A *ᵥ u) := by
    intro t
    have h := quad_nonneg hA (u + t • v)
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hvu] at h
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem posDef_of_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) : A.PosDef := by
  have hs : Aᵀ = A := by
    have := transpose_of_posSemidef h
    rw [transpose_sub, transpose_smul, transpose_one] at this
    exact sub_left_injective this
  refine posDef_iff_dotProduct_mulVec.mpr ⟨(conjTranspose_eq_transpose_of_trivial A).trans hs,
    fun x hx => ?_⟩
  have h1 := quad_nonneg h x
  rw [quad_sub_smul_one] at h1
  have h2 : 0 < x ⬝ᵥ x := by
    rcases (dot_self_nonneg x).lt_or_eq with h3 | h3
    · exact h3
    · exact absurd (dotProduct_self_eq_zero.mp h3.symm) hx
  simpa using (by nlinarith : 0 < x ⬝ᵥ (A *ᵥ x))

theorem inv_le_of_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) :
    (c⁻¹ • (1 : Matrix ι ι ℝ) - A⁻¹).PosSemidef := by
  have hA : A.PosDef := posDef_of_ge hc h
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hs : Aᵀ = A := transpose_of_posSemidef hA.posSemidef
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, transpose_nonsing_inv, hs]
  · rw [quad_smul_one_sub]
    set y := A⁻¹ *ᵥ x with hy
    have hx : A *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have h1 : c * (y ⬝ᵥ y) ≤ x ⬝ᵥ y := by
      have := quad_nonneg h y
      rw [quad_sub_smul_one, hx, dotProduct_comm] at this
      linarith
    have h3 : 0 ≤ (x - c • y) ⬝ᵥ (x - c • y) := dot_self_nonneg _
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm y x] at h3
    have key : c * (x ⬝ᵥ y) ≤ x ⬝ᵥ x := by nlinarith
    have := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hc.le)
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at this
    linarith

theorem inv_ge_of_le {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {l : ℝ}
    (hl : 0 < l) (hA : A.PosDef) (h : (l • (1 : Matrix ι ι ℝ) - A).PosSemidef) :
    (A⁻¹ - l⁻¹ • (1 : Matrix ι ι ℝ)).PosSemidef := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hs : Aᵀ = A := transpose_of_posSemidef hA.posSemidef
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, transpose_nonsing_inv, hs]
  · rw [quad_sub_smul_one]
    set y := A⁻¹ *ᵥ x with hy
    have hx : A *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have hcs := quad_cs hA.posSemidef y x
    have e1 : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ x := by rw [← quad_symm hs, hx]
    have e2 : y ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by rw [hx, dotProduct_comm]
    rw [e1, e2] at hcs
    have hxy : 0 ≤ x ⬝ᵥ y := e2 ▸ quad_nonneg hA.posSemidef y
    have hlx : x ⬝ᵥ (A *ᵥ x) ≤ l * (x ⬝ᵥ x) := by
      have := quad_nonneg h x
      rw [quad_smul_one_sub] at this
      linarith
    have hxx := dot_self_nonneg x
    rcases hxx.lt_or_eq with hpos | hzero
    · have h4 : (x ⬝ᵥ x) * (x ⬝ᵥ x) ≤ (l * (x ⬝ᵥ y)) * (x ⬝ᵥ x) := by
        nlinarith [mul_le_mul_of_nonneg_left hlx hxy]
      have h5 : x ⬝ᵥ x ≤ l * (x ⬝ᵥ y) := le_of_mul_le_mul_right h4 hpos
      have := mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr hl.le)
      rw [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul] at this
      linarith
    · rw [← hzero]; simpa using hxy

open scoped ComplexOrder in

theorem posSemidef_map_ofReal {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (A.map (fun x : ℝ => (x : ℂ))).PosSemidef := by
  have hs : ∀ j k, A k j = A j k := fun j k => by
    simpa using congrFun (congrFun (transpose_of_posSemidef hA) j) k
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
  · ext j k
    simp [conjTranspose_apply, hs]
  · set a : ι → ℝ := fun k => (w k).re
    set b : ι → ℝ := fun k => (w k).im
    have ha := quad_nonneg hA a
    have hb := quad_nonneg hA b
    have hre : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).re =
        a ⬝ᵥ (A *ᵥ a) + b ⬝ᵥ (A *ᵥ b) := by
      simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.re_sum, Complex.mul_re,
        Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, a, b, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have him : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im = 0 := by
      have e : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im =
          ∑ j, ∑ k, (w j).re * (A j k * (w k).im) - ∑ j, ∑ k, (w j).im * (A j k * (w k).re) := by
        simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.mul_im, Complex.mul_re,
          Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.im_sum, Complex.ofReal_re,
          Complex.ofReal_im, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      have hsw : ∑ j, ∑ k, (w j).re * (A j k * (w k).im) =
          ∑ j, ∑ k, (w j).im * (A j k * (w k).re) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hs]; ring
      rw [e, hsw, sub_self]
    exact Complex.nonneg_iff.mpr ⟨hre ▸ add_nonneg ha hb, him.symm⟩

end

end GroundTheory.Heights₂.Heights.MCBounds
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCBounds

open Matrix
open scoped ComplexOrder

noncomputable section

variable (D : PeriodChartData)

theorem cusp_norm_lt {z : Fin D.n → ℂ} (hz : z ∈ D.U) (j : Fin D.a) :
    ‖cuspCoord D.a_le z j‖ < 1 :=
  D.U_subset hz (Fin.castLE D.a_le j)

theorem log_inv_sq_nonneg {w : ℂ} (hw : ‖w‖ < 1) : 0 ≤ Real.log (‖w‖ ^ 2)⁻¹ := by
  rw [Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg w) hw.le))

theorem exp_one_le_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) : Real.exp 1 ≤ D.radius z := by
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => log_inv_sq_nonneg (cusp_norm_lt D hz j)
  simp only [PeriodChartData.radius, chartRadius]
  linarith

theorem one_le_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) : 1 ≤ D.radius z := by
  have := exp_one_le_radius D hz
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem one_le_log_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) : 1 ≤ Real.log (D.radius z) := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (exp_one_le_radius D hz)

theorem cuspTime_le_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) (j : Fin D.a) :
    cuspTime D.a_le z j ≤ D.radius z := by
  have hlt := cusp_norm_lt D hz j
  have hL : 0 ≤ -Real.log ‖cuspCoord D.a_le z j‖ :=
    neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hlt.le)
  have hterm : Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ = 2 * -Real.log ‖cuspCoord D.a_le z j‖ := by
    rw [Real.log_inv, Real.log_pow]; push_cast; ring
  have hsum : Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ ≤
      ∑ i, Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹ :=
    Finset.single_le_sum (f := fun i => Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹)
      (fun i _ => log_inv_sq_nonneg (cusp_norm_lt D hz i)) (Finset.mem_univ j)
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have he := Real.exp_pos 1
  have h1 : cuspTime D.a_le z j = (2 * Real.pi)⁻¹ * -Real.log ‖cuspCoord D.a_le z j‖ := by
    rw [cuspTime, Real.log_inv]
  have h2 := mul_le_mul_of_nonneg_right hpi hL
  rw [h1]
  simp only [PeriodChartData.radius, chartRadius]
  linarith

theorem Y_transpose {z : Fin D.n → ℂ} (hz : z ∈ D.U) : (D.Y z)ᵀ = D.Y z := by
  ext j k
  simp only [transpose_apply, PeriodChartData.Y, chartImag, Matrix.add_apply, map_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [show D.τ0 z k j = D.τ0 z j k from by simpa using congrFun (congrFun (D.τ0_symm z hz) j) k]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show D.B i k j = D.B i j k from by simpa using (D.B_psd i).isHermitian.apply j k]

theorem exists_bound_imτ0 : ∃ M : ℝ, 0 ≤ M ∧
    ∀ p ∈ D.K, entrySum ((D.τ0 p.1).map Complex.im) ≤ M := by
  have hcont : ContinuousOn (fun z => entrySum ((D.τ0 z).map Complex.im)) D.U := by
    unfold entrySum
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
    simp only [map_apply]
    exact continuous_abs.comp_continuousOn
      (Complex.continuous_im.comp_continuousOn (D.τ0_analytic j k).continuousOn)
  have hKc : IsCompact (Prod.fst '' D.K) := D.isCompact_K.image continuous_fst
  have hsub : Prod.fst '' D.K ⊆ D.U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (D.K_subset hp).1
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max M 0, le_max_right _ _, fun p hp => ?_⟩
  have h := hM p.1 ⟨p, hp, rfl⟩
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

theorem quad_Y_le {z : Fin D.n → ℂ} (hz : z ∈ D.U) (M : ℝ)
    (hM : entrySum ((D.τ0 z).map Complex.im) ≤ M) (x : Fin D.g → ℝ) :
    x ⬝ᵥ (D.Y z *ᵥ x) ≤ (M + ∑ j, entrySum (D.B j)) * D.radius z * (x ⬝ᵥ x) := by
  have hr1 := one_le_radius D hz
  have hxx := dot_self_nonneg x
  have hM0 : 0 ≤ M := (entrySum_nonneg _).trans hM
  simp only [PeriodChartData.Y, chartImag]
  rw [add_mulVec, dotProduct_add, quad_sum]
  have h0 : x ⬝ᵥ ((D.τ0 z).map Complex.im *ᵥ x) ≤ M * D.radius z * (x ⬝ᵥ x) := by
    have h3 := (le_abs_self _).trans (abs_quad_le ((D.τ0 z).map Complex.im) x)
    have h2 : entrySum ((D.τ0 z).map Complex.im) * (x ⬝ᵥ x) ≤ M * D.radius z * (x ⬝ᵥ x) := by
      apply mul_le_mul_of_nonneg_right _ hxx
      nlinarith
    linarith
  have h1 : ∀ j, x ⬝ᵥ ((cuspTime D.a_le z j • D.B j) *ᵥ x) ≤
      entrySum (D.B j) * D.radius z * (x ⬝ᵥ x) := by
    intro j
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    have ht1 := cuspTime_le_radius D hz j
    have hq := (le_abs_self _).trans (abs_quad_le (D.B j) x)
    have hq0 := quad_nonneg (D.B_psd j) x
    have hr0 : 0 ≤ D.radius z := by linarith
    calc cuspTime D.a_le z j * (x ⬝ᵥ (D.B j *ᵥ x)) ≤ D.radius z * (entrySum (D.B j) * (x ⬝ᵥ x)) :=
          mul_le_mul ht1 hq hq0 hr0
      _ = _ := by ring
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h1 j
  rw [← Finset.sum_mul, ← Finset.sum_mul] at hsum
  linarith

theorem exists_Y_le : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ D.K,
    ((C * D.radius p.1) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_imτ0 D
  have hβ : 0 ≤ ∑ j, entrySum (D.B j) := Finset.sum_nonneg fun j _ => entrySum_nonneg _
  refine ⟨M + ∑ j, entrySum (D.B j) + 1, by positivity, fun p hp => ?_⟩
  have hz : p.1 ∈ D.U := (D.K_subset hp).1
  have hr1 := one_le_radius D hz
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, Y_transpose D hz]
  · rw [quad_smul_one_sub]
    have h := quad_Y_le D hz M (hM p hp) x
    have hxx := dot_self_nonneg x
    nlinarith

theorem injective_of_rank {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    Function.Injective F.mulVec := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin F)
  rw [Module.finrank_fin_fun] at h1
  have h2 : Module.finrank ℂ (LinearMap.ker F.mulVecLin) = 0 := by
    unfold Matrix.rank at h; omega
  have h3 : LinearMap.ker F.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h2
  exact LinearMap.ker_eq_bot.mp h3

theorem gram_posDef {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    (Fᴴ * F).PosDef :=
  PosDef.conjTranspose_mul_self F (injective_of_rank F h)

theorem continuousOn_f : ContinuousOn D.f (D.U ×ˢ D.V) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_matrix fun j k => (D.f_analytic j k).continuousOn.domRestrict

theorem exists_gram_bounds : ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ p ∈ D.K,
    δ ≤ ((D.f p)ᴴ * D.f p).det.re ∧ ((D.f p)ᴴ * D.f p).det.re ≤ M := by
  have hc : ContinuousOn (fun p => ((D.f p)ᴴ * D.f p).det.re) D.K := by
    have h := (continuousOn_f D).mono D.K_subset
    rw [continuousOn_iff_continuous_domRestrict] at h ⊢
    exact Complex.continuous_re.comp (h.matrix_conjTranspose.matrix_mul h).matrix_det
  have hpos : ∀ p ∈ D.K, 0 < ((D.f p)ᴴ * D.f p).det.re := fun p hp =>
    MCDet.re_det_pos (gram_posDef _ (D.f_rank p (D.K_subset hp)))
  rcases D.K.eq_empty_or_nonempty with hK | hK
  · exact ⟨1, 1, one_pos, one_pos, fun p hp => by simp [hK] at hp⟩
  obtain ⟨p0, hp0, hmin⟩ := D.isCompact_K.exists_isMinOn hK hc
  obtain ⟨M, hM⟩ := D.isCompact_K.exists_bound_of_continuousOn hc
  refine ⟨_, max M 1, hpos p0 hp0, by positivity, fun p hp => ⟨hmin hp, ?_⟩⟩
  have h := hM p hp
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

end

end GroundTheory.Heights₂.Heights.MCBounds
end
