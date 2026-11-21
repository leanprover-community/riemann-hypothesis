import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ArchHeisOf
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ExistsDensity
import GroundTheory.GlobalFields.TateThesis.GaussianComplexFourier
import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SliceMain

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

variable {ι : Type} [Fintype ι]

def nm (y : ι → ℂ) : ℝ := ∏ w, ‖y w‖ ^ 2

theorem nm_pos {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) : 0 < nm y := Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hy w)) 2

theorem nm_mul (x y : ι → ℂ) : nm (x * y) = nm x * nm y := by simp [nm, mul_pow, Finset.prod_mul_distrib]

theorem nm_inv (x : ι → ℂ) : nm x⁻¹ = (nm x)⁻¹ := by simp [nm, Finset.prod_inv_distrib]

theorem continuous_nm : Continuous (nm : (ι → ℂ) → ℝ) := by unfold nm; fun_prop

theorem ae_unit : ∀ᵐ y : ι → ℂ, ∀ w, y w ≠ 0 := ae_all_iff.2 fun w => Measure.ae_eval_ne (fun _ : ι => (volume : Measure ℂ)) w 0

theorem map_mul_volume_pi_complex {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) :
    Measure.map (fun x : ι → ℂ => y * x) volume = ENNReal.ofReal (nm y)⁻¹ • volume := by
  classical
  let L : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := LinearMap.pi fun w => (Algebra.lmul ℝ ℂ (y w)).comp (LinearMap.proj w)
  have hd : LinearMap.det L = nm y := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ)) (f := L) (by rw [hd]; exact (nm_pos hy).ne')
  rw [hd, abs_of_pos (inv_pos.2 (nm_pos hy))] at this
  exact this

theorem meas_mul (y : ι → ℂ) : Measurable fun x : ι → ℂ => y * x := (continuous_const.mul continuous_id).measurable

theorem integral_scale {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) {g : (ι → ℂ) → E}
    (hg : AEStronglyMeasurable g volume) : ∫ x, g (y * x) = (nm y)⁻¹ • ∫ x, g x := by
  rw [← integral_map (meas_mul y).aemeasurable (by rw [map_mul_volume_pi_complex hy]; exact hg.smul_measure _), map_mul_volume_pi_complex hy,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 (nm_pos hy)).le]

theorem integrable_scale {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) {g : (ι → ℂ) → ℂ} (hg : Integrable g) : Integrable fun x => g (y * x) := by
  have : Integrable g (Measure.map (fun x : ι → ℂ => y * x) volume) := by
    rw [map_mul_volume_pi_complex hy]; exact hg.smul_measure ENNReal.ofReal_ne_top
  exact this.comp_measurable (meas_mul y)

theorem kernel {a j : (ι → ℂ) → ℂ} (ha : AEStronglyMeasurable a volume) (hj : Integrable j) (hjm : Measurable j) {s : (ι → ℂ) → ι → ℂ}
    (hs : Measurable s) (hsU : ∀ x, (∀ w, x w ≠ 0) → ∀ w, s x w ≠ 0) (hi : Integrable fun x => a x * ((nm (s x) : ℝ) : ℂ)⁻¹) :
    Integrable (fun q : (ι → ℂ) × (ι → ℂ) => a q.1 * j (s q.1 * q.2)) (volume.prod volume) ∧
      ∫ x, ∫ y, a x * j (s x * y) = (∫ x, a x * ((nm (s x) : ℝ) : ℂ)⁻¹) * ∫ y, j y := by
  constructor
  · have hm : AEStronglyMeasurable (fun q : (ι → ℂ) × (ι → ℂ) => a q.1 * j (s q.1 * q.2)) (volume.prod volume) :=
      ha.comp_fst.mul (hjm.comp ((hs.comp measurable_fst).mul measurable_snd)).aestronglyMeasurable
    refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
    · filter_upwards [ae_unit] with x hx using (integrable_scale (hsU x hx) hj).const_mul _
    · refine (hi.norm.mul_const (∫ y, ‖j y‖)).congr ?_
      filter_upwards [ae_unit] with x hx
      simp only [norm_mul]
      rw [integral_const_mul, integral_scale (hsU x hx) (g := fun y => ‖j y‖) hj.1.norm, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (nm_pos (hsU x hx)).le, smul_eq_mul, mul_assoc]
  · rw [← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [ae_unit] with x hx
    rw [integral_const_mul, integral_scale (hsU x hx) hj.1, Complex.real_smul, mul_assoc]
    push_cast; rfl

def pr (x y : ι → ℂ) : ℝ := ∑ w, 2 * (x w * y w).re

theorem continuous_pr : Continuous fun q : (ι → ℂ) × (ι → ℂ) => pr q.1 q.2 := by unfold pr; fun_prop

def FT (h : (ι → ℂ) → ℂ) (t : ι → ℂ) : ℂ := ∫ x, ch (-pr x t) * h x

theorem continuous_FT {h : (ι → ℂ) → ℂ} (hh : Integrable h) : Continuous (FT h) := by
  refine continuous_of_dominated (bound := fun x => ‖h x‖) (fun t => ?_) (fun t => Eventually.of_forall fun x => ?_) hh.norm
    (Eventually.of_forall fun x => ?_)
  · exact (continuous_ch.comp (continuous_pr.comp (continuous_id.prodMk continuous_const)).neg).aestronglyMeasurable.mul hh.1
  · rw [norm_mul, norm_ch, one_mul]
  · exact (continuous_ch.comp (continuous_pr.comp (continuous_const.prodMk continuous_id)).neg).mul continuous_const

theorem pr_comm (x y : ι → ℂ) : pr x y = pr y x := by simp [pr, mul_comm]

theorem FT_mul {h m : (ι → ℂ) → ℂ} (hh : Integrable h) (hm : Integrable m) : ∫ t, FT h t * m t = ∫ x, h x * FT m x := by
  have hi : Integrable (fun q : (ι → ℂ) × (ι → ℂ) => ch (-pr q.2 q.1) * (m q.1 * h q.2)) (volume.prod volume) := by
    refine (hm.mul_prod hh).bdd_mul (c := 1) ?_ (Eventually.of_forall fun q => (norm_ch _).le)
    exact (continuous_ch.comp (continuous_pr.comp continuous_swap).neg).aestronglyMeasurable
  calc ∫ t, FT h t * m t = ∫ t, ∫ x, ch (-pr x t) * (m t * h x) := by
        congr 1; funext t; rw [FT, ← integral_mul_const]; congr 1; funext x; ring
    _ = ∫ x, ∫ t, ch (-pr x t) * (m t * h x) := integral_integral_swap hi
    _ = _ := by
        congr 1; funext x; rw [FT, ← integral_const_mul]; congr 1; funext t; rw [pr_comm]; ring

theorem FT_scale {m : (ι → ℂ) → ℂ} (hm : Integrable m) {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) (x : ι → ℂ) :
    FT (fun t => m (y * t)) x = ((nm y : ℝ) : ℂ)⁻¹ * FT m (x * y⁻¹) := by
  have h := integral_scale hy (g := fun t => ch (-pr t (x * y⁻¹)) * m t)
    ((continuous_ch.comp (continuous_pr.comp (continuous_id.prodMk continuous_const)).neg).aestronglyMeasurable.mul hm.1)
  rw [Complex.real_smul] at h
  push_cast at h
  rw [FT, FT, ← h]
  congr 1; funext t; congr 3
  refine Finset.sum_congr rfl fun w _ => ?_
  have := hy w
  simp only [Pi.mul_apply, Pi.inv_apply]
  congr 2; field_simp

def r0 (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : ℂ := ∏ w, (x w / (‖x w‖ : ℂ)) ^ κ w * (‖x w‖ : ℂ) ^ (2 * e)

theorem rationalWeight_mul (κ : ι → ℕ) (e : ℕ) (x y : ι → ℂ) : r0 κ e (x * y) = r0 κ e x * r0 κ e y := by
  rw [r0, r0, r0, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp only [Pi.mul_apply, norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_pow]; ring

theorem rationalWeight_ne_zero (κ : ι → ℕ) (e : ℕ) {x : ι → ℂ} (hx : ∀ w, x w ≠ 0) : r0 κ e x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => by have := hx w; simp [this]

theorem measurable_reduced_size (κ : ι → ℕ) (e : ℕ) : Measurable (r0 κ e) := by unfold r0; fun_prop

theorem rationalWeight_one (κ : ι → ℕ) (e : ℕ) : r0 κ e 1 = 1 := by simp [r0]

def gm (κ : ι → ℕ) (x : ι → ℂ) : ℂ := ∏ w, conj (x w) ^ κ w * Complex.exp (-2 * Real.pi * (‖x w‖ : ℂ) ^ 2)

theorem norm_gauss (z : ℂ) : ‖Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2)‖ = Real.exp (-2 * Real.pi * ‖z‖ ^ 2) := by
  have : (-2 * Real.pi * (‖z‖ : ℂ) ^ 2 : ℂ) = ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal]

theorem poly_le (t : ℝ) (ht : 0 ≤ t) (s : ℕ) : (1 + t) ^ s * Real.exp (-2 * Real.pi * t ^ 2) ≤ Real.exp (s ^ 2) := by
  have h1 : (1 + t) ^ s ≤ Real.exp (s * t) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp t]) s
  calc _ ≤ Real.exp (s * t) * Real.exp (-2 * Real.pi * t ^ 2) := by gcongr
    _ ≤ _ := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2
      nlinarith [Real.pi_gt_three, sq_nonneg (t - s), sq_nonneg t, sq_nonneg (s : ℝ)]

theorem int_of_le {g : ℂ → ℂ} (hg : Measurable g) (C : ℝ) (h : ∀ z, z ≠ 0 → ‖g z‖ * (1 + ‖z‖) ^ 3 ≤ C) : Integrable g := by
  have h3 : Integrable fun z : ℂ => (1 + ‖z‖) ^ (-(3 : ℝ)) := integrable_one_add_norm (by simp; norm_num)
  refine (h3.const_mul C).mono' hg.aestronglyMeasurable ?_
  filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
  have hp : 0 < (1 + ‖z‖) ^ 3 := by positivity
  rw [Real.rpow_neg (by positivity), show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp]
  exact h z hz

theorem int_pg {g : ℂ → ℂ} (hg : Measurable g) (s : ℕ) (h : ∀ z, ‖g z‖ ≤ ‖z‖ ^ s * Real.exp (-2 * Real.pi * ‖z‖ ^ 2)) : Integrable g := by
  refine int_of_le hg (Real.exp ((s + 3 : ℕ) ^ 2)) fun z _ => le_trans ?_ (poly_le ‖z‖ (norm_nonneg z) (s + 3))
  have : ‖z‖ ^ s ≤ (1 + ‖z‖) ^ s := pow_le_pow_left₀ (norm_nonneg z) (by linarith) s
  calc _ ≤ (1 + ‖z‖) ^ s * Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * (1 + ‖z‖) ^ 3 := by
        gcongr; exact (h z).trans (by gcongr)
    _ = _ := by ring

theorem integrable_conj_pow_gaussian (k : ℕ) : Integrable fun z : ℂ => conj z ^ k * Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2) :=
  int_pg (by fun_prop) k fun z => by rw [norm_mul, norm_gauss, norm_pow, Complex.norm_conj]

theorem integrable_gm (κ : ι → ℕ) : Integrable (gm κ) := by
  have := Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ)) fun w => integrable_conj_pow_gaussian (κ w)
  exact this

theorem ch_sum (f : ι → ℝ) : ch (∑ w, f w) = ∏ w, ch (f w) := by
  simp only [ch]; rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum]

theorem FT_gm (κ : ι → ℕ) (x : ι → ℂ) :
    FT (gm κ) x = ∏ w, (2⁻¹ * (-Complex.I) ^ κ w) * (x w ^ κ w * Complex.exp (-2 * Real.pi * (‖x w‖ : ℂ) ^ 2)) := by
  have h1 : FT (gm κ) x = ∏ w, ∫ z : ℂ, ch (-(2 * (z * x w).re)) * (conj z ^ κ w * Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2)) := by
    rw [← integral_fintype_prod_volume_eq_prod, FT]
    congr 1; funext t
    rw [pr, ← Finset.sum_neg_distrib, ch_sum, gm, ← Finset.prod_mul_distrib]
  rw [h1]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h := congrFun (GroundTheory.Global.complexFourier_conj_pow_mul_gaussian (κ w)) (x w)
  rw [GroundTheory.Global.complexFourier, GroundTheory.Global.complexPlaceMeasure, integral_smul_measure] at h
  rw [mul_assoc, ← h]
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]
  rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
  congr 1; funext z; congr 1
  rw [ch]; congr 1; push_cast; ring

theorem tate (κ : ι → ℕ) (e : ℕ) (hκ : ∀ w, 2 * e < κ w) : ∃ Z : ℂ, ∀ H : (ι → ℂ) → ℂ, Integrable H →
    Integrable (fun x => H x * r0 κ e x) → Integrable (fun t => FT H t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹)) →
    ∫ t, FT H t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹) = Z * ∫ x, H x * r0 κ e x := by
  let j₁ : (ι → ℂ) → ℂ := fun y => gm κ y * r0 κ e y
  let j₂ : (ι → ℂ) → ℂ := fun y => FT (gm κ) y⁻¹ * r0 κ e y * ((nm y : ℝ) : ℂ)⁻¹
  have e₁ : j₁ = fun y => ∏ w, ((‖y w‖ ^ (κ w + 2 * e) * Real.exp (-2 * Real.pi * ‖y w‖ ^ 2) : ℝ) : ℂ) := by
    funext y
    simp only [j₁, gm, r0]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hk : κ w ≠ 0 := by have := hκ w; omega
    by_cases hy : y w = 0
    · simp [hy, hk]
    · have hn : (‖y w‖ : ℂ) ≠ 0 := by simpa using hy
      have : conj (y w) * (y w / ‖y w‖) = ‖y w‖ := by
        rw [← mul_div_assoc, Complex.conj_mul', div_eq_iff hn]; ring
      push_cast
      calc _ = (conj (y w) * (y w / ‖y w‖)) ^ κ w * (‖y w‖ : ℂ) ^ (2 * e) * Complex.exp (-2 * Real.pi * (‖y w‖ : ℂ) ^ 2) := by
            rw [mul_pow]; ring
        _ = _ := by rw [this, pow_add]
  have i1 : ∀ s : ℕ, Integrable fun z : ℂ => ((‖z‖ ^ s * Real.exp (-2 * Real.pi * ‖z‖ ^ 2) : ℝ) : ℂ) := fun s =>
    int_pg (by fun_prop) s fun z => by rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hj₁ : Integrable j₁ := by
    rw [e₁]; exact Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ)) fun w => i1 _
  have hZ₁ : ∫ y, j₁ y ≠ 0 := by
    rw [e₁, integral_fintype_prod_volume_eq_prod (fun w (z : ℂ) => ((‖z‖ ^ (κ w + 2 * e) * Real.exp (-2 * Real.pi * ‖z‖ ^ 2) : ℝ) : ℂ))]
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
    refine (integral_pos_of_integrable_nonneg_nonzero (x := (1 : ℂ)) (by fun_prop) ?_ (fun z => by positivity) (by simp)).ne'
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using (i1 (κ w + 2 * e)).re
  have mg : Measurable (gm κ) := by unfold gm; fun_prop
  have mF : Measurable (FT (gm κ)) := (continuous_FT (integrable_gm κ)).measurable
  have mn : Measurable fun y : ι → ℂ => ((nm y : ℝ) : ℂ)⁻¹ := (Complex.continuous_ofReal.comp continuous_nm).measurable.inv
  have hj₂ : Integrable j₂ := by
    have e₂ : j₂ = fun y => ∏ w, (2⁻¹ * (-Complex.I) ^ κ w) * ((y w)⁻¹ ^ κ w * Complex.exp (-2 * Real.pi * (‖(y w)⁻¹‖ : ℂ) ^ 2)) *
        ((y w / (‖y w‖ : ℂ)) ^ κ w * (‖y w‖ : ℂ) ^ (2 * e)) * ((‖y w‖ : ℂ) ^ 2)⁻¹ := by
      funext y
      simp only [j₂, FT_gm, r0, nm, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Pi.inv_apply]
      push_cast; rfl
    rw [e₂]
    refine Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ)) (f := fun w z => (2⁻¹ * (-Complex.I) ^ κ w) *
      (z⁻¹ ^ κ w * Complex.exp (-2 * Real.pi * (‖z⁻¹‖ : ℂ) ^ 2)) * ((z / (‖z‖ : ℂ)) ^ κ w * (‖z‖ : ℂ) ^ (2 * e)) * ((‖z‖ : ℂ) ^ 2)⁻¹) fun w => ?_
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_lt (hκ w)
    refine int_of_le (by fun_prop) (Real.exp ((s + 3 : ℕ) ^ 2)) fun z hz => le_trans ?_ (poly_le ‖z‖⁻¹ (by positivity) (s + 3))
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hg := norm_gauss z⁻¹
    rw [norm_mul, norm_mul, norm_mul, norm_mul (z⁻¹ ^ κ w), hg]
    simp only [norm_mul, norm_pow, norm_inv, norm_neg, Complex.norm_I, one_pow, norm_div, Complex.norm_real, norm_norm,
      div_self hn.ne', mul_one, one_mul, Complex.norm_ofNat]
    have h2 : ‖z‖⁻¹ ^ s ≤ (1 + ‖z‖⁻¹) ^ s := pow_le_pow_left₀ (by positivity) (by linarith) s
    calc _ = 2⁻¹ * (‖z‖⁻¹ ^ s * (1 + ‖z‖⁻¹) ^ 3 * Real.exp (-2 * Real.pi * ‖z‖⁻¹ ^ 2)) := by
          rw [hs, pow_succ, pow_add, inv_pow _ (2 * e)]
          generalize ‖z‖⁻¹ ^ s = a
          have : ‖z‖ ^ (2 * e) ≠ 0 := by positivity
          generalize ‖z‖ ^ (2 * e) = b at *
          generalize Real.exp _ = c
          field_simp; ring
      _ ≤ 1 * ((1 + ‖z‖⁻¹) ^ s * (1 + ‖z‖⁻¹) ^ 3 * Real.exp (-2 * Real.pi * ‖z‖⁻¹ ^ 2)) := by gcongr; norm_num
      _ = _ := by ring
  refine ⟨(∫ y, j₂ y) / ∫ y, j₁ y, fun H hH hr hA => ?_⟩
  have k₁ := kernel (a := fun t => FT H t * (r0 κ e t)⁻¹) ((continuous_FT hH).measurable.mul (measurable_reduced_size κ e).inv).aestronglyMeasurable
    hj₁ (mg.mul (measurable_reduced_size κ e)) measurable_id (fun x hx => hx) (by simpa [mul_assoc] using hA)
  have hx' : ∀ᵐ x : ι → ℂ, H x * r0 κ e x = H x * (r0 κ e x * ((nm x : ℝ) : ℂ)⁻¹) * ((nm x⁻¹ : ℝ) : ℂ)⁻¹ := by
    filter_upwards [ae_unit] with x hx
    have : ((nm x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hx).ne'
    rw [nm_inv]; push_cast; field_simp
  have k₂ := kernel (a := fun x => H x * (r0 κ e x * ((nm x : ℝ) : ℂ)⁻¹)) (hH.1.mul ((measurable_reduced_size κ e).mul mn).aestronglyMeasurable)
    hj₂ (((mF.comp measurable_inv).mul (measurable_reduced_size κ e)).mul mn) measurable_inv (fun x hx w => inv_ne_zero (hx w)) (hr.congr hx')
  rw [← integral_congr_ae hx', integral_integral_swap k₂.1] at k₂
  rw [integral_integral_swap k₁.1] at k₁
  have key : ∫ y, ∫ t, FT H t * (r0 κ e t)⁻¹ * j₁ (id t * y) = ∫ y, ∫ x, H x * (r0 κ e x * ((nm x : ℝ) : ℂ)⁻¹) * j₂ (x⁻¹ * y) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_unit] with y hy
    have hny : ((nm y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hy).ne'
    calc _ = ∫ t, r0 κ e y * (FT H t * gm κ (y * t)) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_unit] with t ht
          have := rationalWeight_ne_zero κ e ht
          simp only [j₁, id, rationalWeight_mul, mul_comm t y]; field_simp
      _ = r0 κ e y * ∫ x, H x * FT (fun t => gm κ (y * t)) x := by
          rw [integral_const_mul, FT_mul hH (integrable_scale hy (integrable_gm κ))]
      _ = _ := by
          rw [← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards [ae_unit] with x hx
          have hnx : ((nm x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hx).ne'
          have h1 : r0 κ e x * r0 κ e x⁻¹ = 1 := by
            rw [← rationalWeight_mul, ← rationalWeight_one κ e]; congr 1; funext w; simp [hx w]
          have h2 : (x⁻¹ * y)⁻¹ = x * y⁻¹ := by funext w; simp [mul_comm]
          simp only [j₂, FT_scale (integrable_gm κ) hy, h2, rationalWeight_mul, nm_mul, nm_inv]
          push_cast
          generalize FT (gm κ) (x * y⁻¹) = A
          have h3 : ((nm x : ℝ) : ℂ)⁻¹ * ((nm x : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hnx
          rw [mul_inv, inv_inv]
          linear_combination (-(H x * A * r0 κ e y * ((nm y : ℝ) : ℂ)⁻¹)) * (((nm x : ℝ) : ℂ)⁻¹ * ((nm x : ℝ) : ℂ) * h1 + h3)
  rw [k₁.2, k₂.2] at key
  simp only [id, mul_assoc] at key
  rw [div_mul_eq_mul_div, eq_div_iff hZ₁, key, mul_comm]

end PositivityTheory.ThKG.Loc.Bump

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace

variable {ι : Type} [Fintype ι] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {K : Type} [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

def Dec (a : K × (ι → ℂ) → ℂ) : Prop := ∀ N : ℕ, ∃ C : ℝ, ∀ k c, ‖a (k, c)‖ * (1 + ‖c‖) ^ N ≤ C

theorem norm_rationalWeight_le (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : ‖r0 κ e x‖ ≤ (1 + ‖x‖) ^ (2 * e * Fintype.card ι) := by
  rw [r0, norm_prod, pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun w _ => ?_
  rw [norm_mul, norm_pow, norm_pow, norm_div, Complex.norm_real, norm_norm]
  have h1 : (‖x w‖ / ‖x w‖) ^ κ w ≤ 1 := pow_le_one₀ (by positivity) (div_self_le_one _)
  have h2 : ‖x w‖ ^ (2 * e) ≤ (1 + ‖x‖) ^ (2 * e) := pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_le_pi_norm x w]) _
  calc _ ≤ 1 * (1 + ‖x‖) ^ (2 * e) := by gcongr
    _ = _ := one_mul _

def mj (x : ι → ℂ) : ℝ := ((1 + ‖x‖) ^ (Module.finrank ℝ (ι → ℂ) + 1))⁻¹

theorem integrable_mj : Integrable (mj : (ι → ℂ) → ℝ) := by
  have h : Integrable fun z : ι → ℂ => (1 + ‖z‖) ^ (-((Module.finrank ℝ (ι → ℂ) + 1 : ℕ) : ℝ)) :=
    integrable_one_add_norm (by push_cast; linarith)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [mj]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem Dec.bound {a : K × (ι → ℂ) → ℂ} (ha : Dec a) (M : ℕ) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ k x b : _,
    ‖a (k, x + b)‖ * (1 + ‖x‖) ^ M ≤ C * (1 + ‖b‖) ^ N * mj x := by
  obtain ⟨C, hC⟩ := ha (M + (Module.finrank ℝ (ι → ℂ) + 1))
  refine ⟨max C 0, M + (Module.finrank ℝ (ι → ℂ) + 1), le_max_right _ _, fun k x b => ?_⟩
  rw [mj, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_assoc, ← pow_add]
  have h1 : 1 + ‖x‖ ≤ (1 + ‖x + b‖) * (1 + ‖b‖) := by
    have : ‖x‖ ≤ ‖x + b‖ + ‖b‖ := by simpa using norm_sub_le (x + b) b
    nlinarith [norm_nonneg (x + b), norm_nonneg b]
  calc _ ≤ ‖a (k, x + b)‖ * ((1 + ‖x + b‖) * (1 + ‖b‖)) ^ (M + (Module.finrank ℝ (ι → ℂ) + 1)) := by gcongr
    _ = ‖a (k, x + b)‖ * (1 + ‖x + b‖) ^ (M + (Module.finrank ℝ (ι → ℂ) + 1)) * (1 + ‖b‖) ^ (M + (Module.finrank ℝ (ι → ℂ) + 1)) := by
        rw [mul_pow, mul_assoc]
    _ ≤ _ := by gcongr; exact (hC k _).trans (le_max_left _ _)

theorem continuousOn_rationalWeight (κ : ι → ℕ) (e : ℕ) : ContinuousOn (r0 κ e) {x | ∀ w, x w ≠ 0} := by
  refine continuousOn_finsetProd _ fun w _ => ?_
  refine ContinuousOn.mul (ContinuousOn.pow (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_) _) (by fun_prop)
  simpa using hx w

theorem open_U : IsOpen {p : K × (ι → ℂ) | ∀ w, p.2 w ≠ 0} := by
  simp only [setOf_forall]
  exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const

structure Prp (π : K × (ι → ℂ) → X) (x₀ : X) : Prop where
  cont : Continuous π
  pt : ∃ p, π p = x₀
  cpt : ∃ (ε : ℝ) (S : Set (K × (ι → ℂ))), 0 < ε ∧ IsCompact S ∧ (∀ p ∈ S, ∀ w, p.2 w ≠ 0) ∧ ∀ p, dist (π p) x₀ ≤ ε → p ∈ S

theorem coreA (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {π : K × (ι → ℂ) → X} {x₀ : X} (hπ : Prp π x₀)
    (κ : ι → ℕ) (e : ℕ) {a : K × (ι → ℂ) → ℂ} (ha : Continuous a) (hd : Dec a) (c : ℂ)
    (hpos : ∀ p, π p = x₀ → 0 < (a p * r0 κ e p.2 * c).re)
    (h : ∀ η, ∫ k, ∫ x, ch ⟪η, π (k, x)⟫ * a (k, x) * r0 κ e x ∂volume ∂μ = 0) : False := by
  obtain ⟨ε, S, hε, hS, hSU, hb⟩ := hπ.cpt
  obtain ⟨p₀, h₀⟩ := hπ.pt
  obtain ⟨φ, -, -, hφ⟩ := core_bump (μ.prod volume) π hπ.cont x₀ (fun p => a p * r0 κ e p.2 * c) _ S open_U
    ((ha.continuousOn.mul ((continuousOn_rationalWeight κ e).comp continuous_snd.continuousOn fun p hp => hp)).mul continuousOn_const)
    hS hSU ε hε hb hpos p₀ h₀
  obtain ⟨C, N, -, hC⟩ := hd.bound (2 * e * Fintype.card ι)
  have hi : Integrable (fun p : K × (ι → ℂ) => a p * r0 κ e p.2) (μ.prod volume) := by
    refine ((integrable_const C).mul_prod integrable_mj).mono'
      (ha.measurable.mul ((measurable_reduced_size κ e).comp measurable_snd)).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have := hC p.1 p.2 0
    simp only [add_zero, norm_zero, one_pow, mul_one] at this
    rw [norm_mul]
    exact le_trans (by gcongr; exact norm_rationalWeight_le κ e p.2) this
  refine hφ (fourier_vanish _ π hπ.cont.measurable _ (hi.mul_const c) (fun η => ?_) φ)
  simp only [← mul_assoc]
  rw [integral_mul_const, integral_prod, h, zero_mul]
  simp only [mul_assoc]
  exact hi.bdd_mul (c := 1) (continuous_ch.comp (continuous_const.inner hπ.cont)).aestronglyMeasurable
    (Eventually.of_forall fun q => (norm_ch _).le)

theorem pr_add (x y t : ι → ℂ) : pr (x + y) t = pr x t + pr y t := by
  simp [pr, add_mul, Finset.sum_add_distrib, mul_add]

theorem FT_shift (g : (ι → ℂ) → ℂ) (b t : ι → ℂ) : ∫ x, ch (-pr x t) * g (x + b) = ch (pr b t) * FT g t := by
  rw [FT, ← integral_const_mul, ← integral_add_right_eq_self (fun x => ch (pr b t) * (ch (-pr x t) * g x)) b]
  congr 1; funext x
  rw [← mul_assoc, ← ch_add, pr_add]; congr 2; ring

theorem coreB [FirstCountableTopology K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {π : K × (ι → ℂ) → X} {x₀ : X} (hπ : Prp π x₀)
    (κ : ι → ℕ) (e : ℕ) (hκ : ∀ w, 2 * e < κ w) {a : K × (ι → ℂ) → ℂ} (ha : Continuous a) (hd : Dec a) (c : ℂ)
    (β : K × X → ι → ℂ) (hβ : Continuous β) (D : ℝ) (hD : ∀ k η, ‖β (k, η)‖ ≤ D * ‖η‖)
    (hp : ∀ k η t, pr (β (k, η)) t = ⟪η, π (k, t)⟫)
    (hpos : ∀ p, π p = x₀ → 0 < (FT (fun x => a (p.1, x)) p.2 * ((r0 κ e p.2)⁻¹ * ((nm p.2 : ℝ) : ℂ)⁻¹) * c).re)
    (h : ∀ η, ∫ k, ∫ x, a (k, x + β (k, η)) * r0 κ e x ∂volume ∂μ = 0) : False := by
  obtain ⟨ε, S, hε, hS, hSU, hb⟩ := hπ.cpt
  obtain ⟨p₀, h₀⟩ := hπ.pt
  obtain ⟨C, N, hC0, hC⟩ := hd.bound (2 * e * Fintype.card ι)
  have hle : ∀ k x b, ‖a (k, x + b)‖ ≤ C * (1 + ‖b‖) ^ N * mj x := fun k x b =>
    le_trans (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg x]))) (hC k x b)
  have hler : ∀ k x b, ‖a (k, x + b) * r0 κ e x‖ ≤ C * (1 + ‖b‖) ^ N * mj x := fun k x b => by
    rw [norm_mul]; exact le_trans (by gcongr; exact norm_rationalWeight_le κ e x) (hC k x b)
  have hF : Continuous fun p : K × (ι → ℂ) => FT (fun x => a (p.1, x)) p.2 := by
    have : Continuous fun p : K × (ι → ℂ) => ∫ x, ch (-pr x p.2) * a (p.1, x) := by
      have hu : Continuous (Function.uncurry fun (p : K × (ι → ℂ)) (x : ι → ℂ) => ch (-pr x p.2) * a (p.1, x)) :=
        (continuous_ch.comp (continuous_pr.comp (f := fun q : (K × (ι → ℂ)) × (ι → ℂ) => (q.2, q.1.2)) (by fun_prop)).neg).mul
          (ha.comp (f := fun q : (K × (ι → ℂ)) × (ι → ℂ) => (q.1.1, q.2)) (by fun_prop))
      refine continuous_of_dominated (bound := fun x => C * mj x) (fun p => (hu.uncurry_left p).aestronglyMeasurable)
        (fun p => Eventually.of_forall fun x => ?_) (integrable_mj.const_mul C)
        (Eventually.of_forall fun x => hu.uncurry_right x)
      rw [norm_mul, norm_ch, one_mul]
      simpa using hle p.1 x 0
    exact this
  obtain ⟨φ, -, hint, hφ⟩ := core_bump (μ.prod volume) π hπ.cont x₀
    (fun p => FT (fun x => a (p.1, x)) p.2 * ((r0 κ e p.2)⁻¹ * ((nm p.2 : ℝ) : ℂ)⁻¹) * c) _ S open_U
    ((hF.continuousOn.mul ((((continuousOn_rationalWeight κ e).comp continuous_snd.continuousOn fun p hp => hp).inv₀ fun p hp => rationalWeight_ne_zero κ e hp).mul
      ((Complex.continuous_ofReal.comp (continuous_nm.comp continuous_snd)).continuousOn.inv₀ fun p hp => by
        simpa using (nm_pos hp).ne'))).mul continuousOn_const) hS hSU ε hε hb hpos p₀ h₀
  obtain ⟨b, hb'⟩ := exists_density φ
  obtain ⟨Z, hZ⟩ := tate κ e hκ
  have hD0 : ∀ η : X, ∀ k, (1 + ‖β (k, η)‖) ^ N ≤ (1 + |D|) ^ N * (1 + ‖η‖) ^ N := fun η k => by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    nlinarith [hD k η, le_abs_self D, abs_nonneg D, norm_nonneg η]
  have hbi : Integrable fun η : X => C * ((1 + |D|) ^ N * (1 + ‖η‖) ^ N) * ‖b η‖ := by
    have : Integrable fun η : X => (1 + ‖η‖) ^ N * ‖b η‖ := by
      simp only [add_comm (1 : ℝ), add_pow, one_pow, mul_one, Finset.sum_mul]
      exact integrable_finsetSum _ fun i _ => by
        simpa [mul_right_comm] using (b.integrable_pow_mul volume i).mul_const (N.choose i : ℝ)
    simpa [mul_assoc] using this.const_mul (C * (1 + |D|) ^ N)
  have hcont : Continuous fun q : (K × (ι → ℂ)) × X => b q.2 * a (q.1.1, q.1.2 + β (q.1.1, q.2)) := by
    have := b.continuous; fun_prop
  have bd : ∀ (k : K) (x : ι → ℂ) (η : X) (t : ℂ), ‖t‖ ≤ C * (1 + ‖β (k, η)‖) ^ N * mj x →
      ‖b η * t‖ ≤ mj x * (C * ((1 + |D|) ^ N * (1 + ‖η‖) ^ N) * ‖b η‖) := fun k x η t ht => by
    have hm : 0 ≤ mj x := by unfold mj; positivity
    rw [norm_mul]
    calc _ ≤ ‖b η‖ * (C * ((1 + |D|) ^ N * (1 + ‖η‖) ^ N) * mj x) := by
          gcongr; exact ht.trans (by gcongr; exact hD0 η k)
      _ = _ := by ring
  have I3 : Integrable (fun q : (K × (ι → ℂ)) × X => b q.2 * (a (q.1.1, q.1.2 + β (q.1.1, q.2)) * r0 κ e q.1.2))
      ((μ.prod volume).prod volume) := by
    refine (((integrable_const (1 : ℝ)).mul_prod integrable_mj).mul_prod hbi).mono' ?_ (Eventually.of_forall fun q => ?_)
    · simp only [← mul_assoc]
      exact (hcont.measurable.mul ((measurable_reduced_size κ e).comp (measurable_snd.comp measurable_fst))).aestronglyMeasurable
    · rw [one_mul]; exact bd _ _ _ _ (hler _ _ _)
  have I2 : ∀ k, Integrable (fun q : (ι → ℂ) × X => b q.2 * a (k, q.1 + β (k, q.2))) (volume.prod volume) := fun k =>
    (integrable_mj.mul_prod hbi).mono' (hcont.comp (f := fun q : (ι → ℂ) × X => ((k, q.1), q.2)) (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun q => bd _ _ _ _ (hle _ _ _))
  have I2r : ∀ k, Integrable (fun q : (ι → ℂ) × X => b q.2 * (a (k, q.1 + β (k, q.2)) * r0 κ e q.1)) (volume.prod volume) := fun k => by
    refine (integrable_mj.mul_prod hbi).mono' ?_ (Eventually.of_forall fun q => bd _ _ _ _ (hler _ _ _))
    simp only [← mul_assoc]
    exact (I2 k).1.mul ((measurable_reduced_size κ e).comp measurable_fst).aestronglyMeasurable
  let H : K → (ι → ℂ) → ℂ := fun k x => ∫ η, b η * a (k, x + β (k, η))
  have hHr : ∀ k x, H k x * r0 κ e x = ∫ η, b η * (a (k, x + β (k, η)) * r0 κ e x) := fun k x => by
    simp only [H, ← mul_assoc]; rw [integral_mul_const]
  have hFH : ∀ k t, FT (H k) t = φ (π (k, t)) * FT (fun x => a (k, x)) t := fun k t => by
    have hi : Integrable (fun q : (ι → ℂ) × X => ch (-pr q.1 t) * (b q.2 * a (k, q.1 + β (k, q.2)))) (volume.prod volume) :=
      (I2 k).bdd_mul (c := 1) (continuous_ch.comp (continuous_pr.comp (continuous_fst.prodMk continuous_const)).neg).aestronglyMeasurable
        (Eventually.of_forall fun q => (norm_ch _).le)
    calc FT (H k) t = ∫ x, ∫ η, ch (-pr x t) * (b η * a (k, x + β (k, η))) := by
          rw [FT]; congr 1; funext x; rw [integral_const_mul]
      _ = ∫ η, ∫ x, ch (-pr x t) * (b η * a (k, x + β (k, η))) := integral_integral_swap hi
      _ = _ := by
          rw [hb', ← integral_mul_const]; congr 1; funext η
          simp only [mul_left_comm _ (b η)]
          rw [integral_const_mul, FT_shift (fun x => a (k, x)), hp]; ring
  have h0 : ∫ k, ∫ x, H k x * r0 κ e x ∂volume ∂μ = 0 := by
    simp only [hHr]
    rw [← integral_prod _ I3.integral_prod_left, integral_integral_swap I3]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [I3.swap.prod_right_ae] with η hη
    refine (integral_prod _ hη).trans ?_
    simp only [Function.comp, Prod.swap, integral_const_mul, h, mul_zero]
  apply hφ
  by_cases hc : c = 0
  · simp [hc]
  rw [integral_prod _ hint]
  have : ∀ᵐ k ∂μ, ∫ t, φ (π (k, t)) * (FT (fun x => a (k, x)) t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹) * c) =
      (Z * c) * ∫ x, H k x * r0 κ e x := by
    filter_upwards [hint.prod_right_ae] with k hk
    have e1 : ∀ t, φ (π (k, t)) * (FT (fun x => a (k, x)) t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹) * c) =
        FT (H k) t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹) * c := fun t => by rw [hFH]; ring
    simp only [e1] at hk ⊢
    rw [integral_mul_const, hZ (H k) (I2 k).integral_prod_left (by simpa only [hHr] using (I2r k).integral_prod_left)
      (by simpa [mul_assoc, hc] using hk.mul_const c⁻¹)]
    ring
  rw [integral_congr_ae this, integral_const_mul, h0, mul_zero]

end PositivityTheory.ThKG.Loc.Bump

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate

variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]

abbrev XS (j : Type) : Type := PiLp 2 fun _ : j => ℂ

def pim (ξ : K → ι → n → ℂ) (p : K × (ι → ℂ)) : XS (ι × n) := WithLp.toLp 2 fun j => 2 * (p.2 j.1 * ξ p.1 j.1 j.2)

def bet (ξ : K → ι → n → ℂ) (q : K × XS (ι × n)) : ι → ℂ := fun w => ∑ i, ξ q.1 w i * conj (q.2 (w, i))

omit [TopologicalSpace K] in
theorem pr_bet (ξ : K → ι → n → ℂ) (k : K) (η : XS (ι × n)) (t : ι → ℂ) : pr (bet ξ (k, η)) t = ⟪η, pim ξ (k, t)⟫ := by
  simp only [pr, bet, pim, PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_mul, Complex.re_sum, Finset.mul_sum, Complex.inner]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
  simp; ring

theorem cont_bet {ξ : K → ι → n → ℂ} (h : Continuous ξ) : Continuous (bet ξ) := by unfold bet; fun_prop

theorem bet_le [CompactSpace K] {ξ : K → ι → n → ℂ} (h : Continuous ξ) : ∃ D : ℝ, ∀ k η, ‖bet ξ (k, η)‖ ≤ D * ‖η‖ := by
  obtain ⟨C, hC⟩ := (isCompact_range h).isBounded.exists_norm_le
  refine ⟨Fintype.card n * |C|, fun k η => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_⟩
  refine (norm_sum_le _ _).trans ?_
  rw [mul_assoc, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
  rw [norm_mul, Complex.norm_conj]
  have h1 : ‖ξ k w i‖ ≤ |C| := ((norm_le_pi_norm _ i).trans (norm_le_pi_norm _ w)).trans ((hC _ ⟨k, rfl⟩).trans (le_abs_self C))
  exact mul_le_mul h1 (PiLp.norm_apply_le η (w, i)) (norm_nonneg _) (abs_nonneg _)

theorem exists_lb {α : Type} [TopologicalSpace α] [CompactSpace α] {g : α → ι → ℝ} (h : ∀ w, Continuous fun a => g a w)
    (hp : ∀ a w, 0 < g a w) : ∃ m : ℝ, 0 < m ∧ ∀ a w, m ≤ g a w := by
  letI : TopologicalSpace ι := ⊥
  haveI : DiscreteTopology ι := ⟨rfl⟩
  have hc : Continuous fun q : α × ι => g q.1 q.2 := continuous_prod_of_discrete_right.2 h
  obtain ⟨m, hm, hb⟩ := isCompact_univ.exists_forall_le' hc.continuousOn (a := 0) fun q _ => hp q.1 q.2
  exact ⟨m, hm, fun a w => hb (a, w) trivial⟩

theorem prp_pim [CompactSpace K] {ξ : K → ι → n → ℂ} (h : Continuous ξ) (hne : ∀ k w, ξ k w ≠ 0) (k₁ : K) :
    Prp (pim ξ) (pim ξ (k₁, 1)) := by
  refine ⟨by unfold pim; fun_prop, ⟨_, rfl⟩, ?_⟩
  obtain ⟨m, hm, hb⟩ := exists_lb (g := fun k w => ‖ξ k w‖) (fun w => by fun_prop) fun k w => norm_pos_iff.2 (hne k w)
  refine ⟨m, {p | ∀ w, m / 2 ≤ ‖p.2 w‖ * ‖ξ p.1 w‖} ∩ univ ×ˢ Metric.closedBall 0 ((‖ξ k₁‖ + m) / m), hm, ?_, ?_, fun p hp => ?_⟩
  · refine IsCompact.inter_left (isCompact_univ.prod (isCompact_closedBall _ _)) ?_
    simp only [setOf_forall]
    exact isClosed_iInter fun w => isClosed_le continuous_const (by fun_prop)
  · intro p hp w h0
    have := hp.1 w
    rw [h0, norm_zero, zero_mul] at this
    linarith
  · have key : ∀ w, ‖p.2 w • ξ p.1 w - ξ k₁ w‖ ≤ m / 2 := fun w => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
      have h1 := (PiLp.norm_apply_le (pim ξ p - pim ξ (k₁, 1)) (w, i)).trans ((dist_eq_norm _ _).symm.le.trans hp)
      have h2 : (pim ξ p - pim ξ (k₁, 1)) (w, i) = 2 * (p.2 w • ξ p.1 w - ξ k₁ w) i := by simp [pim]; ring
      rw [h2, norm_mul, Complex.norm_ofNat] at h1
      linarith
    refine ⟨fun w => ?_, trivial, ?_⟩
    · have := norm_sub_norm_le (ξ k₁ w) (p.2 w • ξ p.1 w)
      rw [norm_sub_rev, norm_smul] at this
      linarith [key w, hb k₁ w]
    · rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_
      have := norm_sub_norm_le (p.2 w • ξ p.1 w) (ξ k₁ w)
      rw [norm_smul] at this
      rw [le_div_iff₀ hm]
      nlinarith [key w, hb p.1 w, norm_le_pi_norm (ξ k₁) w, norm_nonneg (p.2 w)]

theorem exists_FT_ne {a : (ι → ℂ) → ℂ} (ha : Continuous a) (hi : Integrable a) (h0 : a 0 ≠ 0) : ∃ t, FT a t ≠ 0 := by
  by_contra hn
  push Not at hn
  let π : (ι → ℂ) → XS ι := fun x => WithLp.toLp 2 fun w => 2 * x w
  have hπ : Continuous π := by fun_prop
  obtain ⟨φ, -, -, hφ⟩ := core_bump volume π hπ 0 (fun x => a x * (a 0)⁻¹) univ (Metric.closedBall 0 1) isOpen_univ
    (ha.mul continuous_const).continuousOn (isCompact_closedBall _ _) (subset_univ _) 1 one_pos (fun x hx => by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_
      have h1 := (PiLp.norm_apply_le (π x) w).trans ((dist_zero_right _).symm.le.trans hx)
      simp only [π, norm_mul, Complex.norm_ofNat] at h1
      linarith [norm_nonneg (x w)]) (fun x hx => by
      have : x = 0 := funext fun w => by simpa [π] using congrArg (fun y : XS ι => y w) hx
      simp [this, h0]) 0 (by ext w; simp [π])
  refine hφ (fourier_vanish _ π hπ.measurable _ (hi.mul_const _) (fun η => ?_) φ)
  simp only [← mul_assoc]
  rw [integral_mul_const]
  have := hn fun w => -conj (η w)
  rw [FT] at this
  refine mul_eq_zero_of_left (Eq.trans ?_ this) _
  congr 1; funext x; congr 2
  simp only [pr, π, PiLp.inner_apply, Complex.inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp; ring

theorem rationalWeight_succ_mul_inv_norm (κ : ι → ℕ) (e : ℕ) {x : ι → ℂ} (hx : ∀ w, x w ≠ 0) :
    r0 κ (e + 1) x * ((∏ w, ‖x w‖ ^ 2 : ℝ) : ℂ)⁻¹ = r0 κ e x := by
  have : ((∏ w, ‖x w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hx).ne'
  rw [mul_inv_eq_iff_eq_mul₀ this]
  push_cast
  rw [r0, r0, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => by ring

theorem rationalWeight_eq_mul_norm_pow (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : r0 κ e x = r0 κ 0 x * ((nm x : ℝ) : ℂ) ^ e := by
  simp only [r0, nm]
  push_cast
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => by ring

omit [TopologicalSpace K] in
theorem Dec.integrable {a : K × (ι → ℂ) → ℂ} (hd : Dec a) (k : K) (ha : Continuous fun x => a (k, x)) : Integrable fun x => a (k, x) := by
  obtain ⟨C, N, -, hC⟩ := hd.bound 0
  exact (integrable_mj.const_mul C).mono' ha.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hC k x 0)

end PositivityTheory.ThKG.Loc.Bump

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr PositivityTheory.ThKF

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

theorem rho_rho (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d) :
    M.co.rho ψ u (M.co.rho ψ u' Φ) = ψ (⅟(2 : AF F) * sy σ X W u u') • M.co.rho ψ (u + u') Φ := by
  funext x
  have h2 : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self _
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add, Prod.fst_add, Prod.snd_add, sy, M.co.2 u u', ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-((M.co.e u).1 ⬝ᵥ (M.co.e u').2)) * h2

theorem rho_zero (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (Φ : Fn F n d) : M.co.rho ψ 0 Φ = Φ := by
  funext x; simp [Darboux.rho, schr]

theorem heisenberg_action_add_of_orthogonal (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {u u' : Matrix (Fin n) (Fin d) (AE F E)} (h : sy σ X W u u' = 0) (Φ : Fn F n d) :
    M.co.rho ψ (u + u') Φ = M.co.rho ψ u (M.co.rho ψ u' Φ) := by
  rw [rho_rho, h, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem rho_comm (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d) :
    M.co.rho ψ u (M.co.rho ψ u' Φ) = ψ (sy σ X W u u') • M.co.rho ψ u' (M.co.rho ψ u Φ) := by
  have h2 : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self _
  rw [rho_rho, rho_rho, smul_smul, ← AddChar.map_add_eq_mul, add_comm u' u]
  congr 2
  simp only [sy, M.co.2]
  linear_combination ((M.co.e u).1 ⬝ᵥ (M.co.e u').2 - (M.co.e u').1 ⬝ᵥ (M.co.e u).2) * h2

variable (σ) in

def bA (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → AE F E) : AE F E := x ⬝ᵥ incM F J *ᵥ fun i => cA σ (y i)

theorem sy_vv (x x' : Fin n → AE F E) (y y' : Fin d → AE F E) :
    sy σ X W (Matrix.vecMulVec x y) (Matrix.vecMulVec x' y') = Algebra.trace (AF F) (AE F E) (-(bA σ X.J x x' * bA σ W.J y y')) := by
  simp only [sy, symp, hTens, bA, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, map_mul, neg_one_mul]
  congr 2
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum _ _ (y j), Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem bA_inc (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : bA σ J (incV F x) (incV F y) = inclR (F := F) (AF F) (form σ J x y) := by
  simp only [bA, form, dotProduct, Matrix.mulVec, map_sum, map_mul]
  rfl

theorem bA_smul (J : Matrix (Fin n) (Fin n) E) (a b : AE F E) (x y : Fin n → AE F E) : bA σ J (a • x) (b • y) = a * cA σ b * bA σ J x y := by
  simp only [bA, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem bA_mat {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (x y : Fin n → AE F E) : bA σ J (mat g *ᵥ x) (mat g *ᵥ y) = bA σ J x y := by
  have h : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have e : (fun i => cA σ ((mat g *ᵥ y) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (y i) :=
    funext fun i => RingHom.map_mulVec (cA σ : AE F E →+* AE F E) (mat g) y i
  simp only [bA]
  conv_rhs => rw [← h]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

theorem om_rho {M : Model σ X W} {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') (g : UA σ X.J)
    (x : Fin n → AE F E) (y : Fin d → AE F E) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    om (g, 1) (M.co.rho B.ψ (Matrix.vecMulVec x y) Φ) = M.co.rho B.ψ (Matrix.vecMulVec (mat g *ᵥ x) y) (om (g, 1) Φ) := by
  rw [hP.weil.isUSplitting.impl (g, 1) _ Φ hΦ]
  congr 1
  change mat g * _ * (1 : Matrix _ _ _)ᵀ = _
  rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec]

theorem om_sch {M : Model σ X W} {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') (g) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    om g Φ ∈ schA F (Fin n × Fin d) := hP.weil.isUSplitting.pres g Φ hΦ

abbrev PV (M : Model σ X W) (f : SInf F (Fin n × Fin d)) : Fn F n d := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac

theorem pv_sch {M : Model σ X W} (hM : M.IsGood B.ψ) (f) : PV M f ∈ schA F (Fin n × Fin d) :=
  (rest_pure f M.vac (fun v => (hM.vac v).1) hM.std).2

theorem pv_act {M : Model σ X W} (hM : M.IsGood B.ψ) {S} {f f₁ : SInf F (Fin n × Fin d)} (h : Acts (evI F) S f f₁) : S (PV M f) = PV M f₁ :=
  h _ (rest_pure f M.vac (fun v => (hM.vac v).1) hM.std)

theorem pv_smul (M : Model σ X W) (c : ℂ) (f) : PV M (c • f) = c • PV M f := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pv_rho {M : Model σ X W} (hB : B.IsGood σ) (hM : M.IsGood B.ψ) {u} (hu : At (evI F) u) (f) :
    ∃ f₁, M.co.rho B.ψ u (PV M f) = PV M f₁ :=
  let ⟨f₁, h⟩ := (archHeis_of F E σ B n d X W M hB).2 u hu f; ⟨f₁, pv_act hM h⟩

theorem one_at {J : Matrix (Fin n) (Fin n) E} (Y : Spc F E n) : (1 : UA σ Y.J) ∈ UAt σ Y (evI F) := fun a _ => by
  rw [mat_one, sub_self, smul_zero]

theorem pv_opI (hA : ArchOp) {M : Model σ X W} {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') {u} (hu : At (evI F) u)
    {k} (hk : k ∈ UAt σ X (evI F)) (f) :
    PV M (opI (fun Φ => M.co.rho B.ψ u (om (k, 1) Φ)) f) = M.co.rho B.ψ u (om (k, 1) (PV M f)) := by
  obtain ⟨T, hT, -⟩ := hA F E σ B n d X W M χX χW om r s r' s' hP k hk 1 (one_at (J := W.J) W)
  obtain ⟨f₂, h₂⟩ := (archHeis_of F E σ B n d X W M hP.base).2 u hu (T f)
  have h : ∃ f₁ : SInf F _, Acts (evI F) (fun Φ => M.co.rho B.ψ u (om (k, 1) Φ)) f f₁ := ⟨f₂, fun q hq => by
    have e := hT.2 f q hq
    beta_reduce
    rw [e]
    exact h₂ q ⟨hq.1, e ▸ om_sch hP _ hq.2⟩⟩
  rw [opI, dif_pos h]
  exact (pv_act hP.good h.choose_spec).symm

open Classical in

def unp (M : Model σ X W) (l : SInf F (Fin n × Fin d) →L[ℂ] ℂ) (Ψ : Fn F n d) : ℂ :=
  if h : ∃ g, Ψ = PV M g then l h.choose else 0

theorem un_pv {M : Model σ X W} (hM : M.IsGood B.ψ) (l) (g) : unp M l (PV M g) = l g := by
  have h : ∃ g', PV M g = PV M g' := ⟨g, rfl⟩
  rw [unp, dif_pos h, ← pure_inj M.vac (fun v => (hM.vac v).2.1) hM.std h.choose_spec]

theorem e_pv {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) {e ei ev} (h : IsEvLoc M M₁ e ei ev) (f) :
    e (PV M f) = PV M₁ (ei f) := by
  rw [h.pure f M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)]
  congr 1
  exact funext fun v => (h.vac v).1

theorem un_e {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {e ei ev} (h : IsEvLoc M M₁ e ei ev) (l) (f) :
    unp M₁ l (e (PV M f)) = l (ei f) := by rw [e_pv hM h, un_pv hM₁]

theorem un_e_smul {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {e ei ev} (h : IsEvLoc M M₁ e ei ev) (l)
    (c : ℂ) {Ψ} (hΨ : ∃ f, Ψ = PV M f) : unp M₁ l (e (c • Ψ)) = c * unp M₁ l (e Ψ) := by
  obtain ⟨f, rfl⟩ := hΨ
  rw [← pv_smul, un_e hM hM₁ h, un_e hM hM₁ h, map_smul, map_smul, smul_eq_mul]

theorem at_mulVec {g : Matrix (Fin n) (Fin n) (AE F E)} {x : Fin n → AE F E} (h : At (evI F) x) : At (evI F) (g *ᵥ x) := fun a ha => by
  rw [← Matrix.mulVec_smul, h a ha, Matrix.mulVec_zero]

theorem at_vv {x : Fin n → AE F E} (h : At (evI F) x) (y : Fin d → AE F E) : At (evI F) (Matrix.vecMulVec x y) := fun a ha => by
  rw [← Matrix.smul_vecMulVec, h a ha, Matrix.zero_vecMulVec]

theorem at_smul2 {N : Type} [AddCommGroup N] [Module (AF F) N] [Module (AE F E) N] [IsScalarTower (AF F) (AE F E) N] {c : AE F E}
    (h : At (evI F) c) (x : N) : At (evI F) (c • x) := fun a ha => by rw [← smul_assoc, h a ha, zero_smul]

theorem mix_un (hA : ArchOp) {M : Model σ X W} {M₁ : Model σ X₁ W₁} {χX χW om om₁ r s r' s' r₁ s₁ r₁' s₁'}
    (hP : IsPair B M χX χW om r s r' s') (hP₁ : IsPair B M₁ χX χW om₁ r₁ s₁ r₁' s₁') {H : Plane E n n₁} {H' : Plane E d d₁} {i j}
    (hH : H.IsAdapted σ B X X₁ i j) {e ei ev} (h : IsEvLoc M M₁ e ei ev) {rX rW} (hm : Mix2 H H' χX χW rX rW om om₁ e)
    {l : SInf F _ →L[ℂ] ℂ} (hl : ∀ g ∈ UAt σ X₁ (evI F), ∀ f f₁ : SInf F _, Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f)
    {k} (hk : k ∈ UAt σ X (evI F)) {t : (AE F E)ˣ} (ht : mat k *ᵥ incV F H.x = t.1 • incV F H.x) :
    (∀ Ψ, (∃ f, Ψ = PV M f) → unp M₁ l (e (om (k, 1) Ψ)) = (χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) * unp M₁ l (e Ψ)) ∧
    ∃ (U : Fin n₁ → AE F E) (c : AE F E), mat k⁻¹ *ᵥ incV F H.y = incM F H.ι *ᵥ U + c • incV F H.x + cA σ t.1 • incV F H.y := by
  obtain ⟨ε, A', hF⟩ := isFr hP.base (Or.inl hP.herm) hH
  obtain ⟨u, hu, g₁, m, hL, rfl, hg⟩ := stab_dec hP.base.cm hF (det_ne (Or.inl hP.herm)) k t ht
  have hg₁ : g₁ ∈ UAt σ X₁ (evI F) := fun a ha => by
    have e1 : mat g₁ - 1 = (incM F A' * (mat (u * m) - 1) * fr (incM F H.ι) (incV F H.x) (incV F H.y)).toBlocks₁₁ := by
      rw [hg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, (IsFr.ad hF).inv2]
      ext a b; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    have e2 : a • (incM F A' * (mat (u * m) - 1) * fr (incM F H.ι) (incV F H.x) (incV F H.y)) = 0 := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hk a ha, Matrix.mul_zero, Matrix.zero_mul]
    rw [e1]
    ext b c
    exact congrFun (congrFun e2 (Sum.inl b)) (Sum.inl c)
  constructor
  · rintro _ ⟨f, rfl⟩
    have := hm t g₁ m hL u hu 1 1 1 levi_one 1 (one_mem _) _ (pv_sch hP.good f)
    rw [mul_one] at this
    obtain ⟨T, hT, -⟩ := hA F E σ B n₁ d₁ X₁ W₁ M₁ χX χW om₁ _ _ _ _ hP₁ g₁ hg₁ 1 (one_at (J := W₁.J) W₁)
    rw [this, e_pv hP.good h, pv_act hP₁.good (hT.2 _), ← pv_smul, un_pv hP₁.good, un_pv hP₁.good, map_smul, hl g₁ hg₁ _ _ (hT.2 _)]
    simp
  · obtain ⟨U, c, hU⟩ := (IsFr.ad hF).fix_y (PositivityTheory.ThKG.Tow.Levi.cA_cA hP.base.cm) (u⁻¹).2 (mem_unip.1 (inv_mem hu)).1
    have h2 := levi_inv hL
    refine ⟨mat g₁⁻¹ *ᵥ U, c * (t⁻¹).1, ?_⟩
    rw [mul_inv_rev, mat_mul, ← Matrix.mulVec_mulVec]
    change mat m⁻¹ *ᵥ ((u⁻¹).1.1 *ᵥ _) = _
    rw [hU, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, h2.1, h2.2.1, levi_vec h2, inv_inv, smul_smul]
    abel

end PositivityTheory.ThKG.Loc.Bump

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr PositivityTheory.ThKF
open scoped ComplexConjugate

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}
  {lift : (InfinitePlace F → ℂ) → AE F E}

theorem IsLift.ext (h : IsLift σ B lift) {a b : AE F E} (hab : At (evI F) (a - b)) (e : ∀ w, piInf (B.emb w) a = piInf (B.emb w) b) :
    a = b := by
  have h0 : lift (fun w => piInf (B.emb w) 0) = 0 := h.inv 0 fun u _ => smul_zero u
  rw [← sub_eq_zero, ← h.inv _ hab, ← h0]
  congr 1; funext w; rw [map_sub, e, sub_self, map_zero]

theorem at_sub {N : Type} [AddCommGroup N] [Module (AF F) N] {a b : N} (ha : At (evI F) a) (hb : At (evI F) b) : At (evI F) (a - b) :=
  fun u hu => by rw [smul_sub, ha u hu, hb u hu, sub_zero]

theorem at_add {N : Type} [AddCommGroup N] [Module (AF F) N] {a b : N} (ha : At (evI F) a) (hb : At (evI F) b) : At (evI F) (a + b) :=
  fun u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]

theorem at_mul {a : AE F E} (ha : At (evI F) a) (b : AE F E) : At (evI F) (a * b) := at_smul2 ha b

theorem IsLift.eq (h : IsLift σ B lift) {a : AE F E} (ha : At (evI F) a) {c} (e : ∀ w, piInf (B.emb w) a = c w) : a = lift c :=
  h.ext (at_sub ha (h.supp c)) fun w => by rw [e, h.pi]

theorem IsLift.ch (h : IsLift σ B lift) {a b : AE F E} (ha : At (evI F) a) {x y : InfinitePlace F → ℂ} (hx : ∀ w, (piInf (B.emb w) (a * b)).re = (x w * y w).re) :
    B.ψ (Algebra.trace (AF F) (AE F E) (a * b)) = ch (-pr x y) := by
  rw [h.psi _ (at_mul ha b), Bump.ch, pr]
  simp only [hx]
  congr 1; push_cast; ring

theorem pi_bA (h : IsLift σ B lift) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → AE F E) (w) : piInf (B.emb w) (bA σ J x y) =
    (fun i => piInf (B.emb w) (x i)) ⬝ᵥ J.map (B.emb w).1 *ᵥ fun i => conj (piInf (B.emb w) (y i)) := by
  simp only [bA, dotProduct, Matrix.mulVec, map_sum, map_mul, h.conj, incM, Matrix.map_apply, h.incl]

variable (B) in

def xi (x : Fin n → E) {S : Subgroup (UA σ X.J)} (k : S) : InfinitePlace F → Fin n → ℂ :=
  fun w i => piInf (B.emb w) ((mat k.1⁻¹ *ᵥ incV F x) i)

theorem cont_xi (h : IsLift σ B lift) (x : Fin n → E) (S : Subgroup (UA σ X.J)) : Continuous (xi B x (S := S)) := by
  refine continuous_pi fun w => continuous_pi fun i => ?_
  simp only [xi, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine continuous_finsetSum _ fun j _ => ((h.cont w).comp ?_).mul continuous_const
  have : Continuous fun k : S => (((k.1.1)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) :=
    Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact (continuous_apply j).comp ((continuous_apply i).comp this)

theorem xi_ne (h : IsLift σ B lift) {x y : Fin n → E} (hxy : form σ X.J x y = 1) {S : Subgroup (UA σ X.J)} (k : S) (w) : xi B x k w ≠ 0 := by
  intro h0
  have := pi_bA h X.J (mat k.1⁻¹ *ᵥ incV F x) (mat k.1⁻¹ *ᵥ incV F y) w
  rw [bA_mat, bA_inc, hxy, map_one, map_one] at this
  change _ = xi B x k w ⬝ᵥ _ at this
  rw [h0, zero_dotProduct] at this
  exact one_ne_zero this

variable (B X) in

def Yv (lift : (InfinitePlace F → ℂ) → AE F E) (η : XS (InfinitePlace F × Fin n)) : Fin n → AE F E :=
  fun i => lift fun w => conj (((X.J.map (B.emb w).1)⁻¹ *ᵥ fun j => conj (η (w, j))) i)

theorem at_Yv (h : IsLift σ B lift) (η) : At (evI F) (Yv X B lift η) := fun u hu => funext fun _ => h.supp _ u hu

theorem pi_beta (h : IsLift σ B lift) {r s} (hX : X.IsHerm σ B r s) (x : Fin n → E) {S : Subgroup (UA σ X.J)} (k : S) (η) (w) :
    piInf (B.emb w) (bA σ X.J (incV F x) (mat k.1 *ᵥ Yv X B lift η)) = bet (xi B x) (k, η) w := by
  rw [← mat_cancel' k.1 (incV F x), bA_mat, pi_bA h]
  simp only [Yv, h.pi, Complex.conj_conj]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (cartan_det (hX.cartan w)).isUnit, Matrix.one_mulVec]
  rfl

theorem sig_pt (h : IsLift σ B lift) {x y : Fin n → E} (hxy : form σ X.J x y = 1) {S : Subgroup (UA σ X.J)}
    (hS : ∀ k ∈ S, k ∈ UAt σ X (evI F)) (p : S × (InfinitePlace F → ℂ)) (hp : pim (xi B x) p = pim (xi B x) ((1 : S), 1)) :
    (∀ w, p.2 w ≠ 0) ∧ ∃ t : (AE F E)ˣ, At (evI F) ((t : AE F E) - 1) ∧ (∀ w, piInf (B.emb w) (t : AE F E) = p.2 w) ∧
      mat p.1.1 *ᵥ incV F x = t.1 • incV F x := by
  have e : ∀ w i, p.2 w * xi B x p.1 w i = xi B x (1 : S) w i := fun w i => by
    simpa [pim] using congrArg (fun z : XS _ => z (w, i)) hp
  have hne : ∀ w, p.2 w ≠ 0 := fun w h0 => xi_ne h hxy (1 : S) w (funext fun i => by rw [← e, h0, zero_mul]; rfl)
  obtain ⟨t, ht, ht'⟩ := h.unit p.2 hne
  refine ⟨hne, t, ht, ht', ?_⟩
  have k1 : t.1 • (mat p.1.1⁻¹ *ᵥ incV F x) = incV F x := funext fun i => by
    refine h.ext ?_ fun w => ?_
    · have a1 : At (evI F) ((mat p.1.1⁻¹ - 1) *ᵥ incV F x) := fun u hu => by
        rw [← Matrix.smul_mulVec, hS _ (inv_mem p.1.2) u hu, Matrix.zero_mulVec]
      have a2 := at_add (at_smul2 ht (mat p.1.1⁻¹ *ᵥ incV F x)) a1
      rw [sub_smul, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_sub_cancel] at a2
      exact fun u hu => congrFun (a2 u hu) i
    · rw [Pi.smul_apply, smul_eq_mul, map_mul, ht']
      refine (e w i).trans ?_
      simp [xi, mat_one]
  conv_lhs => rw [← k1, Matrix.mulVec_smul, mat_cancel']

theorem nu_eq (h : IsLift σ B lift) {ν : Chr F E} {κ : InfinitePlace F → ℕ} (hν : HasExp B.emb ν fun w => κ w) {t : (AE F E)ˣ}
    (ht : At (evI F) ((t : AE F E) - 1)) : (ν t : ℂ) = r0 κ 0 (fun w => piInf (B.emb w) t) ∧
      (absE F E t : ℝ) = nm fun w => piInf (B.emb w) t := ⟨by rw [hν t ht]; simp [r0], h.abs t ht⟩

theorem conv (h : IsLift σ B lift) {ν : Chr F E} {κ : InfinitePlace F → ℕ} (hν : HasExp B.emb ν fun w => κ w)
    (x : @Measure (idAt E (evI F)) (borel _)) (hx : @Measure.IsHaarMeasure _ _ _ (borel _) x) : ∃ c : ℂ, c ≠ 0 ∧
    ∀ (e : ℕ) (g : (InfinitePlace F → ℂ) → ℂ) (G : (AE F E)ˣ → ℂ), (∀ t : (AE F E)ˣ, G t = g fun w => piInf (B.emb w) t) →
      @integral _ _ _ _ (borel _) x (fun t => G t.1 * (ν t.1 : ℂ) * ((absE F E t.1 : ℝ) : ℂ) ^ (e + 1)) = c * ∫ y, g y * r0 κ e y := by
  obtain ⟨c, hc, H⟩ := h.haar x hx
  refine ⟨c, by exact_mod_cast hc.ne', fun e g G hG => ?_⟩
  have := H fun y => g y * r0 κ (e + 1) y
  rw [← show _ = ∫ y, g y * r0 κ e y from integral_congr_ae (by
    filter_upwards [ae_unit] with y hy
    exact (mul_assoc _ _ _).trans (congrArg _ (rationalWeight_succ_mul_inv_norm κ e hy))), ← this]
  congr 1; funext t
  obtain ⟨e1, e2⟩ := nu_eq h hν ((h.idAt t.1).1 t.2)
  rw [hG, rationalWeight_eq_mul_norm_pow κ (e + 1), e1, e2, mul_assoc]

theorem form_yx (hB : B.IsGood σ) {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ} (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j)
    {x y : Fin n → E} (h : form σ J x y = 1) : form σ J y x = ((ε : ℤ) : E) := by
  have hs := PositivityTheory.ThKG.Tow.Levi.sig_sig hB.cm
  rw [← hs (form σ J y x), form_eps hs hJ, h, mul_one, map_intCast]

theorem decomp (hB : B.IsGood σ) {r s} (hX : X.IsHerm σ B r s) {H : Plane E n n₁} {i j} (hH : H.IsAdapted σ B X X₁ i j)
    (z : Fin n → AE F E) : ∃ (U : Fin n₁ → AE F E) (a : AE F E),
      z = incM F H.ι *ᵥ U + a • incV F H.x + cA σ (bA σ X.J (incV F H.x) z) • incV F H.y := by
  obtain ⟨ε, A', hF⟩ := isFr hB (Or.inl hX) hH
  obtain ⟨U, a, b, rfl⟩ := (IsFr.ad hF).span z
  refine ⟨U, a, ?_⟩
  congr 2
  have g := (IsFr.ad hF).gram
  have e : (fun i => cA σ ((fr (incM F H.ι) (incV F H.x) (incV F H.y) *ᵥ Sum.elim U ![a, b]) i)) =
      (fr (incM F H.ι) (incV F H.x) (incV F H.y)).map (cA σ) *ᵥ fun i => cA σ (Sum.elim U ![a, b] i) :=
    funext fun i => RingHom.map_mulVec (cA σ : AE F E →+* AE F E) _ _ i
  have g2 := congrFun (congrArg (· *ᵥ fun i => cA σ (Sum.elim U ![a, b] i)) g) (Sum.inr 0)
  rw [← fr_mulVec, bA, e]
  have g3 : incV F H.x ⬝ᵥ incM F X.J *ᵥ (fr (incM F H.ι) (incV F H.x) (incV F H.y)).map (cA σ) *ᵥ
      (fun i => cA σ (Sum.elim U ![a, b] i)) = cA σ b := by
    simp only [← Matrix.mulVec_mulVec] at g2
    refine Eq.trans ?_ (g2.trans ?_)
    · rfl
    · simp [gr, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [g3, PositivityTheory.ThKG.Tow.Levi.cA_cA hB.cm]

end PositivityTheory.ThKG.Loc.Bump

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr PositivityTheory.ThKF
open scoped ComplexConjugate RealInnerProductSpace

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

theorem bA_l (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (x y : Fin n → AE F E) : bA σ J (a • x) y = a * bA σ J x y := by
  simpa using bA_smul J a 1 x y

theorem bA_r (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (x y : Fin n → AE F E) : bA σ J x (a • y) = cA σ a * bA σ J x y := by
  simpa using bA_smul J 1 a x y

theorem genA (hA : ArchOp) (hE : EiDense) (hS : ArchSlice) {M : Model σ X W} {M₁ : Model σ X₁ W₁} {χX χW om om₁ r s r' s' r₁ s₁ r₁' s₁'}
    (hP : IsPair B M χX χW om r s r' s') (hP₁ : IsPair B M₁ χX χW om₁ r₁ s₁ r₁' s₁') {H : Plane E n n₁} {H' : Plane E d d₁} {i j i' j'}
    (hH : H.IsAdapted σ B X X₁ i j) (hH' : H'.IsAdapted σ B W W₁ i' j') {e ei ev} (he : IsEv B M M₁ H.ι H'.ι (isoA H H') e)
    (hv : IsEvLoc M M₁ e ei ev) {rX rW} (hm : Mix2 H H' χX χW rX rW om om₁ e) {K : Subgroup (UA σ X.J)} {m : LocMeas K}
    (hK : IsStab B K) (hm' : m.Is) {ν : Chr F E} (hc : Continuous ν) {κ : InfinitePlace F → ℕ} (hν : HasExp B.emb ν fun w => κ w)
    {z : ℕ} (hχ : ∀ t, (χW t : ℂ) * ν t = 1)
    {L} (hL : IsConeI B M om m ei (shiftA H H') ν (z + 1) L) {l : SInf F _ →L[ℂ] ℂ} (hl0 : l ≠ 0)
    (hl : ∀ g ∈ UAt σ X₁ (evI F), ∀ f f₁ : SInf F _, Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) : ∃ f, l (L f) ≠ 0 := by
  by_contra hn
  push Not at hn
  have cfg : Cfg B M M₁ H H' e (shiftA H H') :=
    ⟨hP.base, ⟨_, _, hP.herm⟩, ⟨_, _, hP.skew⟩, ⟨_, _, hP₁.herm⟩, ⟨_, _, hP₁.skew⟩, hP.good, hP₁.good, ⟨_, _, hH⟩, ⟨_, _, hH'⟩, Or.inl ⟨he, rfl⟩⟩
  obtain ⟨lift, hlf⟩ := archDict_of F E σ B hP.base
  obtain ⟨hcp, hin, hsl⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e _ ei ev cfg hv lift hlf K m hK hm' _ _ om _ _ _ _ hP
  obtain ⟨f₀, hf₀⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e _ ei ev cfg hv l hl0
  obtain ⟨-, i1, i2⟩ := PositivityTheory.ThKEst.lcsc_UA σ X.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : CompactSpace (kAt K (evI F)) := isCompact_iff_compactSpace.1 hcp
  haveI := hm'.ki
  obtain ⟨c₀, hc₀, hcv⟩ := conv hlf hν m.xi hm'.xi
  have hU : ∀ k ∈ kAt K (evI F), k ∈ UAt σ X (evI F) := fun k hk => (hin k hk).1
  have hG := hP.good
  have hG₁ := hP₁.good
  have sch := (archHeis_of F E σ B n d X W M hP.base).1
  have yx : form σ X.J H.y H.x = 1 := by simpa using form_yx hP.base (ε := 1) (by simpa using hP.herm.herm) hH.xy
  have yx' : form σ W.J H'.y H'.x = -1 := by simpa using form_yx hP.base (ε := -1) (by simpa using hP.skew.skew) hH'.xy
  have hprp := prp_pim (cont_xi hlf H.x (kAt K (evI F))) (xi_ne hlf hH.xy) 1
  have val : ∀ (u) (_ : At (evI F) u) (k : kAt K (evI F)) f, l (ei (opI (fun Φ => M.co.rho B.ψ u (om (k.1, 1) Φ)) f)) =
      unp M₁ l (e (M.co.rho B.ψ u (om (k.1, 1) (PV M f)))) := fun u hu k f => by
    rw [← pv_opI hA hP hu (hU _ k.2), un_e hG hG₁ hv]
  have omv : ∀ (k : kAt K (evI F)) f, ∃ g, om (k.1, 1) (PV M f) = PV M g := fun k f =>
    ⟨_, ((pv_opI hA hP (u := 0) (fun a _ => smul_zero a) (hU _ k.2) f).trans (rho_zero _ _ _)).symm⟩
  have om1 : ∀ Φ, om (((1 : kAt K (evI F)) : UA σ X.J), 1) Φ = Φ := fun Φ => by
    change om 1 Φ = Φ
    rw [map_one]; rfl
  have sh : ∀ c, lift c • shiftA H H' 1 = Matrix.vecMulVec (lift c • incV F H.x) (incV F H'.y) := fun c => by
    rw [shiftA, Units.val_one, one_smul, Matrix.smul_vecMulVec]
  let a : SInf F _ → kAt K (evI F) × (InfinitePlace F → ℂ) → ℂ := fun f p =>
    l (ei (opI (fun Φ => M.co.rho B.ψ (lift p.2 • shiftA H H' 1) (om (p.1.1, 1) Φ)) f))
  have ha : ∀ f k c, a f (k, c) = unp M₁ l (e (M.co.rho B.ψ (Matrix.vecMulVec (lift c • incV F H.x) (incV F H'.y)) (om (k.1, 1) (PV M f)))) :=
    fun f k c => by rw [← sh]; exact val _ (at_smul2 (hlf.supp c) _) k f
  have zero : ∀ f, ∫ k, ∫ c, a f (k, c) * r0 κ z c ∂volume ∂m.ki = 0 := fun f => by
    have h1 := (hsl f l).2.2 ν (z + 1) hc (by omega) L hL
    rw [hn] at h1
    have h2 : ∀ k : kAt K (evI F), _ = c₀ * ∫ c, a f (k, c) * r0 κ z c := fun k => hcv z (fun c => a f (k, c))
      (fun t => l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • shiftA H H' t) (om (k.1, 1) Φ)) f))) fun t => by
        simp only [a, shiftA, Units.val_one, one_smul]
        rw [← smul_assoc, hlf.eq (hlf.part t.1).1 (hlf.part t.1).2]
    simp only [h2] at h1
    rw [integral_const_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hc₀
  obtain ⟨f, hf⟩ := pv_rho hP.base hG (u := Matrix.vecMulVec ((-lift 1) • incV F H.x) (incV F H'.y))
    (at_vv (by rw [neg_smul, ← zero_sub]; exact at_sub (fun a _ => smul_zero a) (at_smul2 (hlf.supp 1) _)) _) f₀
  have h11 : a f (1, 1) ≠ 0 := by
    rw [ha, om1, ← hf, ← heisenberg_action_add_of_orthogonal M B.ψ (by rw [sy_vv, bA_smul, bA_inc, hH.xx]; simp), ← Matrix.add_vecMulVec, ← add_smul, add_neg_cancel,
      zero_smul, Matrix.zero_vecMulVec, rho_zero, un_e hG hG₁ hv]
    exact hf₀
  refine coreA m.ki hprp κ z (hsl f l).1 (hsl f l).2.1 (a f (1, 1))⁻¹ (fun p hp => ?_) fun η => ?_
  · obtain ⟨hne, t, ht, ht', hk⟩ := sig_pt hlf hH.xy hU p hp
    obtain ⟨e1, e2⟩ := nu_eq hlf hν ht
    simp only [ht'] at e1 e2
    have k1 : lift p.2 • incV F H.x = mat p.1.1 *ᵥ (lift 1 • incV F H.x) := by
      rw [Matrix.mulVec_smul, hk, smul_smul, ← hlf.eq (at_mul (hlf.supp 1) t.1) fun w => by rw [map_mul, hlf.pi, ht']; simp]
    have k2 : a f p = (χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) * a f (1, 1) := by
      rw [ha f p.1 p.2, ha, k1, ← om_rho hP _ _ _ (pv_sch hG f), om1]
      exact (mix_un hA hP hP₁ hH hv hm hl (hU _ p.1.2) hk).1 _
        ((pv_rho hP.base hG (at_vv (at_smul2 (hlf.supp 1) _) _) f))
    have k3 : a f p * r0 κ z p.2 * (a f (1, 1))⁻¹ = (((nm p.2) ^ rX * nm p.2 ^ z : ℝ) : ℂ) := by
      rw [k2, rationalWeight_eq_mul_norm_pow, ← e1, e2]
      push_cast
      field_simp
      linear_combination ((((nm p.2) ^ rX : ℝ) : ℂ) * ((nm p.2 : ℝ) : ℂ) ^ z) * hχ t
    change 0 < (a f p * _ * _).re
    rw [k3, Complex.ofReal_re]
    have := nm_pos hne
    positivity
  · obtain ⟨g, hg⟩ := pv_rho hP.base hG (at_vv (at_Yv hlf (X := X) (-η)) (incV F H'.x)) f
    refine Eq.trans ?_ (zero g)
    congr 1; funext k; congr 1; funext c; congr 1
    obtain ⟨f₁, hf₁⟩ := omv k f
    change _ * a f (k, c) = _
    rw [ha, ha, ← hg, om_rho hP _ _ _ (pv_sch hG f), rho_comm, hf₁]
    obtain ⟨f₂, hf₂⟩ := pv_rho hP.base hG (at_vv (at_smul2 (hlf.supp c) (incV F H.x)) (incV F H'.y)) f₁
    rw [hf₂, un_e_smul hG hG₁ hv l _ (pv_rho hP.base hG (at_vv (at_mulVec (at_Yv hlf _)) _) f₂),
      he.inv _ (Or.inl ⟨_, rfl⟩) _ (pv_sch hG f₂)]
    congr 1
    rw [sy_vv, bA_l, bA_inc, yx', map_neg (inclR (F := F) (E := E) (AF F)), map_one, mul_neg_one, neg_neg,
      hlf.ch (hlf.supp c) (x := bet (xi B H.x) (k, -η)) (y := c) fun w => by rw [map_mul, hlf.pi, pi_beta hlf hP.herm, mul_comm],
      pr_bet, inner_neg_left, neg_neg]

set_option maxHeartbeats 400000 in
theorem genB (hA : ArchOp) (hE : EiDense) (hS : ArchSlice) {M : Model σ X W} {M₁ : Model σ X₁ W₁} {χX χW om om₁ r s r' s' r₁ s₁ r₁' s₁'}
    (hP : IsPair B M χX χW om r s r' s') (hP₁ : IsPair B M₁ χX χW om₁ r₁ s₁ r₁' s₁') {H : Plane E n n₁} {H' : Plane E d d₁} {i j i' j'}
    (hH : H.IsAdapted σ B X X₁ i j) (hH' : H'.IsAdapted σ B W W₁ i' j') {e ei ev} (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e)
    (hv : IsEvLoc M M₁ e ei ev) {rX rW} (hm : Mix2 H H' χX χW rX rW om om₁ e) {K : Subgroup (UA σ X.J)} {m : LocMeas K}
    (hK : IsStab B K) (hm' : m.Is) {ν : Chr F E} (hc : Continuous ν) {κ : InfinitePlace F → ℕ} (hν : HasExp B.emb ν fun w => κ w)
    {z : ℕ} (hχ : ∀ t, χW t = ν t) (hκ : ∀ w, 2 * z < κ w)
    {L} (hL : IsConeI B M om m ei (shiftB σ H H') ν (z + 1) L) {l : SInf F _ →L[ℂ] ℂ} (hl0 : l ≠ 0)
    (hl : ∀ g ∈ UAt σ X₁ (evI F), ∀ f f₁ : SInf F _, Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) : ∃ f, l (L f) ≠ 0 := by
  by_contra hn
  push Not at hn
  have cfg : Cfg B M M₁ H H' e (shiftB σ H H') :=
    ⟨hP.base, ⟨_, _, hP.herm⟩, ⟨_, _, hP.skew⟩, ⟨_, _, hP₁.herm⟩, ⟨_, _, hP₁.skew⟩, hP.good, hP₁.good, ⟨_, _, hH⟩, ⟨_, _, hH'⟩, Or.inr ⟨he, rfl⟩⟩
  obtain ⟨lift, hlf⟩ := archDict_of F E σ B hP.base
  obtain ⟨hcp, hin, hsl⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e _ ei ev cfg hv lift hlf K m hK hm' _ _ om _ _ _ _ hP
  obtain ⟨f₀, hf₀⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e _ ei ev cfg hv l hl0
  obtain ⟨-, i1, i2⟩ := PositivityTheory.ThKEst.lcsc_UA σ X.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : CompactSpace (kAt K (evI F)) := isCompact_iff_compactSpace.1 hcp
  haveI := hm'.ki
  obtain ⟨c₀, hc₀, hcv⟩ := conv hlf hν m.xi hm'.xi
  have hU : ∀ k ∈ kAt K (evI F), k ∈ UAt σ X (evI F) := fun k hk => (hin k hk).1
  have hG := hP.good
  have hG₁ := hP₁.good
  have sch := (archHeis_of F E σ B n d X W M hP.base).1
  have yx : form σ X.J H.y H.x = 1 := by simpa using form_yx hP.base (ε := 1) (by simpa using hP.herm.herm) hH.xy
  have yx' : form σ W.J H'.y H'.x = -1 := by simpa using form_yx hP.base (ε := -1) (by simpa using hP.skew.skew) hH'.xy
  have hprp := prp_pim (cont_xi hlf H.x (kAt K (evI F))) (xi_ne hlf hH.xy) 1
  have val : ∀ (u) (_ : At (evI F) u) (k : kAt K (evI F)) f, l (ei (opI (fun Φ => M.co.rho B.ψ u (om (k.1, 1) Φ)) f)) =
      unp M₁ l (e (M.co.rho B.ψ u (om (k.1, 1) (PV M f)))) := fun u hu k f => by
    rw [← pv_opI hA hP hu (hU _ k.2), un_e hG hG₁ hv]
  have omv : ∀ (k : kAt K (evI F)) f, ∃ g, om (k.1, 1) (PV M f) = PV M g := fun k f =>
    ⟨_, ((pv_opI hA hP (u := 0) (fun a _ => smul_zero a) (hU _ k.2) f).trans (rho_zero _ _ _)).symm⟩
  have om1 : ∀ Φ, om (((1 : kAt K (evI F)) : UA σ X.J), 1) Φ = Φ := fun Φ => by
    change om 1 Φ = Φ
    rw [map_one]; rfl
  have sh : ∀ c, lift c • shiftB σ H H' 1 = Matrix.vecMulVec (lift c • incV F H.y) (incV F H'.x) := fun c => by
    rw [shiftB, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec]
  have cj : Continuous fun p : kAt K (evI F) × (InfinitePlace F → ℂ) => (p.1, star p.2) := by fun_prop
  let a : SInf F _ → kAt K (evI F) × (InfinitePlace F → ℂ) → ℂ := fun f p =>
    l (ei (opI (fun Φ => M.co.rho B.ψ (lift (star p.2) • shiftB σ H H' 1) (om (p.1.1, 1) Φ)) f))
  have hac : ∀ f, Continuous (a f) := fun f => by
    have := (hsl f l).1.comp cj
    exact this
  have had : ∀ f, Dec (a f) := fun f N => let ⟨C, hC⟩ := (hsl f l).2.1 N; ⟨C, fun k c => by have := hC k (star c); rw [norm_star] at this; exact this⟩
  have ha : ∀ f k c, a f (k, c) =
      unp M₁ l (e (M.co.rho B.ψ (Matrix.vecMulVec (lift (star c) • incV F H.y) (incV F H'.x)) (om (k.1, 1) (PV M f)))) :=
    fun f k c => by rw [← sh]; exact val _ (at_smul2 (hlf.supp _) _) k f
  have zero : ∀ f, ∫ k, ∫ c, a f (k, c) * r0 κ z c ∂volume ∂m.ki = 0 := fun f => by
    have h1 := (hsl f l).2.2 ν (z + 1) hc (by omega) L hL
    rw [hn] at h1
    have h2 : ∀ k : kAt K (evI F), _ = c₀ * ∫ c, a f (k, c) * r0 κ z c := fun k => hcv z (fun c => a f (k, c))
      (fun t => l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • shiftB σ H H' t) (om (k.1, 1) Φ)) f))) fun t => by
        simp only [a, shiftB, Units.val_one, map_one, one_smul]
        rw [← smul_assoc, hlf.eq (hlf.part _).1 (c := star fun w => piInf (B.emb w) t.1) fun w => by
          rw [(hlf.part _).2, hlf.conj]; rfl]
    simp only [h2] at h1
    rw [integral_const_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hc₀
  clear_value a
  clear hsl val hcv
  have hac1 : ∀ f, Continuous fun c => a f (1, c) := fun f => (hac f).comp (Continuous.prodMk_right 1)
  have sy0 : ∀ x x' : Fin n → AE F E, sy σ X W (Matrix.vecMulVec x (incV F H'.x)) (Matrix.vecMulVec x' (incV F H'.x)) = 0 := fun x x' => by
    rw [sy_vv, bA_inc, hH'.xx]; simp
  have kill : ∀ U (b : AE F E) y, ∀ Φ ∈ schA F _, e (M.co.rho B.ψ (Matrix.vecMulVec (incM F H.ι *ᵥ U + b • incV F H.x + y) (incV F H'.x)) Φ) =
      e (M.co.rho B.ψ (Matrix.vecMulVec y (incV F H'.x)) Φ) := fun U b y Φ hΦ => by
    rw [Matrix.add_vecMulVec, Matrix.add_vecMulVec, add_assoc, ← Matrix.add_vecMulVec, heisenberg_action_add_of_orthogonal M B.ψ (sy0 _ _),
      he.inv _ (Or.inr ⟨_, rfl⟩) _ (sch _ _ hΦ), Matrix.add_vecMulVec, heisenberg_action_add_of_orthogonal M B.ψ (sy0 _ _),
      he.inv _ (Or.inl ⟨b • incV F H'.x, by rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]⟩) _ (sch _ _ hΦ)]
  have l0 : lift 0 = 0 := (hlf.eq (fun u _ => smul_zero u) fun w => map_zero _).symm
  obtain ⟨t₀, ht₀⟩ := exists_FT_ne (a := fun c => a f₀ (1, c)) (hac1 f₀)
    ((had f₀).integrable 1 (hac1 f₀)) (by
      rw [ha, om1, star_zero, l0, zero_smul, Matrix.zero_vecMulVec, rho_zero, un_e hG hG₁ hv]; exact hf₀)
  obtain ⟨f, hf⟩ := pv_rho hP.base hG (at_vv (at_smul2 (hlf.supp (1 - t₀)) (incV F H.x)) (incV F H'.y)) f₀
  have h11 : FT (fun c => a f (1, c)) 1 ≠ 0 := by
    refine fun h => ht₀ (Eq.trans ?_ h)
    rw [FT, FT]
    congr 1; funext c
    obtain ⟨f₂, hf₂⟩ := pv_rho hP.base hG (at_vv (at_smul2 (hlf.supp (star c)) (incV F H.y)) (incV F H'.x)) f₀
    rw [ha, ha, om1, om1, ← hf, rho_comm, hf₂, un_e_smul hG hG₁ hv l _ (pv_rho hP.base hG (at_vv (at_smul2 (hlf.supp _) _) _) f₂),
      he.inv _ (Or.inl ⟨lift (1 - t₀) • incV F H'.y, by rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]⟩) _ (pv_sch hG f₂),
      ← mul_assoc]
    congr 1
    rw [sy_vv, bA_smul, bA_inc, bA_inc, yx, hH'.xy, map_one, mul_one, mul_one, ← mul_neg,
      hlf.ch (hlf.supp _) (x := c) (y := t₀ - 1) fun w => by
        rw [map_mul, map_neg, hlf.conj, hlf.pi, hlf.pi]; simp <;> ring, ← ch_add]
    congr 1
    simp only [pr, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by simp; ring
  haveI : SecondCountableTopology (kAt K (evI F)) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : FirstCountableTopology (kAt K (evI F)) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  obtain ⟨D, hD⟩ := bet_le (cont_xi hlf H.x (kAt K (evI F)))
  refine coreB m.ki hprp κ z hκ (hac f) (had f) (FT (fun c => a f (1, c)) 1)⁻¹ _ (cont_bet (cont_xi hlf H.x _)) D hD (pr_bet _)
    (fun p hp => ?_) fun η => ?_
  · obtain ⟨hne, t, ht, ht', hk⟩ := sig_pt hlf hH.xy hU p hp
    obtain ⟨e1, e2⟩ := nu_eq hlf hν ht
    simp only [ht'] at e1 e2
    obtain ⟨hmx, U, b, hy⟩ := mix_un hA hP hP₁ hH hv hm hl (hU _ p.1.2) hk
    have k2 : ∀ c, a f (p.1, c) = (χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) * a f (1, p.2 * c) := fun c => by
      rw [ha, ha, ← mat_cancel' p.1.1 (lift (star c) • incV F H.y), ← om_rho hP _ _ _ (pv_sch hG f), om1,
        hmx _ (pv_rho hP.base hG (at_vv (at_mulVec (at_smul2 (hlf.supp _) _)) _) f), Matrix.mulVec_smul, hy, smul_add, smul_add,
        ← Matrix.mulVec_smul, smul_smul, smul_smul, kill _ _ _ _ (pv_sch hG f),
        hlf.eq (at_mul (hlf.supp (star c)) (cA σ t.1)) (c := star (p.2 * c)) fun w => by
          rw [map_mul, hlf.pi, hlf.conj, ht']; simp [mul_comm]]
    have k4 : FT (fun c => a f (p.1, c)) p.2 =
        (χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) * (((nm p.2 : ℝ) : ℂ)⁻¹ * FT (fun c => a f (1, c)) 1) := by
      have := FT_scale ((had f).integrable 1 (hac1 f)) hne p.2
      rw [show p.2 * p.2⁻¹ = 1 from funext fun w => mul_inv_cancel₀ (hne w)] at this
      rw [← this, FT, FT, ← integral_const_mul]
      congr 1; funext c; rw [k2]; ring
    have hp' := nm_pos hne
    have hp'' : ((nm p.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
    have hr := rationalWeight_ne_zero κ 0 hne
    have k3 : FT (fun c => a f (p.1, c)) p.2 * ((r0 κ z p.2)⁻¹ * ((nm p.2 : ℝ) : ℂ)⁻¹) * (FT (fun c => a f (1, c)) 1)⁻¹ =
        (((nm p.2) ^ rX * (nm p.2 ^ (z + 2))⁻¹ : ℝ) : ℂ) := by
      rw [k4, rationalWeight_eq_mul_norm_pow κ z p.2, hχ, e1, e2]
      change r0 κ 0 p.2 * (((nm p.2) ^ rX : ℝ) : ℂ) * _ * _ * _ = _
      rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
      have h11' : FT (fun c => a f (1, c)) 1 * (FT (fun c => a f (1, c)) 1)⁻¹ = 1 := mul_inv_cancel₀ h11
      have hr' : r0 κ 0 p.2 * (r0 κ 0 p.2)⁻¹ = 1 := mul_inv_cancel₀ hr
      generalize (((nm p.2) ^ rX : ℝ) : ℂ) = A
      generalize FT (fun c => a f (1, c)) 1 = T at h11'
      rw [mul_inv, pow_add, mul_inv, ← inv_pow _ 2]
      linear_combination (A * ((nm p.2 : ℝ) : ℂ)⁻¹ ^ 2 * (((nm p.2 : ℝ) : ℂ) ^ z)⁻¹) * (T * T⁻¹ * hr' + h11')
    rw [k3, Complex.ofReal_re]
    positivity
  · obtain ⟨g, hg⟩ := pv_rho hP.base hG (at_vv (at_Yv hlf (X := X) η) (incV F H'.x)) f
    refine Eq.trans ?_ (zero g)
    congr 1; funext k; congr 1; funext c; congr 1
    obtain ⟨U, b, hy⟩ := decomp hP.base hP.herm hH (mat k.1 *ᵥ Yv X B lift η)
    have hat : At (evI F) (cA σ (bA σ X.J (incV F H.x) (mat k.1 *ᵥ Yv X B lift η))) := by
      rw [← at_iff.1 (at_mulVec (g := mat k.1) (at_Yv hlf (X := X) η)), ← algebraMap_smul (AE F E), bA_r, map_mul,
        PositivityTheory.ThKG.Tow.Levi.cA_cA hP.base.cm, ← Algebra.smul_def]
      exact (hlf.part _).1
    rw [ha, ha, ← hg, om_rho hP _ _ _ (pv_sch hG f), ← heisenberg_action_add_of_orthogonal M B.ψ (sy0 _ _), ← Matrix.add_vecMulVec, hy, add_comm (lift _ • _),
      add_assoc, kill _ _ _ _ (om_sch hP _ (pv_sch hG f)), ← add_smul,
      ← hlf.eq (at_add hat (hlf.supp (star c))) (c := star (c + bet (xi B H.x) (k, η))) fun w => by
        rw [map_add, hlf.pi, hlf.conj, pi_beta hlf hP.herm]; simp [add_comm]]

theorem kap_ex {a a' : ℕ} {G : Geo σ a a'} {Y : Chars F E} {om om'} (t : IsTriple B G Y om om') :
    ∃ κ : InfinitePlace F → ℕ, (∀ w, a + a' < κ w) ∧ HasExp B.emb Y.ν fun w => κ w := by
  refine ⟨fun w => (B.mα w - B.mβ w).toNat, fun w => by have := t.geo.kappa w; beta_reduce; omega, fun z hz => ?_⟩
  obtain ⟨lift, h⟩ := archDict_of F E σ B t.base
  rw [Chars.ν, MonoidHom.div_apply, Circle.coe_div, t.chars.expα z hz, t.chars.expβ z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h0 : piInf (B.emb w) (z : AE F E) ≠ 0 := (z.isUnit.map _).ne_zero
  rw [← zpow_sub₀ (by simpa using h0)]
  congr 1
  have := t.geo.kappa w; beta_reduce; omega

theorem pcast {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' a b a' b' : ℕ} (h : IsPair B M χX χW om r s r' s')
    (h1 : r = a) (h2 : s = b) (h3 : r' = a') (h4 : s' = b') : IsPair B M χX χW om a b a' b' := by subst h1 h2 h3 h4; exact h

theorem bumpA_of (hA : ArchOp) (hE : EiDense) (hS : ArchSlice) (hM : MixAB) : BumpA := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' c e ei ev he hv K m hK hm X om om' om₁ om₁' t t₁ L hL l hl0 hl
  obtain ⟨κ, -, hκ⟩ := kap_ex t
  have h1 := t.geo.eBig; have h2 := t₁.geo.eBig; have h3 := c.ep; have h4 := c.q0; have h5 := c.q1
  obtain ⟨z, hz⟩ : ∃ z, (b + 2 - a') / 2 = z + 1 := ⟨(b + 2 - a') / 2 - 1, by omega⟩
  rw [hz] at hL
  refine genA hA hE hS (pairV t) (pairV t₁) c.hH c.hH' he hv ((hM F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ _ _ c.hH c.hH' _ _ om om₁
    (pcast (pairV t) (by omega) (by omega) (by omega) (by omega)) (pairV t₁)).1 e he) hK hm
    (isHecke_div t.chars.heckeα t.chars.heckeβ).1 hκ (fun x => ?_) hL hl0 hl
  simp [Chars.ν]

theorem bumpB_of (hA : ArchOp) (hE : EiDense) (hS : ArchSlice) (hM : MixAB) : BumpB := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' c e ei ev he hv K m hK hm X om om' om₁ om₁' t t₁ L hL l hl0 hl
  obtain ⟨κ, hκ', hκ⟩ := kap_ex t
  have h1 := t.geo.aBig; have h2 := t₁.geo.aBig; have h3 := c.ep; have h4 := c.eq; have h5 := t.geo.lt
  exact genB hA hE hS (pairV' t) (pairV' t₁) c.hH c.hH' he hv ((hM F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ _ _ c.hH c.hH' _ _ om' om₁'
    (pcast (pairV' t) (by omega) (by omega) (by omega) (by omega)) (pairV' t₁)).2 e he) hK hm
    (isHecke_div t.chars.heckeα t.chars.heckeβ).1 hκ (fun x => rfl) (fun w => by have := hκ' w; omega) hL hl0 hl

end PositivityTheory.ThKG.Loc.Bump

end
end

section
namespace PositivityTheory.ThKG.Loc.Bump

open GlobalTheory.ThK PositivityTheory.ThKCT PositivityTheory.ThKF

theorem bumpA_fin (h₁ : StabEx) (h₂ : ArchOp) (h₃ : Slice) (h₄ : ArchUniq) (h₅ : SchInt) (h₆ : MixAB) : BumpA :=
  bumpA_of h₂ (eiDense_of h₅) (archSlice_of h₁ h₂ h₃ archHeis_of h₄ h₅) h₆

theorem bumpB_fin (h₁ : StabEx) (h₂ : ArchOp) (h₃ : Slice) (h₄ : ArchUniq) (h₅ : SchInt) (h₆ : MixAB) : BumpB :=
  bumpB_of h₂ (eiDense_of h₅) (archSlice_of h₁ h₂ h₃ archHeis_of h₄ h₅) h₆

end PositivityTheory.ThKG.Loc.Bump
end
