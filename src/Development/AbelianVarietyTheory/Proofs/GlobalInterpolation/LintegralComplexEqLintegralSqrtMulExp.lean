import Mathlib

section
namespace GlobalTheory.SquareImageInterval

open MeasureTheory

theorem image_sq_Ioi : (fun r : ℝ => r ^ 2) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact pow_pos (Set.mem_Ioi.1 hr) 2
  · intro hy
    exact ⟨√y, Real.sqrt_pos.2 hy, Real.sq_sqrt (le_of_lt hy)⟩

theorem main : ∀ (G : ℝ → ENNReal), ∫⁻ (r : ℝ) in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r
    = ∫⁻ (u : ℝ) in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G √u := by
  intro G
  have hinj : Set.InjOn (fun r : ℝ => r ^ 2) (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    have h2 : a ^ 2 = b ^ 2 := hab
    nlinarith [h2]
  have hder : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * x) (Set.Ioi 0) x := by
    intro x _
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj
    (fun u => (2 : ENNReal)⁻¹ * G √u)
  rw [image_sq_Ioi] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  have hx' : 0 < x := hx
  simp only
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * x), Real.sqrt_sq (le_of_lt hx'),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  calc ENNReal.ofReal x * G x = (2 * 2⁻¹) * (ENNReal.ofReal x * G x) := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ = 2 * ENNReal.ofReal x * (2⁻¹ * G x) := by ring

end GlobalTheory.SquareImageInterval
end

section
open MeasureTheory

namespace GlobalTheory

theorem lintegral_Ioi_mul_eq_lintegral_Ioi_sqrt (G : ℝ → ENNReal) :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r
      = ∫⁻ u in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G (Real.sqrt u) := by
  first
  | exact @_root_.GlobalTheory.SquareImageInterval.main
  | exact _root_.GlobalTheory.SquareImageInterval.main
  | (apply _root_.GlobalTheory.SquareImageInterval.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareImageInterval.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareImageInterval.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareImageInterval.main ..)

theorem lintegral_complex_eq_lintegral_sqrt_mul_exp (ε c : ℝ) (hε : ε = 1 ∨ ε = -1)
    (g : ℂ → ENNReal) (hg : Measurable g) (h0 : g 0 = 0) :
    ∫⁻ z, g z = ∫⁻ t : ℝ, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
      (2 : ENNReal)⁻¹ *
        g ((Real.sqrt (ε * (t - c)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  set G : ℝ → ENNReal := fun r => ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
    g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) with hG
  have h1 : ∫⁻ z, g z = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r := by
    rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod]
    have hm : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal p.1 * g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by
      refine (ENNReal.measurable_ofReal.comp measurable_fst).mul (hg.comp ?_)
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)).measurable
    have he : (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • g (Complex.polarCoord.symm p))
        = fun p : ℝ × ℝ =>
          ENNReal.ofReal p.1 * g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by
      funext p
      simp [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
    rw [he, setLIntegral_prod _ hm.aemeasurable]
    refine lintegral_congr fun r => ?_
    simp only [hG]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h2 : ∫⁻ u in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G (Real.sqrt u)
      = ∫⁻ u, (2 : ENNReal)⁻¹ * G (Real.sqrt u) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, Real.sqrt_eq_zero_of_nonpos (not_lt.1 hu)]
      simp [hG, h0]
  have h3 : ∀ F : ℝ → ENNReal, ∫⁻ u, F u = ∫⁻ t, F (ε * (t - c)) := by
    intro F
    rw [lintegral_sub_right_eq_self (fun u => F (ε * u)) c]
    rcases hε with rfl | rfl
    · simp
    · simp only [neg_mul, one_mul]
      exact (lintegral_neg_eq_self F).symm
  rw [h1, lintegral_Ioi_mul_eq_lintegral_Ioi_sqrt, h2, h3]
  refine lintegral_congr fun t => ?_
  simp only [hG]
  rw [lintegral_const_mul' _ _ (by norm_num)]

end GlobalTheory
end
