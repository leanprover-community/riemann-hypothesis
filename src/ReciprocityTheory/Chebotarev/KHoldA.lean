import ReciprocityTheory.Chebotarev.Support
import ReciprocityTheory.Chebotarev.DiscreteTopologyLatOf
import ReciprocityTheory.Chebotarev.UnitPart
import Mathlib

section
open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem gs_eq_ofReal {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    Gs χ s x = χ (rsgn x : ZMod l) * ((uphi x * (mixedEmbedding.norm x) ^ (-s) : ℝ) : ℂ) := by
  unfold Gs
  rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (mixedEmbedding.norm_nonneg x)]
  push_cast; ring

theorem norm_gs_le {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    ‖Gs χ s x‖ ≤ uphi x * (mixedEmbedding.norm x) ^ (-s) := by
  rw [gs_eq_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (uphi_nonneg x) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _))]
  exact mul_le_of_le_one_left (mul_nonneg (uphi_nonneg x) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _))
    (DirichletCharacter.norm_le_one χ _)

theorem norm_gs_embZ_le {l : ℕ} (χ : DirichletCharacter ℂ l) {s : ℝ} (hs : 1 ≤ s) (α : 𝓞 E) :
    ‖Gs χ s (embZ α)‖ ≤ 1 := by
  refine (norm_gs_le χ s _).trans ?_
  have h1 : (mixedEmbedding.norm (embZ α)) ^ (-s) ≤ 1 := by
    rw [norm_embZ]
    by_cases h0 : Algebra.norm ℤ α = 0
    · rw [h0]; simp only [Int.cast_zero, abs_zero]
      rw [Real.zero_rpow (by linarith)]; norm_num
    · apply Real.rpow_le_one_of_one_le_of_nonpos _ (by linarith)
      have : (1 : ℤ) ≤ |Algebra.norm ℤ α| := Int.one_le_abs h0
      exact_mod_cast this
  calc uphi (embZ α) * (mixedEmbedding.norm (embZ α)) ^ (-s) ≤ 1 * 1 :=
        mul_le_mul (uphi_le_one _) h1 (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _) zero_le_one
    _ = 1 := one_mul 1

theorem continuous_gs {l : ℕ} (χ : DirichletCharacter ℂ l) (x : mixedSpace E) :
    Continuous fun s : ℝ => Gs χ s x := by
  simp_rw [gs_eq_ofReal]
  by_cases h : mixedEmbedding.norm x = 0
  · simp only [uphi_of_norm_eq_zero h, zero_mul, Complex.ofReal_zero, mul_zero]
    exact continuous_const
  · refine continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul ?_))
    exact (Real.continuous_const_rpow h).comp continuous_neg

theorem summable_gs {l : ℕ} (χ : DirichletCharacter ℂ l) (Λ : Submodule ℤ (mixedSpace E)) [DiscreteTopology Λ]
    (hΛ : Module.finrank ℤ Λ = Module.finrank ℚ E) {s : ℝ} (hs : 1 < s) :
    Summable fun x : Λ => Gs χ s (x : mixedSpace E) := by
  obtain ⟨c₀, hc₀, -, hb⟩ := exists_support_bound (E := E)
  set d := Module.finrank ℚ E
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Module.finrank_pos
  set r : ℝ := -((d : ℝ) * s)
  have hr : r < -(Module.finrank ℤ Λ : ℝ) := by
    rw [hΛ]; simp only [r, neg_lt_neg_iff]; nlinarith
  refine Summable.of_norm_bounded ((ZLattice.summable_norm_rpow Λ r hr).mul_left (c₀ ^ r)) fun x => ?_
  refine (norm_gs_le χ s _).trans ?_
  have hpos : 0 ≤ c₀ ^ r * ‖x‖ ^ r := mul_nonneg (Real.rpow_nonneg hc₀.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hu : uphi (x : mixedSpace E) = 0
  · rw [hu, zero_mul]; exact hpos
  obtain ⟨-, hN⟩ := hb _ hu
  have hN0 : mixedEmbedding.norm (x : mixedSpace E) ≠ 0 := by
    intro h; exact hu (uphi_of_norm_eq_zero h)
  have hx0 : (x : mixedSpace E) ≠ 0 := by
    rintro h; apply hN0; rw [h]
    exact mixedEmbedding.norm_eq_zero_iff.mpr ⟨Classical.arbitrary _, by simp⟩
  have hxn : 0 < ‖(x : mixedSpace E)‖ := norm_pos_iff.mpr hx0
  have hcx : 0 < c₀ * ‖(x : mixedSpace E)‖ := mul_pos hc₀ hxn
  have key : (mixedEmbedding.norm (x : mixedSpace E)) ^ (-s) ≤ (c₀ * ‖(x : mixedSpace E)‖) ^ r := by
    have : (c₀ * ‖(x : mixedSpace E)‖) ^ r = ((c₀ * ‖(x : mixedSpace E)‖) ^ d) ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hcx.le]; simp [r]
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos (pow_pos hcx _) (by rw [mul_pow]; exact hN) (by linarith)
  calc uphi (x : mixedSpace E) * (mixedEmbedding.norm (x : mixedSpace E)) ^ (-s)
      ≤ 1 * (c₀ * ‖(x : mixedSpace E)‖) ^ r :=
        mul_le_mul (uphi_le_one _) key (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _) zero_le_one
    _ = c₀ ^ r * ‖x‖ ^ r := by rw [one_mul, Real.mul_rpow hc₀.le (norm_nonneg _)]; rfl

end ReciprocityTheory.Cheb
end

section
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem

open scoped Classical

namespace ReciprocityTheory.Cheb

theorem abs_log_sub_log_le_of_half {a b δ : ℝ} (hb : 0 < b) (hab : |a - b| ≤ δ) (ha : b / 2 ≤ a) :
    |Real.log a - Real.log b| ≤ 2 * δ / b := by
  have ha0 : 0 < a := by linarith
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hab
  rw [abs_le] at hab ⊢
  constructor
  · have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha0)
    rw [Real.log_div hb.ne' ha0.ne'] at h1
    have h2 : b / a - 1 ≤ 2 * δ / b := by
      rw [div_sub_one ha0.ne', div_le_div_iff₀ ha0 hb]
      nlinarith
    linarith
  · have h1 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb)
    rw [Real.log_div ha0.ne' hb.ne'] at h1
    have h2 : a / b - 1 ≤ 2 * δ / b := by
      rw [div_sub_one hb.ne']
      apply div_le_div_of_nonneg_right _ hb.le
      linarith
    linarith

theorem abs_exp_neg_mul_sub_le {s u v L : ℝ} (hs : 1 ≤ s) (hL : 0 ≤ L) (hu : L ≤ u) (hv : L ≤ v) :
    |Real.exp (-s * u) - Real.exp (-s * v)| ≤ s * |u - v| * Real.exp (-L) := by
  have key : ∀ u v : ℝ, L ≤ u → u ≤ v →
      Real.exp (-s * u) - Real.exp (-s * v) ≤ s * (v - u) * Real.exp (-L) := by
    intro u v hu huv
    have e1 : Real.exp (-s * v) = Real.exp (-s * u) * Real.exp (-(s * (v - u))) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : 1 - Real.exp (-(s * (v - u))) ≤ s * (v - u) := by
      linarith [Real.add_one_le_exp (-(s * (v - u)))]
    have e3 : Real.exp (-s * u) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by nlinarith)
    have e4 : 0 ≤ s * (v - u) := mul_nonneg (by linarith) (by linarith)
    rw [e1]
    calc Real.exp (-s * u) - Real.exp (-s * u) * Real.exp (-(s * (v - u)))
        = Real.exp (-s * u) * (1 - Real.exp (-(s * (v - u)))) := by ring
      _ ≤ Real.exp (-L) * (s * (v - u)) :=
        mul_le_mul e3 e2 (by linarith [Real.exp_le_one_iff.mpr (by linarith : -(s * (v - u)) ≤ 0)])
          (Real.exp_pos _).le
      _ = s * (v - u) * Real.exp (-L) := by ring
  rcases le_total u v with huv | hvu
  · have h := key u v hu huv
    have hm : Real.exp (-s * v) ≤ Real.exp (-s * u) := Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h := key v u hv hvu
    have hm : Real.exp (-s * u) ≤ Real.exp (-s * v) := Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

theorem sign_add_of_abs_lt {a e : ℝ} (h : |e| < |a|) : SignType.sign (a + e) = SignType.sign a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [abs_of_neg ha] at h
    have : a + e < 0 := by linarith [le_abs_self e]
    rw [sign_neg this, sign_neg ha]
  · subst ha; simp at h; linarith [abs_nonneg e]
  · rw [abs_of_pos ha] at h
    have : 0 < a + e := by linarith [neg_abs_le e]
    rw [sign_pos this, sign_pos ha]

variable {E : Type} [Field E] [NumberField E]

theorem normAtPlace_le_norm' (w : InfinitePlace E) (z : mixedSpace E) : normAtPlace w z ≤ ‖z‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => normAtPlace w z) (Finset.mem_univ w)

theorem abs_normAtPlace_add_sub_le (w : InfinitePlace E) (y k : mixedSpace E) :
    |normAtPlace w (y + k) - normAtPlace w y| ≤ ‖k‖ := by
  have h1 := normAtPlace_add_le w y k
  have h2 := normAtPlace_add_le w (y + k) (-k)
  rw [add_neg_cancel_right, normAtPlace_neg] at h2
  have h3 := normAtPlace_le_norm' w k
  rw [abs_le]; constructor <;> linarith

theorem mult_le_two' (w : InfinitePlace E) : (mult w : ℝ) ≤ 2 := by
  unfold mult; split_ifs <;> norm_num

theorem log_norm_eq_sum {z : mixedSpace E} (hz : ∀ w, normAtPlace w z ≠ 0) :
    Real.log (mixedEmbedding.norm z) = ∑ w, (mult w : ℝ) * Real.log (normAtPlace w z) := by
  rw [mixedEmbedding.norm_apply, Real.log_prod (fun w _ => pow_ne_zero _ (hz w))]
  simp_rw [Real.log_pow]

section Core

variable {y k : mixedSpace E} {B a : ℝ}

theorem half_le_normAtPlace_add (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y)
    (w : InfinitePlace E) : normAtPlace w y / 2 ≤ normAtPlace w (y + k) := by
  have h := abs_normAtPlace_add_sub_le w y k
  rw [abs_le] at h
  linarith [hy w]

theorem normAtPlace_add_pos (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y)
    (w : InfinitePlace E) : 0 < normAtPlace w (y + k) := by
  have := half_le_normAtPlace_add hk ha hy w
  linarith [hy w]

theorem abs_log_normAtPlace_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) (w : InfinitePlace E) :
    |Real.log (normAtPlace w (y + k)) - Real.log (normAtPlace w y)| ≤ 2 * B / a := by
  have ha0 : 0 < a := by linarith
  have hw : 0 < normAtPlace w y := lt_of_lt_of_le ha0 (hy w)
  refine (abs_log_sub_log_le_of_half hw ((abs_normAtPlace_add_sub_le w y k).trans hk)
    (half_le_normAtPlace_add hk ha hy w)).trans ?_
  exact div_le_div_of_nonneg_left (by linarith) ha0 (hy w)

theorem abs_log_norm_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) :
    |Real.log (mixedEmbedding.norm (y + k)) - Real.log (mixedEmbedding.norm y)| ≤
      (Module.finrank ℚ E : ℝ) * (2 * B / a) := by
  have ha0 : 0 < a := by linarith
  rw [log_norm_eq_sum (fun w => (normAtPlace_add_pos hB hk ha hy w).ne'),
    log_norm_eq_sum (fun w => (lt_of_lt_of_le ha0 (hy w)).ne'), ← Finset.sum_sub_distrib]
  calc |∑ w, ((mult w : ℝ) * Real.log (normAtPlace w (y + k)) - (mult w : ℝ) * Real.log (normAtPlace w y))|
      ≤ ∑ w, |(mult w : ℝ) * Real.log (normAtPlace w (y + k)) - (mult w : ℝ) * Real.log (normAtPlace w y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : InfinitePlace E, (mult w : ℝ) * (2 * B / a) := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (abs_log_normAtPlace_sub_le hB hk ha hy w) (Nat.cast_nonneg _)
    _ = (Module.finrank ℚ E : ℝ) * (2 * B / a) := by
        rw [← Finset.sum_mul, ← sum_mult_eq]; push_cast; ring

theorem abs_logMap_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) (w : {w : InfinitePlace E // w ≠ w₀}) :
    |logMap (y + k) w - logMap y w| ≤ 4 * (2 * B / a) := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.mpr Module.finrank_pos
  have hδ : 0 ≤ 2 * B / a := div_nonneg (by linarith) (by linarith)
  simp only [logMap_apply]
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 := abs_log_normAtPlace_sub_le hB hk ha hy w.1
  have h2 := abs_log_norm_sub_le hB hk ha hy
  have h3 : |Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
      Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹| ≤ 2 * B / a := by
    rw [← sub_mul, abs_mul, abs_of_pos (inv_pos.mpr hd)]
    calc _ ≤ (Module.finrank ℚ E : ℝ) * (2 * B / a) * (Module.finrank ℚ E : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_pos.mpr hd).le
      _ = 2 * B / a := by field_simp
  have h4 : |Real.log (normAtPlace w.1 (y + k)) - Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
      (Real.log (normAtPlace w.1 y) - Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹)| ≤
        2 * (2 * B / a) := by
    have := abs_sub (Real.log (normAtPlace w.1 (y + k)) - Real.log (normAtPlace w.1 y))
      (Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
        Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹)
    calc _ = |Real.log (normAtPlace w.1 (y + k)) - Real.log (normAtPlace w.1 y) -
          (Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
            Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹)| := by ring_nf
      _ ≤ _ := this
      _ ≤ 2 * (2 * B / a) := by linarith
  calc (mult w.1 : ℝ) * |_| ≤ 2 * (2 * (2 * B / a)) :=
        mul_le_mul (mult_le_two' w.1) h4 (abs_nonneg _) (by norm_num)
    _ = 4 * (2 * B / a) := by ring

theorem norm_logMap_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) : ‖logMap (y + k) - logMap y‖ ≤ 4 * (2 * B / a) := by
  have hδ : 0 ≤ 2 * B / a := div_nonneg (by linarith) (by linarith)
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun w => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_logMap_sub_le hB hk ha hy w

theorem rsgn_add (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y) :
    rsgn (y + k) = rsgn y := by
  unfold rsgn
  refine Finset.prod_congr rfl fun w _ => ?_
  have h1 : |k.1 w| ≤ B := by
    have := normAtPlace_le_norm' w.1 k
    rw [normAtPlace_apply_of_isReal w.2] at this
    exact (Real.norm_eq_abs _ ▸ this).trans hk
  have h2 : a ≤ |y.1 w| := by
    have := hy w.1
    rwa [normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs] at this
  have h3 : SignType.sign ((y + k).1 w) = SignType.sign (y.1 w) := by
    rw [Prod.fst_add, Pi.add_apply]
    exact sign_add_of_abs_lt (a := y.1 w) (e := k.1 w) (by linarith)
  rw [h3]

end Core

theorem exists_ucoord_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ x y : mixedSpace E,
    ∑ i, |ucoord x i - ucoord y i| ≤ A * ‖logMap x - logMap y‖ := by
  set b := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)
  refine ⟨∑ i, ‖LinearMap.toContinuousLinearMap (b.coord i)‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun x y => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : ucoord x i - ucoord y i =
      LinearMap.toContinuousLinearMap (b.coord i) (logMap x - logMap y) := by
    simp [ucoord, b, Module.Basis.coord_apply, map_sub]
  rw [h, ← Real.norm_eq_abs]
  exact ContinuousLinearMap.le_opNorm _ _

theorem abs_uphi_sub_le {x y : mixedSpace E} (hx : mixedEmbedding.norm x ≠ 0)
    (hy : mixedEmbedding.norm y ≠ 0) : |uphi x - uphi y| ≤ ∑ i, |ucoord x i - ucoord y i| := by
  unfold uphi
  rw [if_neg hx, if_neg hy]
  exact abs_Tent_sub_Tent_le _ _

theorem Gs_eq_real {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    Gs χ s x = χ (rsgn x : ZMod l) * ((uphi x * mixedEmbedding.norm x ^ (-s) : ℝ) : ℂ) := by
  unfold Gs
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (mixedEmbedding.norm_nonneg x), Complex.ofReal_neg]
  ring

theorem abs_rpow_neg_sub_le {s m N N' : ℝ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hN : m ≤ N) (hN' : m ≤ N') :
    |N' ^ (-s) - N ^ (-s)| ≤ s * |Real.log N' - Real.log N| * m⁻¹ := by
  have hm0 : 0 < m := by linarith
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith),
    mul_comm (Real.log N'), mul_comm (Real.log N)]
  have := abs_exp_neg_mul_sub_le hs (Real.log_nonneg hm) (Real.log_le_log hm0 hN')
    (Real.log_le_log hm0 hN)
  rwa [Real.exp_neg, Real.exp_log hm0] at this

theorem rpow_neg_le_inv {s m N : ℝ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hN : m ≤ N) : N ^ (-s) ≤ m⁻¹ := by
  calc N ^ (-s) ≤ N ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = N⁻¹ := Real.rpow_neg_one N
    _ ≤ m⁻¹ := inv_anti₀ (by linarith) hN

theorem pow_le_norm_of_le {z : mixedSpace E} {b : ℝ} (hb : 0 ≤ b) (h : ∀ w, b ≤ normAtPlace w z) :
    b ^ Module.finrank ℚ E ≤ mixedEmbedding.norm z := by
  rw [mixedEmbedding.norm_apply, ← sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg hb _) (fun w _ => pow_le_pow_left₀ hb (h w) _)

theorem norm_Gs_add_sub_le_core {l : ℕ} (χ : DirichletCharacter ℂ l) {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) 2)
    {A : ℝ} (hA : 0 ≤ A)
    (hAb : ∀ x y : mixedSpace E, ∑ i, |ucoord x i - ucoord y i| ≤ A * ‖logMap x - logMap y‖)
    {y k : mixedSpace E} {B a : ℝ} (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (ha2 : 2 ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) :
    ‖Gs χ s (y + k) - Gs χ s y‖ ≤
      (A * (4 * (2 * B / a)) + 2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a))) *
        ((a / 2) ^ Module.finrank ℚ E)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hyw : ∀ w, 0 < normAtPlace w y := fun w => lt_of_lt_of_le ha0 (hy w)
  have hyN : mixedEmbedding.norm y ≠ 0 := mixedEmbedding.norm_ne_zero_iff.mpr fun w => (hyw w).ne'
  have hykN : mixedEmbedding.norm (y + k) ≠ 0 :=
    mixedEmbedding.norm_ne_zero_iff.mpr fun w => (normAtPlace_add_pos hB hk ha hy w).ne'
  set m := (a / 2) ^ Module.finrank ℚ E with hm_def
  have hm1 : 1 ≤ m := one_le_pow₀ (by linarith)
  have hmN : m ≤ mixedEmbedding.norm y :=
    pow_le_norm_of_le (by linarith) fun w => by linarith [hy w]
  have hmN' : m ≤ mixedEmbedding.norm (y + k) :=
    pow_le_norm_of_le (by linarith) fun w => by
      linarith [hy w, half_le_normAtPlace_add hk ha hy w]
  have hδ : 0 ≤ 2 * B / a := div_nonneg (by linarith) ha0.le

  have hu : |uphi (y + k) - uphi y| ≤ A * (4 * (2 * B / a)) :=
    (abs_uphi_sub_le hykN hyN).trans ((hAb _ _).trans
      (mul_le_mul_of_nonneg_left (norm_logMap_sub_le hB hk ha hy) hA))

  have hP : |mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)| ≤
      2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a)) * m⁻¹ := by
    refine (abs_rpow_neg_sub_le hs.1 hm1 hmN hmN').trans ?_
    have hl := abs_log_norm_sub_le hB hk ha hy
    have hm0 : 0 ≤ m⁻¹ := inv_nonneg.mpr (by linarith)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hs.2 hl (abs_nonneg _) (by norm_num)) hm0
  have hP' : mixedEmbedding.norm (y + k) ^ (-s) ≤ m⁻¹ := rpow_neg_le_inv hs.1 hm1 hmN'
  have hP0 : 0 ≤ mixedEmbedding.norm (y + k) ^ (-s) :=
    Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _
  have hu0 : 0 ≤ uphi y := uphi_nonneg y
  have hu1 : uphi y ≤ 1 := uphi_le_one y
  have hreal : |uphi (y + k) * mixedEmbedding.norm (y + k) ^ (-s) - uphi y * mixedEmbedding.norm y ^ (-s)| ≤
      (A * (4 * (2 * B / a)) + 2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a))) * m⁻¹ := by
    have e : uphi (y + k) * mixedEmbedding.norm (y + k) ^ (-s) - uphi y * mixedEmbedding.norm y ^ (-s) =
        (uphi (y + k) - uphi y) * mixedEmbedding.norm (y + k) ^ (-s) +
          uphi y * (mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hu0]
    have h1 : |uphi (y + k) - uphi y| * mixedEmbedding.norm (y + k) ^ (-s) ≤ A * (4 * (2 * B / a)) * m⁻¹ :=
      mul_le_mul hu hP' hP0 (by positivity)
    have h2 : uphi y * |mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)| ≤
        2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a)) * m⁻¹ := by
      calc _ ≤ 1 * |mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)| :=
            mul_le_mul_of_nonneg_right hu1 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hP
    linarith
  rw [Gs_eq_real, Gs_eq_real, rsgn_add hB hk ha hy, ← mul_sub, norm_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  calc ‖χ (rsgn y : ZMod l)‖ * |_| ≤ 1 * |uphi (y + k) * mixedEmbedding.norm (y + k) ^ (-s) -
        uphi y * mixedEmbedding.norm y ^ (-s)| :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hreal

end ReciprocityTheory.Cheb
end

section
open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

theorem core_const_eq {A B c d t : ℝ} (n : ℕ) (hc : 0 < c) (ht : 0 < t) :
    (A * (4 * (2 * B / (c * t))) + 2 * (d * (2 * B / (c * t)))) * (((c * t) / 2) ^ n)⁻¹ =
      ((8 * A * B + 4 * d * B) / c * (2 / c) ^ n) * (t ^ (n + 1))⁻¹ := by
  rw [div_pow, inv_div, div_pow, mul_pow, pow_succ]
  field_simp
  ring

theorem rpow_neg_finrank_sub_one (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    t ^ (-(n : ℝ) - 1) = (t ^ (n + 1))⁻¹ := by
  rw [show -(n : ℝ) - 1 = -((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg ht, Real.rpow_natCast]

variable {E : Type} [Field E] [NumberField E]

theorem Gs_of_uphi_eq_zero {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) {x : mixedSpace E}
    (hx : uphi x = 0) : Gs χ s x = 0 := by
  rw [Gs_eq_real, hx, zero_mul, Complex.ofReal_zero, mul_zero]

theorem gs_diff_bound {l : ℕ} (χ : DirichletCharacter ℂ l) (B : ℝ) :
    ∃ R₀ C : ℝ, ∀ s ∈ Set.Icc (1 : ℝ) 2, ∀ x h : mixedSpace E, ‖h‖ ≤ B → R₀ ≤ ‖x‖ →
      ‖Gs χ s (x + h) - Gs χ s x‖ ≤ C * ‖x‖ ^ (-(Module.finrank ℚ E : ℝ) - 1) := by
  obtain ⟨c₀, hc₀, -, hsupp⟩ := exists_support_bound (E := E)
  obtain ⟨A, hA, hAb⟩ := exists_ucoord_bound (E := E)
  set B' := max B 1 with hB'
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := by linarith
  set n := Module.finrank ℚ E with hn
  set R₁ := (2 * B' + 2) / c₀ with hR₁
  have hR₁0 : 0 < R₁ := div_pos (by linarith) hc₀
  set K := (8 * A * B' + 4 * (n : ℝ) * B') / c₀ * (2 / c₀) ^ n with hK
  have hK0 : 0 ≤ K := by positivity

  have core : ∀ s ∈ Set.Icc (1 : ℝ) 2, ∀ y k : mixedSpace E, uphi y ≠ 0 → ‖k‖ ≤ B' → R₁ ≤ ‖y‖ →
      ‖Gs χ s (y + k) - Gs χ s y‖ ≤ K * (‖y‖ ^ (n + 1))⁻¹ := by
    intro s hs y k hyu hk hy
    have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hR₁0 hy
    have hcy : 2 * B' + 2 ≤ c₀ * ‖y‖ := by
      rw [hR₁, div_le_iff₀ hc₀] at hy; linarith
    have h := norm_Gs_add_sub_le_core χ hs hA hAb hB'0 hk (a := c₀ * ‖y‖) (by linarith) (by linarith)
      (hsupp y hyu).1
    rwa [core_const_eq n hc₀ hy0] at h
  refine ⟨2 * R₁ + 2 * B', K * 2 ^ (n + 1), fun s hs x h hh hx => ?_⟩
  have hx0 : 0 < ‖x‖ := by linarith
  have hhB : ‖h‖ ≤ B' := hh.trans (le_max_left _ _)
  rw [rpow_neg_finrank_sub_one _ (norm_nonneg _) n]
  have hpow : 0 < ‖x‖ ^ (n + 1) := pow_pos hx0 _
  by_cases h1 : uphi x ≠ 0
  · refine (core s hs x h h1 hhB (by linarith)).trans ?_
    have : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
    calc K * (‖x‖ ^ (n + 1))⁻¹ = K * (‖x‖ ^ (n + 1))⁻¹ * 1 := by ring
      _ ≤ K * (‖x‖ ^ (n + 1))⁻¹ * 2 ^ (n + 1) :=
          mul_le_mul_of_nonneg_left this (mul_nonneg hK0 (inv_pos.mpr hpow).le)
      _ = K * 2 ^ (n + 1) * (‖x‖ ^ (n + 1))⁻¹ := by ring
  by_cases h2 : uphi (x + h) ≠ 0
  · have hy : ‖x‖ / 2 ≤ ‖x + h‖ := by
      have := norm_sub_norm_le x (-h)
      rw [sub_neg_eq_add, norm_neg] at this
      linarith
    have hc := core s hs (x + h) (-h) h2 (by rwa [norm_neg]) (by linarith)
    rw [add_neg_cancel_right, norm_sub_rev] at hc
    refine hc.trans ?_
    have hxy : (‖x + h‖ ^ (n + 1))⁻¹ ≤ 2 ^ (n + 1) * (‖x‖ ^ (n + 1))⁻¹ := by
      have e : (2 : ℝ) ^ (n + 1) * (‖x‖ ^ (n + 1))⁻¹ = ((‖x‖ / 2) ^ (n + 1))⁻¹ := by
        rw [div_pow]; field_simp
      rw [e]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hy _)
    calc K * (‖x + h‖ ^ (n + 1))⁻¹ ≤ K * (2 ^ (n + 1) * (‖x‖ ^ (n + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left hxy hK0
      _ = K * 2 ^ (n + 1) * (‖x‖ ^ (n + 1))⁻¹ := by ring
  push Not at h1 h2
  rw [Gs_of_uphi_eq_zero χ s h1, Gs_of_uphi_eq_zero χ s h2, sub_zero, norm_zero]
  positivity

end ReciprocityTheory.Cheb
end

section
open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem nzIdeal_ne_zero (a : NZIdeal E) : a.1 ≠ 0 := by
  intro h; exact a.2 (by rw [h]; rfl)

theorem cls_mul_eq_one_iff (a b : NZIdeal E) :
    cls a * cls b = 1 ↔ Submodule.IsPrincipal (a.1 * b.1) := by
  have hab : a.1 * b.1 ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (nzIdeal_ne_zero a) (nzIdeal_ne_zero b))
  rw [← ClassGroup.mk0_eq_one_iff hab]
  unfold cls
  rw [← map_mul]
  rfl

theorem norm_embZ_ne_zero {g : 𝓞 E} (hg : g ≠ 0) : mixedEmbedding.norm (embZ g) ≠ 0 := by
  rw [norm_embZ]
  have : Algebra.norm ℤ g ≠ 0 := Algebra.norm_ne_zero_iff.2 hg
  exact abs_ne_zero.2 (Int.cast_ne_zero.2 this)

theorem uphi_embZ_zero : uphi (embZ (0 : 𝓞 E)) = 0 := by
  apply uphi_of_norm_eq_zero
  rw [norm_embZ]; simp

theorem tsum_class_eq_latSum (b : NZIdeal E) (H : Ideal (𝓞 E) → ℂ)
    (hH : Summable fun a : NZIdeal E => H (a.1 * b.1)) :
    ∑' a : NZIdeal E, (if cls a * cls b = 1 then H (a.1 * b.1) else 0) =
      ((torsionOrder E : ℕ) : ℂ)⁻¹ *
        ∑' α : b.1, ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * H (Ideal.span {(α : 𝓞 E)}) := by
  set S : Set (NZIdeal E) := {a | cls a * cls b = 1} with hS
  have hP : ∀ a : S, ∃ g : 𝓞 E, Ideal.span {g} = a.1.1 * b.1 := by
    intro a
    rcases ((cls_mul_eq_one_iff a.1 b).1 a.2) with ⟨g, hg⟩
    exact ⟨g, hg.symm⟩
  choose gen hgen using hP
  have gen_mem : ∀ a, gen a ∈ b.1 := fun a => by
    rw [← Ideal.span_singleton_le_iff_mem, hgen]; exact Ideal.mul_le_inf.trans inf_le_right
  have gen_ne : ∀ a, gen a ≠ 0 := fun a h => by
    have := hgen a
    rw [h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact mul_ne_zero (nzIdeal_ne_zero a.1) (nzIdeal_ne_zero b) (by rw [← this]; rfl)
  have hb0 : b.1 ≠ 0 := nzIdeal_ne_zero b
  let Ψ : S × (𝓞 E)ˣ → b.1 := fun p => ⟨(p.2 : 𝓞 E) * gen p.1, b.1.mul_mem_left _ (gen_mem p.1)⟩
  have hspan : ∀ p : S × (𝓞 E)ˣ, Ideal.span {((Ψ p : b.1) : 𝓞 E)} = p.1.1.1 * b.1 := fun p => by
    show Ideal.span {(p.2 : 𝓞 E) * gen p.1} = _
    rw [Ideal.span_singleton_mul_left_unit p.2.isUnit, hgen]
  have hinj : Function.Injective Ψ := by
    rintro ⟨a, u⟩ ⟨a', u'⟩ h
    have h1 : a.1.1 * b.1 = a'.1.1 * b.1 := by
      rw [← hspan (a, u), ← hspan (a', u'), h]
    have h2 : a = a' := Subtype.ext (Subtype.ext (mul_right_cancel₀ hb0 h1))
    subst h2
    have h3 : (u : 𝓞 E) * gen a = u' * gen a := congrArg Subtype.val h
    rw [Units.ext (mul_right_cancel₀ (gen_ne a) h3)]
  let F : b.1 → ℂ := fun α => ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * H (Ideal.span {(α : 𝓞 E)})
  have hsupp : Function.support F ⊆ Set.range Ψ := by
    intro α hα
    have hα0 : (α : 𝓞 E) ≠ 0 := by
      intro h0; apply hα; simp only [F, h0, uphi_embZ_zero]; simp
    have hle : Ideal.span {(α : 𝓞 E)} ≤ b.1 := (Ideal.span_singleton_le_iff_mem _).2 α.2
    obtain ⟨c, hc⟩ := Ideal.dvd_iff_le.2 hle
    have hcne : c ≠ ⊥ := by
      rintro rfl
      rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hc
      exact hα0 hc
    have hcS : (⟨c, hcne⟩ : NZIdeal E) ∈ S := by
      show cls _ * cls b = 1
      rw [cls_mul_eq_one_iff]
      exact ⟨⟨α, by rw [mul_comm, ← hc]⟩⟩
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1
      ((hgen ⟨_, hcS⟩).trans (by rw [mul_comm, ← hc]) : Ideal.span {gen ⟨_, hcS⟩} = Ideal.span {(α : 𝓞 E)})
    refine ⟨(⟨_, hcS⟩, u), Subtype.ext ?_⟩
    show (u : 𝓞 E) * gen _ = α
    rw [mul_comm]; exact hu
  rw [← hinj.tsum_eq hsupp]
  let f : S × (𝓞 E)ˣ → ℂ := fun p => ((uphi (p.2 • embZ (gen p.1)) : ℝ) : ℂ) * H (p.1.1.1 * b.1)
  have hFf : ∀ p, F (Ψ p) = f p := fun p => by
    simp only [F, f]
    rw [hspan p]
    show ((uphi (embZ ((p.2 : 𝓞 E) * gen p.1)) : ℝ) : ℂ) * _ = _
    rw [unit_smul_embZ]
  simp only [hFf]
  have hw : ∀ a : S, HasSum (fun u : (𝓞 E)ˣ => uphi (u • embZ (gen a))) (torsionOrder E : ℝ) :=
    fun a => hasSum_uphi_unit_smul _ (norm_embZ_ne_zero (gen_ne a))
  have hfib : ∀ a : S, HasSum (fun u => f (a, u)) (((torsionOrder E : ℕ) : ℂ) * H (a.1.1 * b.1)) := by
    intro a
    have := (Complex.hasSum_ofReal.2 (hw a)).mul_right (H (a.1.1 * b.1))
    simpa [f] using this
  have hnfib : ∀ a : S, HasSum (fun u => ‖f (a, u)‖) ((torsionOrder E : ℝ) * ‖H (a.1.1 * b.1)‖) := by
    intro a
    have := (hw a).mul_right ‖H (a.1.1 * b.1)‖
    have e : (fun u => ‖f (a, u)‖) = fun i => uphi (i • embZ (gen a)) * ‖H (a.1.1 * b.1)‖ := by
      funext u
      simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (uphi_nonneg _)]
    rw [e]; exact this
  have hHn : Summable fun a : S => (torsionOrder E : ℝ) * ‖H (a.1.1 * b.1)‖ :=
    ((summable_norm_iff.2 hH).subtype S).mul_left _
  have hfs : Summable f := by
    apply Summable.of_norm
    rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun a => (hnfib a).summable, ?_⟩
    simpa only [(hnfib _).tsum_eq] using hHn
  have hsum := hfs.hasSum.prod_fiberwise hfib
  rw [← hsum.tsum_eq, tsum_mul_left, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast torsionOrder_ne_zero E), one_mul,
    tsum_subtype S (fun a => H (a.1 * b.1))]
  congr 1

end ReciprocityTheory.Cheb
end

section
namespace ReciprocityTheory.Cheb

open Module

theorem norm_modEq_of_sub_mem_span {S : Type*} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (m : ℤ) {α α' : S} (h : α - α' ∈ Ideal.span {(m : S)}) :
    Algebra.norm ℤ α ≡ Algebra.norm ℤ α' [ZMOD m] := by
  classical
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.mp h
  have hα : α = α' + algebraMap ℤ S m * β := by
    rw [algebraMap_int_eq, eq_intCast, mul_comm, hβ]; ring
  rw [Int.modEq_iff_dvd, ← Int.natAbs_dvd, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
  symm
  let b := Module.Free.chooseBasis ℤ S
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, hα, map_add, map_mul,
    AlgHom.commutes]
  have key : ∀ M : Matrix (Module.Free.ChooseBasisIndex ℤ S) (Module.Free.ChooseBasisIndex ℤ S) ℤ,
      ((Int.castRingHom (ZMod m.natAbs)) M.det : ZMod m.natAbs) = ((Int.castRingHom (ZMod m.natAbs)).mapMatrix M).det :=
    fun M => RingHom.map_det _ M
  simp only [eq_intCast] at key
  rw [key, key]
  congr 1
  have h0 : ((m : ZMod m.natAbs)) = 0 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub 0 m m.natAbs).mpr (by simp)
    simpa using this.symm
  have hM : (Int.castRingHom (ZMod m.natAbs)).mapMatrix
      ((algebraMap ℤ (Matrix (Free.ChooseBasisIndex ℤ S) (Free.ChooseBasisIndex ℤ S) ℤ)) m) = 0 := by
    rw [eq_intCast, map_intCast]
    ext i j
    by_cases hij : i = j <;> simp [hij, h0, Matrix.diagonal, ← Matrix.diagonal_intCast']
  rw [map_add, map_mul, hM, zero_mul, add_zero]

theorem absNorm_dvd_algebraNorm {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] {b : Ideal S} {α : S} (h : α ∈ b) :
    (Ideal.absNorm b : ℤ) ∣ Algebra.norm ℤ α :=
  Ideal.absNorm_dvd_norm_of_mem h

theorem norm_div_absNorm_modEq {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] (l : ℤ) {b : Ideal S} {α α' : S} (hα : α ∈ b) (hα' : α' ∈ b)
    (h : α - α' ∈ Ideal.span {((l * (Ideal.absNorm b : ℤ) : ℤ) : S)}) :
    Algebra.norm ℤ α / (Ideal.absNorm b : ℤ) ≡ Algebra.norm ℤ α' / (Ideal.absNorm b : ℤ) [ZMOD l] := by
  have hm := norm_modEq_of_sub_mem_span _ h
  obtain ⟨a, ha⟩ := absNorm_dvd_algebraNorm hα
  obtain ⟨c, hc⟩ := absNorm_dvd_algebraNorm hα'
  rw [ha, hc] at hm ⊢
  by_cases hN : (Ideal.absNorm b : ℤ) = 0
  · rw [hN, Int.ediv_zero, Int.ediv_zero]
  rw [Int.mul_ediv_cancel_left _ hN, Int.mul_ediv_cancel_left _ hN]
  rw [mul_comm l] at hm
  exact Int.ModEq.mul_left_cancel' hN hm

example {E : Type*} [Field E] [NumberField E] (m : ℤ) {α α' : NumberField.RingOfIntegers E}
    (h : α - α' ∈ Ideal.span {(m : NumberField.RingOfIntegers E)}) :
    Algebra.norm ℤ α ≡ Algebra.norm ℤ α' [ZMOD m] := norm_modEq_of_sub_mem_span m h

example {E : Type*} [Field E] [NumberField E] (l : ℤ) {b : Ideal (NumberField.RingOfIntegers E)}
    {α α' : NumberField.RingOfIntegers E} (hα : α ∈ b) (hα' : α' ∈ b)
    (h : α - α' ∈ Ideal.span {((l * (Ideal.absNorm b : ℤ) : ℤ) : NumberField.RingOfIntegers E)}) :
    Algebra.norm ℤ α / (Ideal.absNorm b : ℤ) ≡ Algebra.norm ℤ α' / (Ideal.absNorm b : ℤ) [ZMOD l] :=
  norm_div_absNorm_modEq l hα hα' h

end ReciprocityTheory.Cheb
end

section
open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem isCoprime_span_mul_of_coprime_absNorm {l : ℕ} (B C : Ideal (𝓞 E))
    (hcop : Nat.Coprime (Ideal.absNorm C) (l * Ideal.absNorm B)) :
    IsCoprime (Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B) C := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have h2 : Nat.Coprime (Ideal.absNorm C) ((l * Ideal.absNorm B) * Ideal.absNorm B) :=
    Nat.Coprime.mul_right hcop (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hcop)
  obtain ⟨u, v, huv⟩ : IsCoprime (Ideal.absNorm C : ℤ)
      (((l * Ideal.absNorm B) * Ideal.absNorm B : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr h2
  have hmem1 : ((l * Ideal.absNorm B : ℕ) : 𝓞 E) * ((Ideal.absNorm B : ℕ) : 𝓞 E) ∈
      Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B :=
    Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.absNorm_mem B)
  have hmem2 : ((Ideal.absNorm C : ℕ) : 𝓞 E) ∈ C := Ideal.absNorm_mem C
  have h1 : (1 : 𝓞 E) = (v : 𝓞 E) * (((l * Ideal.absNorm B : ℕ) : 𝓞 E) * ((Ideal.absNorm B : ℕ) : 𝓞 E))
      + (u : 𝓞 E) * ((Ideal.absNorm C : ℕ) : 𝓞 E) := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) huv
    push_cast at this ⊢
    linear_combination -this
  rw [h1]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hmem1))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hmem2))

theorem sum_crt_weight_eq_zero {R : Type*} [CommRing R] (I C : Ideal R) (hIC : IsCoprime I C)
    [Fintype (R ⧸ I * C)] [Fintype (R ⧸ I)] [Fintype (R ⧸ C)] (f : R → ℂ)
    (hf : ∀ a b, a - b ∈ I → f a = f b) (σ : R ⧸ I * C → R)
    (hσ : ∀ y, Ideal.Quotient.mk _ (σ y) = y) :
    ∑ y, f (σ y) * (1 - (Fintype.card (R ⧸ C) : ℂ) * if σ y ∈ C then 1 else 0) = 0 := by
  set e := Ideal.quotientMulEquivQuotientProd I C hIC
  have hfst : ∀ p, Ideal.Quotient.mk I (σ (e.symm p)) = p.1 := by
    intro p
    have := congrArg Prod.fst (e.apply_symm_apply p)
    rw [← hσ (e.symm p), Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk] at this
    exact this
  have hsnd : ∀ p, Ideal.Quotient.mk C (σ (e.symm p)) = p.2 := by
    intro p
    have := congrArg Prod.snd (e.apply_symm_apply p)
    rw [← hσ (e.symm p), Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk] at this
    exact this
  rw [← (e.symm.toEquiv).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun u _ => ?_
  have hfe : ∀ v, f (σ (e.symm (u, v))) = f (σ (e.symm (u, 0))) := by
    intro v
    apply hf
    rw [← Ideal.Quotient.eq, hfst, hfst]
  have hC : ∀ v, σ (e.symm (u, v)) ∈ C ↔ v = 0 := by
    intro v
    rw [← Ideal.Quotient.eq_zero_iff_mem, hsnd]
  calc ∑ v, f (σ (e.symm.toEquiv (u, v))) *
        (1 - (Fintype.card (R ⧸ C) : ℂ) * if σ (e.symm.toEquiv (u, v)) ∈ C then 1 else 0)
      = ∑ v : R ⧸ C, f (σ (e.symm (u, 0))) *
        (1 - (Fintype.card (R ⧸ C) : ℂ) * if v = 0 then 1 else 0) :=
        Finset.sum_congr rfl fun v _ => by
          simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]
          rw [hfe v]
          simp only [hC v]
    _ = f (σ (e.symm (u, 0))) * ∑ v : R ⧸ C, (1 - (Fintype.card (R ⧸ C) : ℂ) * if v = 0 then 1 else 0) := by
        rw [Finset.mul_sum]
    _ = 0 := by
        simp [Finset.sum_sub_distrib]

theorem exists_reps_meanZero {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    latOf (mbc l b.1 c.1) ≤ latOf b.1 ∧
    ∃ reps : Finset (mixedSpace E), (∀ β ∈ reps, β ∈ latOf b.1) ∧
      (∀ α ∈ latOf b.1, ∃ l' ∈ latOf (mbc l b.1 c.1), ∃ β ∈ reps, α = l' + β) ∧
      (∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ latOf (mbc l b.1 c.1) → β₁ = β₂) ∧
      (∀ l' ∈ latOf (mbc l b.1 c.1), ∀ β ∈ reps, cfun χ b.1 c.1 (l' + β) = cfun χ b.1 c.1 β) ∧
      ∑ β ∈ reps, cfun χ b.1 c.1 β = 0 := by
  have hM : mbc l b.1 c.1 = Ideal.span {((l * Ideal.absNorm b.1 : ℕ) : 𝓞 E)} * b.1 * c.1 := rfl
  rw [hM]
  obtain ⟨B, hB0⟩ := b
  obtain ⟨C, hC0⟩ := c
  simp only at hcop ⊢
  set I : Ideal (𝓞 E) := Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B with hI
  have hIC : IsCoprime I C := isCoprime_span_mul_of_coprime_absNorm B C hcop
  have hIB : I ≤ B := Ideal.mul_le_right
  have hIspan : I ≤ Ideal.span {((((l : ℤ) * (Ideal.absNorm B : ℤ) : ℤ)) : 𝓞 E)} := by
    have : ((((l : ℤ) * (Ideal.absNorm B : ℤ) : ℤ)) : 𝓞 E) = ((l * Ideal.absNorm B : ℕ) : 𝓞 E) := by
      push_cast; rfl
    rw [this]; exact Ideal.mul_le_left
  have hMB : I * C ≤ B := le_trans Ideal.mul_le_left hIB
  have hMBC : I * C ≤ B * C := Ideal.mul_mono_left hIB
  have hBC : B * C = B ⊓ C := Ideal.mul_eq_inf_of_coprime
    (Ideal.isCoprime_iff_sup_eq.mp (hIC.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hIB)))
  have hl0 : (l * Ideal.absNorm B : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (Fact.out : l.Prime).ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨by exact_mod_cast hl0, hB0⟩
  have hM0 : I * C ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]; exact ⟨hI0, hC0⟩
  have := Ideal.finiteQuotientOfFreeOfNeBot (I * C) hM0
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI0
  have := Ideal.finiteQuotientOfFreeOfNeBot C hC0
  let : Fintype (𝓞 E ⧸ I * C) := Fintype.ofFinite _
  let : Fintype (𝓞 E ⧸ I) := Fintype.ofFinite _
  let : Fintype (𝓞 E ⧸ C) := Fintype.ofFinite _
  have hsurj : Function.Surjective (Ideal.Quotient.mk (I * C)) := Ideal.Quotient.mk_surjective
  obtain ⟨σ, hσ⟩ : ∃ σ : 𝓞 E ⧸ I * C → 𝓞 E, ∀ y, Ideal.Quotient.mk (I * C) (σ y) = y :=
    ⟨_, Function.surjInv_eq hsurj⟩
  have hσinj : Function.Injective σ := fun y₁ y₂ h => by rw [← hσ y₁, ← hσ y₂, h]
  have hkey : ∀ y₁ y₂, σ y₁ - σ y₂ ∈ I * C → y₁ = y₂ := by
    intro y₁ y₂ h
    rw [← hσ y₁, ← hσ y₂]; exact Ideal.Quotient.eq.mpr h

  set F : 𝓞 E → ℂ := fun α => χ (((Algebra.norm ℤ α / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) *
    (1 - (Ideal.absNorm C : ℂ) * (if α ∈ B * C then 1 else 0)) with hF
  have hcf : ∀ α, cfun χ B C (embZ α) = F α := by
    intro α; simp only [cfun, preZ_embZ, hF]
  have hchi : ∀ a a', a ∈ B → a' ∈ B → a - a' ∈ I →
      χ (((Algebra.norm ℤ a / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) =
      χ (((Algebra.norm ℤ a' / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) := by
    intro a a' ha ha' h
    congr 1
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (norm_div_absNorm_modEq (l : ℤ) ha ha' (hIspan h))
  have hper : ∀ μ ∈ I * C, ∀ a ∈ B, F (μ + a) = F a := by
    intro μ hμ a ha
    simp only [hF]
    rw [hchi (μ + a) a (B.add_mem (hMB hμ) ha) ha (by rw [add_sub_cancel_right]; exact Ideal.mul_le_left hμ)]
    simp only [Ideal.add_mem_iff_right _ (hMBC hμ)]
  set reps : Finset (mixedSpace E) :=
    (Finset.univ.filter fun y => σ y ∈ B).image (fun y => embZ (σ y)) with hreps
  have hmemreps : ∀ β ∈ reps, ∃ y, σ y ∈ B ∧ embZ (σ y) = β := by
    intro β hβ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hβ
    exact ⟨y, (Finset.mem_filter.mp hy).2, rfl⟩
  refine ⟨latOf_mono hMB, reps, ?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    obtain ⟨y, hy, rfl⟩ := hmemreps β hβ
    exact mem_latOf.mpr ⟨_, hy, rfl⟩
  · intro α hα
    obtain ⟨a, ha, rfl⟩ := mem_latOf.mp hα
    have hya : σ (Ideal.Quotient.mk _ a) - a ∈ I * C := Ideal.Quotient.eq.mp (hσ _)
    have hyB : σ (Ideal.Quotient.mk _ a) ∈ B := by
      have := B.add_mem (hMB hya) ha
      rwa [sub_add_cancel] at this
    refine ⟨embZ (a - σ (Ideal.Quotient.mk _ a)), mem_latOf.mpr ⟨_, ?_, rfl⟩,
      embZ (σ (Ideal.Quotient.mk _ a)), ?_, ?_⟩
    · have := (I * C).neg_mem hya
      rwa [neg_sub] at this
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyB⟩, rfl⟩
    · rw [map_sub, sub_add_cancel]
  · intro β₁ h₁ β₂ h₂ hd
    obtain ⟨y₁, -, rfl⟩ := hmemreps β₁ h₁
    obtain ⟨y₂, -, rfl⟩ := hmemreps β₂ h₂
    obtain ⟨μ, hμ, hμe⟩ := mem_latOf.mp hd
    have : μ = σ y₁ - σ y₂ := embZ_injective (by rw [hμe, map_sub])
    rw [hkey y₁ y₂ (this ▸ hμ)]
  · intro l' hl' β hβ
    obtain ⟨y, hy, rfl⟩ := hmemreps β hβ
    obtain ⟨μ, hμ, rfl⟩ := mem_latOf.mp hl'
    rw [← map_add, hcf, hcf, hper μ hμ _ hy]
  · rw [hreps, Finset.sum_image (fun y₁ _ y₂ _ h => hσinj (embZ_injective h))]
    simp only [hcf]
    rw [Finset.sum_filter]
    set f : 𝓞 E → ℂ := fun a => if a ∈ B then
      χ (((Algebra.norm ℤ a / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) else 0 with hf
    have hfper : ∀ a a', a - a' ∈ I → f a = f a' := by
      intro a a' h
      have hiff : a ∈ B ↔ a' ∈ B := by
        have h' := hIB h
        constructor
        · intro ha; have := B.sub_mem ha h'; rwa [sub_sub_cancel] at this
        · intro ha'; have := B.add_mem h' ha'; rwa [sub_add_cancel] at this
      simp only [hf]
      by_cases ha : a ∈ B
      · rw [if_pos ha, if_pos (hiff.mp ha), hchi a a' ha (hiff.mp ha) h]
      · rw [if_neg ha, if_neg (fun h' => ha (hiff.mpr h'))]
    have hcard : (Ideal.absNorm C : ℂ) = (Fintype.card (𝓞 E ⧸ C) : ℂ) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    refine (Finset.sum_congr rfl fun y _ => ?_).trans (sum_crt_weight_eq_zero I C hIC f hfper σ hσ)
    by_cases hy : σ y ∈ B
    · simp only [hf, hF, ← hcard, if_pos hy, hBC, Ideal.mem_inf, hy, true_and, if_true]
    · simp only [hf, if_neg hy, zero_mul]

end ReciprocityTheory.Cheb
end

section
open Set

namespace ReciprocityTheory.Cheb

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def latSumEquiv (Λ₀ Λ' : Submodule ℤ V) (hle : Λ' ≤ Λ₀) (reps : Finset V)
    (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂) :
    Λ' × reps ≃ Λ₀ :=
  Equiv.ofBijective (fun p => ⟨(p.1 : V) + (p.2 : V), Λ₀.add_mem (hle p.1.2) (hmem _ p.2.2)⟩) (by
    constructor
    · rintro ⟨l₁, β₁⟩ ⟨l₂, β₂⟩ h
      simp only [Subtype.mk.injEq] at h
      have hβ : (β₁ : V) = β₂ := huniq _ β₁.2 _ β₂.2 (by
        have e : (β₁ : V) - β₂ = l₂ - l₁ := by
          rw [sub_eq_sub_iff_add_eq_add, add_comm (β₁ : V), h]
        rw [e]; exact Λ'.sub_mem l₂.2 l₁.2)
      have hl : (l₁ : V) = l₂ := by rw [hβ] at h; exact add_right_cancel h
      exact Prod.ext (Subtype.ext hl) (Subtype.ext hβ)
    · rintro ⟨α, hα⟩
      obtain ⟨l, hl, β, hβ, rfl⟩ := hcover α hα
      exact ⟨(⟨l, hl⟩, ⟨β, hβ⟩), rfl⟩)

theorem tsum_latSum_eq (Λ₀ Λ' : Submodule ℤ V) (hle : Λ' ≤ Λ₀) (reps : Finset V)
    (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂)
    (c' : V → ℂ) (hper : ∀ l ∈ Λ', ∀ β ∈ reps, c' (l + β) = c' β) (hmean : ∑ β ∈ reps, c' β = 0)
    (g : V → ℂ) (hg : Summable fun α : Λ₀ => g α) :
    ∑' α : Λ₀, c' α * g α = ∑' l : Λ', ∑ β ∈ reps, c' β * (g (l + β) - g l) := by
  set e := latSumEquiv Λ₀ Λ' hle reps hmem hcover huniq
  have hc : ∀ α : Λ₀, ‖c' α‖ ≤ ∑ β ∈ reps, ‖c' β‖ := by
    rintro ⟨α, hα⟩
    obtain ⟨l, hl, β, hβ, rfl⟩ := hcover α hα
    rw [hper l hl β hβ]
    exact Finset.single_le_sum (f := fun β => ‖c' β‖) (fun _ _ => norm_nonneg _) hβ
  have hcg : Summable fun α : Λ₀ => c' α * g α := by
    refine summable_norm_iff.mp (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => ?_)
      ((summable_norm_iff.mpr hg).mul_left (∑ β ∈ reps, ‖c' β‖)))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc α) (norm_nonneg _)
  have hs : Summable fun p : Λ' × reps => c' (e p) * g (e p) := (e.summable_iff).mpr hcg
  rw [← e.tsum_eq, hs.tsum_prod]
  refine tsum_congr fun l => ?_
  rw [tsum_fintype]
  have h1 : ∀ β : reps, (fun α : Λ₀ => c' α * g α) (e (l, β)) = c' β * g (l + β) := by
    rintro ⟨β, hβ⟩
    show c' ((l : V) + β) * g ((l : V) + β) = _
    rw [hper l l.2 β hβ]
  simp only [h1]
  rw [Finset.sum_coe_sort reps (fun β => c' β * g (l + β))]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmean, zero_mul, sub_zero]

variable [FiniteDimensional ℝ V]

theorem exists_continuousOn_latticeSum (Λ₀ Λ' : Submodule ℤ V) [DiscreteTopology Λ₀] (hle : Λ' ≤ Λ₀)
    (reps : Finset V) (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂)
    (c' : V → ℂ) (hper : ∀ l ∈ Λ', ∀ β ∈ reps, c' (l + β) = c' β) (hmean : ∑ β ∈ reps, c' β = 0)
    (G : ℝ → V → ℂ) (r : ℝ) (hr : r < -(Module.finrank ℤ Λ₀ : ℝ))
    (hdiff : ∃ R₀ C : ℝ, ∀ s ∈ Icc (1 : ℝ) 2, ∀ β ∈ reps, ∀ x ∈ Λ', R₀ ≤ ‖x‖ →
      ‖G s (x + β) - G s x‖ ≤ C * ‖x‖ ^ r)
    (K : ℝ) (hbound : ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ Λ₀, ‖G s x‖ ≤ K)
    (hsum : ∀ s ∈ Ioc (1 : ℝ) 2, Summable fun α : Λ₀ => G s α)
    (hcont : ∀ x ∈ Λ₀, ContinuousOn (fun s => G s x) (Icc 1 2)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2, F s = ∑' α : Λ₀, c' α * G s α := by
  classical
  obtain ⟨R₀, C, hRC⟩ := hdiff
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set A := ∑ β ∈ reps, ‖c' β‖ with hAdef
  have hr0 : r < 0 := lt_of_lt_of_le hr (neg_nonpos.mpr (Nat.cast_nonneg _))
  set X := |C| + 2 * |K| * R ^ (-r) with hXdef
  have hX : 0 ≤ X := by positivity
  let u : Λ' → ℝ := fun l => A * X * ‖(l : V)‖ ^ r + if (l : V) = 0 then A * (2 * |K|) else 0
  have hu : Summable u := by
    refine Summable.add ?_ ?_
    · refine Summable.mul_left (A * X) ?_
      have h0 := ZLattice.summable_norm_rpow Λ₀ r hr
      have h1 := h0.comp_injective (i := fun l : Λ' => (⟨l, hle l.2⟩ : Λ₀))
        (fun a b h => Subtype.ext (congrArg Subtype.val h :))
      exact h1
    · apply summable_of_ne_finset_zero (s := {0})
      intro l hl
      have : (l : V) ≠ 0 := by simpa using hl
      simp [this]
  refine ⟨fun s => ∑' l : Λ', ∑ β ∈ reps, c' β * (G s (l + β) - G s l), ?_, ?_⟩
  · refine continuousOn_tsum (u := u) (fun l => ?_) hu (fun l s hs => ?_)
    · refine continuousOn_finsetSum _ fun β hβ => ?_
      exact continuousOn_const.mul
        ((hcont _ (Λ₀.add_mem (hle l.2) (hmem β hβ))).sub (hcont _ (hle l.2)))
    · have key : ∀ β ∈ reps, ‖G s (l + β) - G s l‖ ≤
          X * ‖(l : V)‖ ^ r + if (l : V) = 0 then 2 * |K| else 0 := by
        intro β hβ
        have h2K : ‖G s (l + β) - G s l‖ ≤ 2 * |K| := by
          refine (norm_sub_le _ _).trans ?_
          have := hbound s hs _ (Λ₀.add_mem (hle l.2) (hmem β hβ))
          have := hbound s hs _ (hle l.2)
          have := le_abs_self K
          linarith
        have hpow : 0 ≤ ‖(l : V)‖ ^ r := Real.rpow_nonneg (norm_nonneg _) _
        by_cases hl0 : (l : V) = 0
        · rw [if_pos hl0]
          nlinarith
        rw [if_neg hl0, add_zero]
        by_cases hR : R ≤ ‖(l : V)‖
        · have := hRC s hs β hβ l l.2 ((le_max_left _ _).trans hR)
          have hC : C * ‖(l : V)‖ ^ r ≤ |C| * ‖(l : V)‖ ^ r :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hpow
          have : 0 ≤ 2 * |K| * R ^ (-r) * ‖(l : V)‖ ^ r := by positivity
          nlinarith
        · rw [not_le] at hR
          have hlpos : 0 < ‖(l : V)‖ := norm_pos_iff.mpr hl0
          have hRr : R ^ r ≤ ‖(l : V)‖ ^ r := Real.rpow_le_rpow_of_nonpos hlpos hR.le hr0.le
          have hone : R ^ (-r) * R ^ r = 1 := by
            rw [Real.rpow_neg hRpos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hRpos r).ne']
          have hRn : 0 ≤ R ^ (-r) := Real.rpow_nonneg hRpos.le _
          have h3 : 2 * |K| ≤ 2 * |K| * R ^ (-r) * ‖(l : V)‖ ^ r := by
            calc 2 * |K| = 2 * |K| * (R ^ (-r) * R ^ r) := by rw [hone, mul_one]
              _ ≤ 2 * |K| * (R ^ (-r) * ‖(l : V)‖ ^ r) := by gcongr
              _ = _ := by ring
          have : 0 ≤ |C| * ‖(l : V)‖ ^ r := by positivity
          nlinarith
      calc ‖∑ β ∈ reps, c' β * (G s (l + β) - G s l)‖
          ≤ ∑ β ∈ reps, ‖c' β‖ * ‖G s (l + β) - G s l‖ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp only [norm_mul]
        _ ≤ ∑ β ∈ reps, ‖c' β‖ * (X * ‖(l : V)‖ ^ r + if (l : V) = 0 then 2 * |K| else 0) :=
            Finset.sum_le_sum fun β hβ => mul_le_mul_of_nonneg_left (key β hβ) (norm_nonneg _)
        _ = u l := by
            rw [← Finset.sum_mul]
            simp only [u]
            split_ifs <;> ring
  · intro s hs
    exact (tsum_latSum_eq Λ₀ Λ' hle reps hmem hcover huniq c' hper hmean (G s) (hsum s hs)).symm

end ReciprocityTheory.Cheb
end

section
open NumberField NumberField.mixedEmbedding NumberField.Units Set

open scoped Classical

namespace ReciprocityTheory.Cheb

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def gfun {l : ℕ} (χ : DirichletCharacter ℂ l) (c : NZIdeal E) (s : ℝ) (a : NZIdeal E) : ℂ :=
  χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * (1 - (Ideal.absNorm c.1 : ℂ) * (if c.1 ∣ a.1 then 1 else 0)) *
    ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))

theorem exists_F {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2,
      F s = ∑' α : b.1, cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E)) := by
  obtain ⟨hle, reps, hmem, hcover, huniq, hper, hmean⟩ := exists_reps_meanZero χ b c hcop
  obtain ⟨R₀, C, hRC⟩ := gs_diff_bound (E := E) χ (∑ β ∈ reps, ‖β‖)
  have hr : -(Module.finrank ℚ E : ℝ) - 1 < -(Module.finrank ℤ (latOf b.1) : ℝ) := by
    rw [finrank_latOf b.2]; linarith
  have hd : ∀ s ∈ Icc (1 : ℝ) 2, ∀ β ∈ reps, ∀ x ∈ latOf (mbc l b.1 c.1), R₀ ≤ ‖x‖ →
      ‖Gs χ s (x + β) - Gs χ s x‖ ≤ C * ‖x‖ ^ (-(Module.finrank ℚ E : ℝ) - 1) := by
    intro s hs β hβ x _ hR
    exact hRC s hs x β (Finset.single_le_sum (f := fun β => ‖β‖) (fun _ _ => norm_nonneg _) hβ) hR
  have hbd : ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ latOf b.1, ‖Gs χ s x‖ ≤ 1 := by
    intro s hs x hx
    obtain ⟨α, -, rfl⟩ := mem_latOf.mp hx
    exact norm_gs_embZ_le χ hs.1 α
  have hsm : ∀ s ∈ Ioc (1 : ℝ) 2, Summable fun α : latOf b.1 => Gs χ s (α : mixedSpace E) := fun s hs =>
    summable_gs χ (latOf b.1) (finrank_latOf b.2) hs.1
  have hct : ∀ x ∈ latOf b.1, ContinuousOn (fun s => Gs χ s x) (Icc 1 2) := fun x _ =>
    (continuous_gs χ x).continuousOn
  obtain ⟨F, hF, hFeq⟩ := exists_continuousOn_latticeSum (latOf b.1) (latOf (mbc l b.1 c.1)) hle reps
    hmem hcover huniq (cfun χ b.1 c.1) hper hmean (fun s => Gs χ s) _ hr ⟨R₀, C, hd⟩ 1 hbd hsm hct
  refine ⟨F, hF, fun s hs => ?_⟩
  rw [hFeq s hs]
  exact tsum_latOf b.1 (fun x => cfun χ b.1 c.1 x * Gs χ s x)

def Hfun {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (I : Ideal (𝓞 E)) : ℂ :=
  ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) * (χ (((Ideal.absNorm I / Ideal.absNorm b.1 : ℕ)) : ZMod l) *
    (1 - (Ideal.absNorm c.1 : ℂ) * (if b.1 * c.1 ∣ I then 1 else 0)) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ)))

theorem natCast_cpow_mul_cpow_neg {n : ℕ} (hn : n ≠ 0) (s : ℂ) : (n : ℂ) ^ s * (n : ℂ) ^ (-s) = 1 := by
  rw [Complex.cpow_neg, mul_inv_cancel₀]
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => hn (by exact_mod_cast h.1)

theorem Hfun_mul {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (a : NZIdeal E) :
    Hfun χ b c s (a.1 * b.1) = gfun χ c s a := by
  have hb : Ideal.absNorm b.1 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact b.2
  have hdvd : (b.1 * c.1 ∣ a.1 * b.1) ↔ c.1 ∣ a.1 := by
    rw [mul_comm a.1]; exact mul_dvd_mul_iff_left b.2
  simp only [Hfun, gfun, map_mul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb), hdvd, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  have := natCast_cpow_mul_cpow_neg hb (s : ℂ)
  linear_combination (χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) *
    (1 - (Ideal.absNorm c.1 : ℂ) * (if c.1 ∣ a.1 then 1 else 0)) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) * this

theorem uphi_Hfun_span {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (α : b.1) :
    ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * Hfun χ b c s (Ideal.span {(α : 𝓞 E)}) =
      ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) *
        (cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E))) := by
  obtain ⟨q, hq⟩ := absNorm_dvd_algebraNorm α.2
  have hbc : (b.1 * c.1 ∣ Ideal.span {(α : 𝓞 E)}) ↔ (α : 𝓞 E) ∈ b.1 * c.1 := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have hb : Ideal.absNorm b.1 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact b.2
  have hsg := rsgn_mul_norm (α : 𝓞 E)
  have hchi : χ ((((Ideal.absNorm (Ideal.span {(α : 𝓞 E)})) / Ideal.absNorm b.1 : ℕ)) : ZMod l) =
      χ ((Algebra.norm ℤ (α : 𝓞 E) / (Ideal.absNorm b.1 : ℤ) : ℤ) : ZMod l) * χ (rsgn (embZ (α : 𝓞 E)) : ZMod l) := by
    rw [← map_mul, ← Int.cast_mul, ← Int.cast_natCast, Ideal.absNorm_span_singleton, Int.natCast_div,
      Int.natCast_natAbs, ← hsg, Int.mul_ediv_assoc _ (absNorm_dvd_algebraNorm α.2), mul_comm]
  have hn : ((mixedEmbedding.norm (embZ (α : 𝓞 E)) : ℝ) : ℂ) =
      ((Ideal.absNorm (Ideal.span {(α : 𝓞 E)}) : ℕ) : ℂ) := by
    rw [norm_embZ, Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    rw [← Int.cast_abs, Complex.ofReal_intCast]
  simp only [Hfun, cfun, Gs, preZ_embZ, hbc, hchi, hn]
  ring

theorem class_sum_eq {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ)
    (hg : Summable (gfun χ c s)) :
    ∑' a : NZIdeal E, (if cls a * cls b = 1 then gfun χ c s a else 0) =
      ((torsionOrder E : ℕ) : ℂ)⁻¹ * ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) *
        ∑' α : b.1, cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E)) := by
  have h := tsum_class_eq_latSum b (Hfun χ b c s) (by simpa only [Hfun_mul] using hg)
  simp only [Hfun_mul] at h
  rw [h]
  simp_rw [uphi_Hfun_span]
  rw [tsum_mul_left, mul_assoc]

theorem exists_class_cont {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2, Summable (gfun χ c s) →
      ∑' a : NZIdeal E, (if cls a * cls b = 1 then gfun χ c s a else 0) =
        ((torsionOrder E : ℕ) : ℂ)⁻¹ * ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) * F s := by
  obtain ⟨F, hF, hFeq⟩ := exists_F χ b c hcop
  exact ⟨F, hF, fun s hs hg => by rw [class_sum_eq χ b c s hg, hFeq s hs]⟩

end

end ReciprocityTheory.Cheb
end
