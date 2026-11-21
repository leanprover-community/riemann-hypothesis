import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PiDens
import BuildAid.ForwardExisting

section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

variable {W : Type} [Fintype W] {n M : ℕ}

abbrev TupV (W : Type) [Fintype W] (n M : ℕ) : Type :=
  PiLp 2 (fun _ : W × Fin M => EuclideanSpace ℂ (Fin n))

def tupCoord : TupV W n M ≃L[ℝ] (W → Fin n → Fin M → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x w a p => x (w, p) a
      invFun := fun X => WithLp.toLp 2 fun k => WithLp.toLp 2 fun a => X k.1 a k.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp] theorem tupCoord_apply (x : TupV W n M) (w : W) (a : Fin n) (p : Fin M) :
    tupCoord x w a p = x (w, p) a := rfl

def diagOp (b : W → Matrix (Fin n) (Fin n) ℂ) : TupV W n M →ₗ[ℂ] TupV W n M where
  toFun y := WithLp.toLp 2 fun k => Matrix.toEuclideanLin (b k.1).transpose (y k)
  map_add' x y := by
    ext k : 2
    simp
  map_smul' c x := by
    ext k : 2
    simp

@[simp] theorem diagOp_apply (b : W → Matrix (Fin n) (Fin n) ℂ) (y : TupV W n M) (k : W × Fin M) :
    diagOp b y k = Matrix.toEuclideanLin (b k.1).transpose (y k) := rfl

def mixOp (J : W → Matrix (Fin M) (Fin M) ℂ) : TupV W n M →ₗ[ℂ] TupV W n M where
  toFun z := WithLp.toLp 2 fun k => (2 : ℂ) • ∑ j, J k.1 k.2 j • z (k.1, j)
  map_add' x y := by
    ext k : 2
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext k : 2
    simp [Finset.smul_sum, smul_smul, mul_comm, mul_left_comm]
    exact Finset.sum_congr rfl fun _ _ => by ring

@[simp] theorem mixOp_apply (J : W → Matrix (Fin M) (Fin M) ℂ) (z : TupV W n M) (k : W × Fin M) :
    mixOp J z k = (2 : ℂ) • ∑ j, J k.1 k.2 j • z (k.1, j) := rfl

def polarOp (J : W → Matrix (Fin M) (Fin M) ℂ) (b : W → Matrix (Fin n) (Fin n) ℂ) :
    TupV W n M →ₗ[ℝ] TupV W n M :=
  ((mixOp J).comp (diagOp b)).restrictScalars ℝ

theorem polarOp_apply (J : W → Matrix (Fin M) (Fin M) ℂ) (b : W → Matrix (Fin n) (Fin n) ℂ)
    (y : TupV W n M) : polarOp J b y = mixOp J (diagOp b y) := rfl

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound
end
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

open MeasureTheory
open scoped ComplexConjugate FourierTransform

section Decay

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def diffFun (f : SchwartzMap V ℂ) (y : V) : V → ℂ := fun x => f (x + y) * conj (f x)

theorem contDiff_translate (f : SchwartzMap V ℂ) (y : V) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => f (x + y)) :=
  (f.smooth ⊤).comp (contDiff_id.add contDiff_const)

theorem contDiff_conj (f : SchwartzMap V ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => conj (f x)) :=
  Complex.conjCLE.contDiff.comp (f.smooth ⊤)

theorem contDiff_diffFun (f : SchwartzMap V ℂ) (y : V) :
    ContDiff ℝ (⊤ : ℕ∞) (diffFun f y) :=
  (contDiff_translate f y).mul (contDiff_conj f)

theorem norm_iteratedFDeriv_conj (f : SchwartzMap V ℂ) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (fun x => conj (f x)) x‖ = ‖iteratedFDeriv ℝ i f x‖ :=
  Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) f x i

theorem peetre (x y : V) : 1 + ‖y‖ ≤ (1 + ‖x + y‖) * (1 + ‖x‖) := by
  have h : ‖y‖ ≤ ‖x + y‖ + ‖x‖ := by
    have := norm_sub_le (x + y) x
    simpa using this
  nlinarith [norm_nonneg (x + y), norm_nonneg x, mul_nonneg (norm_nonneg (x + y)) (norm_nonneg x)]

theorem diffFun_bound (f : SchwartzMap V ℂ) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : V,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (diffFun f y) x‖ * (1 + ‖y‖) ^ K ≤ C := by
  set M : ℝ := 2 ^ (K + k) *
    ((Finset.Iic (K + k, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; exact mul_nonneg (by positivity) (apply_nonneg _ _)
  have hA : ∀ i, i ≤ n → ∀ z : V, (1 + ‖z‖) ^ (K + k) * ‖iteratedFDeriv ℝ i f z‖ ≤ M := by
    intro i hi z
    exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K + k, n)) le_rfl hi f z
  have hB : ∀ i, i ≤ n → ∀ z : V, (1 + ‖z‖) ^ K * ‖iteratedFDeriv ℝ i f z‖ ≤ M := by
    intro i hi z
    refine le_trans ?_ (hA i hi z)
    have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (Nat.le_add_right _ _)) (norm_nonneg _)
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M * M), by positivity, fun x y => ?_⟩
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (contDiff_translate f y) (contDiff_conj f) x (n := n) (by exact_mod_cast le_top)
  have hw : ‖x‖ ^ k * (1 + ‖y‖) ^ K ≤ (1 + ‖x + y‖) ^ K * (1 + ‖x‖) ^ (K + k) := by
    have h1 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
    have h2 : (1 + ‖y‖) ^ K ≤ ((1 + ‖x + y‖) * (1 + ‖x‖)) ^ K :=
      pow_le_pow_left₀ (by positivity) (peetre x y) _
    calc ‖x‖ ^ k * (1 + ‖y‖) ^ K ≤ (1 + ‖x‖) ^ k * ((1 + ‖x + y‖) * (1 + ‖x‖)) ^ K := by
          gcongr
      _ = _ := by rw [mul_pow, pow_add]; ring
  have hw0 : 0 ≤ ‖x‖ ^ k * (1 + ‖y‖) ^ K := by positivity
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (diffFun f y) x‖ * (1 + ‖y‖) ^ K
      = (‖x‖ ^ k * (1 + ‖y‖) ^ K) * ‖iteratedFDeriv ℝ n (diffFun f y) x‖ := by ring
    _ ≤ (‖x‖ ^ k * (1 + ‖y‖) ^ K) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x => f (x + y)) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun x => conj (f x)) x‖ :=
        mul_le_mul_of_nonneg_left hL hw0
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((‖x‖ ^ k * (1 + ‖y‖) ^ K) *
          (‖iteratedFDeriv ℝ i f (x + y)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_iteratedFDeriv_conj, iteratedFDeriv_comp_add_right]
        ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M * M) := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        calc _ ≤ ((1 + ‖x + y‖) ^ K * (1 + ‖x‖) ^ (K + k)) *
              (‖iteratedFDeriv ℝ i f (x + y)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) :=
              mul_le_mul_of_nonneg_right hw (by positivity)
          _ = ((1 + ‖x + y‖) ^ K * ‖iteratedFDeriv ℝ i f (x + y)‖) *
              ((1 + ‖x‖) ^ (K + k) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
          _ ≤ M * M := mul_le_mul (hB i hi' _) (hA _ (Nat.sub_le _ _) _)
              (by positivity) hM0

def diffS (f : SchwartzMap V ℂ) (y : V) : SchwartzMap V ℂ where
  toFun := diffFun f y
  smooth' := contDiff_diffFun f y
  decay' := by
    intro k n
    obtain ⟨C, -, hC⟩ := diffFun_bound f k n 0
    exact ⟨C, fun x => by simpa using hC x y⟩

theorem diffS_apply (f : SchwartzMap V ℂ) (y x : V) :
    diffS f y x = f (x + y) * conj (f x) := rfl

theorem seminorm_diffS_le (f : SchwartzMap V ℂ) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V,
      SchwartzMap.seminorm ℂ k n (diffS f y) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := diffFun_bound f k n K
  refine ⟨C, hC0, fun y => ?_⟩
  have hy : 0 < (1 + ‖y‖) ^ K := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  rw [← div_eq_mul_inv, le_div_iff₀ hy]
  exact hC x y

theorem continuous_seminorm_diffS_le (f : SchwartzMap V ℂ) (K : ℕ)
    (p : Seminorm ℂ (SchwartzMap V ℂ)) (hp : Continuous p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V, p (diffS f y) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  choose D hD0 hD using fun m : ℕ × ℕ => seminorm_diffS_le f m.1 m.2 K
  refine ⟨C * ∑ m ∈ s, D m, mul_nonneg C.2 (Finset.sum_nonneg fun m _ => hD0 m), fun y => ?_⟩
  have hw : 0 ≤ ((1 + ‖y‖) ^ K)⁻¹ := by positivity
  have hsup : (s.sup (schwartzSeminormFamily ℂ V ℂ)) (diffS f y) ≤
      (∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹ := by
    refine Seminorm.finset_sup_apply_le
      (mul_nonneg (Finset.sum_nonneg fun m _ => hD0 m) hw) fun m hm => ?_
    refine (hD m y).trans (mul_le_mul_of_nonneg_right ?_ hw)
    exact Finset.single_le_sum (f := D) (fun i _ => hD0 i) hm
  calc p (diffS f y) ≤ (C • s.sup (schwartzSeminormFamily ℂ V ℂ)) (diffS f y) := hC _
    _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (diffS f y) := rfl
    _ ≤ (C : ℝ) * ((∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹) :=
        mul_le_mul_of_nonneg_left hsup C.2
    _ = _ := by ring

end Decay

section Fourier

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem fourier_diffS_decay (f : SchwartzMap V ℂ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ξ : V,
      ‖𝓕 (diffS f y) ξ‖ ≤ C * (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖ξ‖) ^ K)⁻¹) := by
  have hp : ∀ m : ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V,
      SchwartzMap.seminorm ℂ m.1 m.2 (𝓕 (diffS f y)) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by
    intro m
    refine continuous_seminorm_diffS_le f K
      ((SchwartzMap.seminorm ℂ m.1 m.2).comp
        (SchwartzMap.fourierTransformCLM ℂ (V := V) (E := ℂ)).toLinearMap) ?_
    exact ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm m).comp
      (SchwartzMap.fourierTransformCLM ℂ (V := V) (E := ℂ)).continuous
  choose D hD0 hD using hp
  set s := Finset.Iic ((K, 0) : ℕ × ℕ)
  refine ⟨2 ^ K * ∑ m ∈ s, D m,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => hD0 m), fun y ξ => ?_⟩
  have hy : 0 ≤ ((1 + ‖y‖) ^ K)⁻¹ := by positivity
  have hξ : 0 < (1 + ‖ξ‖) ^ K := by positivity
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, 0)) (k := K) (n := 0)
    le_rfl le_rfl (𝓕 (diffS f y)) ξ
  have hsup : (s.sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) (𝓕 (diffS f y)) ≤
      (∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹ := by
    refine Seminorm.finset_sup_apply_le
      (mul_nonneg (Finset.sum_nonneg fun m _ => hD0 m) hy) fun m hm => ?_
    refine (hD m y).trans (mul_le_mul_of_nonneg_right ?_ hy)
    exact Finset.single_le_sum (f := D) (fun i _ => hD0 i) hm
  rw [norm_iteratedFDeriv_zero] at h1
  have h2 : (1 + ‖ξ‖) ^ K * ‖𝓕 (diffS f y) ξ‖ ≤ 2 ^ K * ((∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹) :=
    h1.trans (mul_le_mul_of_nonneg_left hsup (by positivity))
  have h3 : ‖𝓕 (diffS f y) ξ‖ ≤ 2 ^ K * ((∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹) / (1 + ‖ξ‖) ^ K := by
    rw [le_div_iff₀ hξ]; linarith
  calc _ ≤ _ := h3
    _ = _ := by rw [div_eq_mul_inv]; ring

def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ))

theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  simp only [ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ee, this, Complex.norm_exp_ofReal_mul_I]

theorem conj_ee (t : ℝ) : conj (ee t) = ee (-t) := by
  rw [ee, ee, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem continuous_ee : Continuous ee := by
  unfold ee
  fun_prop

theorem enorm_sq_le (f : SchwartzMap V ℂ) (q : V → ℝ) (T : V →ₗ[ℝ] V) (hq : Continuous q)
    (hT : ∀ x y, q (x + y) = q x + q y + inner ℝ x (T y)) :
    ENNReal.ofReal (‖∫ x, f x * ee (q x)‖ ^ 2) ≤ ∫⁻ y, ‖𝓕 (diffS f y) (-(T y))‖ₑ := by
  set v : V → ℂ := fun x => f x * ee (q x) with hv
  set u : V → ℂ := fun x => conj (v x) with hu
  have hvc : Continuous v := f.continuous.mul (continuous_ee.comp hq)
  have hvi : Integrable v := by
    refine f.integrable.mono hvc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simp [hv, norm_ee]
  have hui : Integrable u := by
    refine hvi.mono (Complex.continuous_conj.comp hvc).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simp [hu]
  have hh : Integrable (fun z : V × V => u z.1 * v z.2) (volume.prod volume) := hui.mul_prod hvi
  have mp := measurePreserving_prod_add (volume : Measure V) (volume : Measure V)
  set F : V × V → ℂ := fun z => u z.1 * v (z.1 + z.2) with hF
  have hFi : Integrable F (volume.prod volume) := mp.integrable_comp_of_integrable hh
  have e1 : ∫ z : V × V, u z.1 * v z.2 ∂(volume.prod volume) =
      ∫ z : V × V, F z ∂(volume.prod volume) := by
    conv_lhs => rw [← mp.map_eq]
    exact integral_map mp.measurable.aemeasurable (by rw [mp.map_eq]; exact hh.aestronglyMeasurable)
  have e2 : ∀ y : V, ∫ x, F (x, y) = ee (q y) * 𝓕 (diffS f y) (-(T y)) := by
    intro y
    rw [SchwartzMap.fourier_coe, Real.fourier_eq', ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hx : Complex.exp (((-2 * Real.pi * inner ℝ x (-(T y)) : ℝ) : ℂ) * Complex.I) =
        ee (inner ℝ x (T y)) := by
      rw [ee]
      congr 1
      rw [inner_neg_right]
      push_cast
      ring
    simp only [hF, hu, hv, hx, diffS_apply, smul_eq_mul, map_mul, conj_ee, hT x y, ee_add]
    have h1 : ee (-q x) * ee (q x) = 1 := by
      rw [← ee_add]; simp [ee]
    linear_combination (conj (f x) * f (x + y) * ee (q y) * ee (inner ℝ x (T y))) * h1
  have e3 : conj (∫ x, v x) * ∫ x, v x = ∫ y, ee (q y) * 𝓕 (diffS f y) (-(T y)) := by
    rw [← integral_conj, ← integral_prod_mul u v, e1, integral_prod_symm F hFi]
    exact integral_congr_ae (ae_of_all _ e2)
  have e4 : ENNReal.ofReal (‖∫ x, v x‖ ^ 2) = ‖conj (∫ x, v x) * ∫ x, v x‖ₑ := by
    rw [← ofReal_norm, norm_mul, Complex.norm_conj, sq]
  rw [e4, e3]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  rw [enorm_mul, ← ofReal_norm (ee _), norm_ee]
  simp

theorem weyl_differencing (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : SchwartzMap V ℂ) (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : V → ℝ) (T : V →ₗ[ℝ] V), Continuous q →
      (∀ x y, q (x + y) = q x + q y + inner ℝ x (T y)) →
      ENNReal.ofReal (‖∫ x, f x * Complex.exp (2 * Real.pi * Complex.I * ((q x : ℝ) : ℂ))‖ ^ 2) ≤
        ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖T y‖) ^ K)⁻¹) := by
  obtain ⟨C, hC0, hC⟩ := fourier_diffS_decay f K
  refine ⟨C, hC0, fun q T hq hT => (enorm_sq_le f q T hq hT).trans ?_⟩
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_mul hC0, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using hC y (-(T y))

end Fourier

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Vol

def I0 : ℝ≥0∞ := ∫⁻ z : ℂ, ENNReal.ofReal (((1 + ‖z‖) ^ 3)⁻¹)

theorem I0_lt_top : I0 < ⊤ := by
  have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  have h2 := h.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun z => ?_
  congr 1
  rw [Real.rpow_neg (by positivity), show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]

def wt (l : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + ‖z‖) ^ 3)⁻¹ * ((1 + |l| * ‖z‖) ^ 3)⁻¹)

theorem measurable_wt (l : ℝ) : Measurable (wt l) := by
  unfold wt
  fun_prop

theorem lint_scale {l : ℝ} (hl : l ≠ 0) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹) = ENNReal.ofReal ((l ^ 2)⁻¹) * I0 := by
  have hr : |l| ≠ 0 := abs_ne_zero.mpr hl
  have hm := Measure.map_addHaar_smul (volume : Measure ℂ) hr
  have hF : Measurable fun w : ℂ => ENNReal.ofReal (((1 + ‖w‖) ^ 3)⁻¹) := by fun_prop
  have h1 : ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹)
      = ∫⁻ w : ℂ, ENNReal.ofReal (((1 + ‖w‖) ^ 3)⁻¹) ∂(Measure.map (fun x : ℂ => |l| • x) volume) := by
    rw [lintegral_map hF (measurable_const_smul _)]
    refine lintegral_congr fun z => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_abs]
  rw [h1, hm, lintegral_smul_measure, Complex.finrank_real_complex]
  simp only [smul_eq_mul, I0]
  congr 2
  rw [abs_of_nonneg (by positivity), sq_abs]

theorem one_var (l : ℝ) :
    ∫⁻ z : ℂ, wt l z ≤ ENNReal.ofReal (2 * I0.toReal * (1 + l ^ 2)⁻¹) := by
  have hI : ENNReal.ofReal I0.toReal = I0 := ENNReal.ofReal_toReal I0_lt_top.ne
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  rcases le_or_gt |l| 1 with h | h
  · have h1 : ∫⁻ z : ℂ, wt l z ≤ I0 := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have ha : (0:ℝ) ≤ ((1 + ‖z‖) ^ 3)⁻¹ := by positivity
      have hb : ((1 + |l| * ‖z‖) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
        (one_le_pow₀ (by nlinarith [norm_nonneg z, abs_nonneg l]))
      nlinarith
    refine h1.trans ?_
    conv_lhs => rw [← hI]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : l ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg l]
    have h3 : (1 : ℝ) ≤ 2 * (1 + l ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    nlinarith
  · have hl : l ≠ 0 := by
      rintro rfl
      simp at h
      linarith
    have h1 : ∫⁻ z : ℂ, wt l z ≤ ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹) := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have ha : (0:ℝ) ≤ ((1 + |l| * ‖z‖) ^ 3)⁻¹ := by positivity
      have hb : ((1 + ‖z‖) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
        (one_le_pow₀ (by linarith [norm_nonneg z]))
      nlinarith
    refine h1.trans ?_
    rw [lint_scale hl]
    conv_lhs => rw [← hI]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : 1 ≤ l ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have h3 : (l ^ 2)⁻¹ ≤ 2 * (1 + l ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    nlinarith

theorem pi_bound {n : ℕ} (l : Fin n → ℝ) :
    ∫⁻ z : Fin n → ℂ, ∏ i, wt (l i) (z i) ≤
      ENNReal.ofReal ((2 * I0.toReal) ^ n * (∏ i, (1 + l i ^ 2))⁻¹) := by
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod
    (f := fun i => wt (l i)) fun i => (measurable_wt (l i)).aemeasurable]
  refine (Finset.prod_le_prod' fun i _ => one_var (l i)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_inv_distrib]

theorem prod_le_pow {n K : ℕ} (hK : 3 * n ≤ K) {x : Fin n → ℝ} {a : ℝ} (h0 : ∀ i, 0 ≤ x i)
    (hx : ∀ i, x i ≤ a) (ha : 0 ≤ a) :
    ((1 + a) ^ K)⁻¹ ≤ ∏ i, ((1 + x i) ^ 3)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  refine inv_anti₀ (Finset.prod_pos fun i _ => by have := h0 i; positivity) ?_
  calc ∏ i, (1 + x i) ^ 3 ≤ ∏ _i : Fin n, (1 + a) ^ 3 :=
        Finset.prod_le_prod (fun i _ => by have := h0 i; positivity)
          fun i _ => pow_le_pow_left₀ (by have := h0 i; positivity) (by linarith [hx i]) 3
    _ = (1 + a) ^ (3 * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    _ ≤ (1 + a) ^ K := pow_le_pow_right₀ (by linarith) hK

theorem weight_le {n K : ℕ} (hK : 3 * n ≤ K) (l : Fin n → ℝ) {a d : ℝ} (z : Fin n → ℂ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (h1 : ∀ i, ‖z i‖ ≤ a) (h2 : ∀ i, |l i| * ‖z i‖ ≤ d) :
    ENNReal.ofReal (((1 + a) ^ K)⁻¹ * ((1 + d) ^ K)⁻¹) ≤ ∏ i, wt (l i) (z i) := by
  unfold wt
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity, Finset.prod_mul_distrib]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul (prod_le_pow hK (fun i => norm_nonneg _) h1 ha)
    (prod_le_pow hK (fun i => by positivity) h2 hd) (by positivity)
    (Finset.prod_nonneg fun i _ => by positivity)

theorem det_conj_unitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    det ((U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ)) = det X := by
  rw [det_mul, det_mul, mul_comm (det (U : Matrix (Fin n) (Fin n) ℂ)), mul_assoc, ← det_mul,
    mem_unitaryGroup_iff.mp U.2, det_one, mul_one]

theorem detW_eq {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) :
    detW b = ∏ i, (1 + hb.eigenvalues i ^ 2) := by
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hb.eigenvalues) with hD
  have hs := hb.spectral_theorem
  have h1 : 1 + b * b = Unitary.conjStarAlgAut ℂ _ hb.eigenvectorUnitary (1 + D * D) := by
    rw [map_add, map_one, map_mul, ← hs]
  have h2 : 1 + D * D = diagonal fun i => (((1 + hb.eigenvalues i ^ 2 : ℝ)) : ℂ) := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one, diagonal_add]
    congr 1
    ext i
    simp [sq]
  rw [detW, h1, Unitary.conjStarAlgAut_apply, det_conj_unitary, h2, det_diagonal,
    ← Complex.ofReal_prod, Complex.ofReal_re]

theorem repr_apply_lin {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (y : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    hb.eigenvectorBasis.repr (Matrix.toEuclideanLin b y) i =
      (hb.eigenvalues i : ℂ) * hb.eigenvectorBasis.repr y i := by
  have hs : (Matrix.toEuclideanLin b).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hb
  have he : Matrix.toEuclideanLin b (hb.eigenvectorBasis i) =
      (hb.eigenvalues i : ℂ) • hb.eigenvectorBasis i := by
    have := hb.mulVec_eigenvectorBasis i
    apply PiLp.ext
    intro j
    have h2 := congrFun this j
    simpa [toLpLin_apply] using h2
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, ← hs, he, inner_smul_left]
  simp

theorem map_isometry {n : ℕ} (m : Measure (EuclideanSpace ℂ (Fin n))) [m.IsAddHaarMeasure]
    (R : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving R m m := by
  have hp := LinearIsometryEquiv.measurePreserving
    (⟨R.toLinearEquiv.restrictScalars ℝ, R.norm_map⟩ :
      EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
  have hc := Measure.isAddLeftInvariant_eq_smul m (volume : Measure (EuclideanSpace ℂ (Fin n)))
  refine ⟨R.continuous.measurable, ?_⟩
  have hm : Measure.map R (volume : Measure (EuclideanSpace ℂ (Fin n))) = volume := hp.map_eq
  conv_lhs => rw [hc]
  rw [Measure.map_smul, hm, ← hc]

theorem exists_scale (n : ℕ) (m : Measure (EuclideanSpace ℂ (Fin n))) [m.IsAddHaarMeasure] :
    ∃ c : NNReal, ∀ P : (Fin n → ℂ) → ℝ≥0∞, Measurable P →
      ∫⁻ y, P (WithLp.ofLp y) ∂m = c * ∫⁻ x, P x := by
  let e := EuclideanSpace.equiv (Fin n) ℂ
  haveI : (Measure.map e m).IsAddHaarMeasure := e.isAddHaarMeasure_map m
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e m = c • (volume : Measure (Fin n → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun P hP => ?_⟩
  have h1 : ∫⁻ y, P (WithLp.ofLp y) ∂m = ∫⁻ x, P x ∂(Measure.map e m) := by
    rw [lintegral_map hP e.continuous.measurable]
    rfl
  rw [h1, hc, lintegral_smul_measure]
  rfl

theorem volume_bound : ∀ (n K : ℕ), 3 * n ≤ K → ∀ m : Measure (EuclideanSpace ℂ (Fin n)), m.IsAddHaarMeasure →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∫⁻ y, ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖Matrix.toEuclideanLin b y‖) ^ K)⁻¹) ∂m ≤
      ENNReal.ofReal (C * (detW b)⁻¹) := by
  intro n K hK m hm
  obtain ⟨c, hc⟩ := exists_scale n m
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  refine ⟨c * (2 * I0.toReal) ^ n, by positivity, fun b hb => ?_⟩
  set l := hb.eigenvalues with hl
  set R := hb.eigenvectorBasis.repr with hR
  let P : (Fin n → ℂ) → ℝ≥0∞ := fun x => ∏ i, wt (l i) (x i)
  have hP : Measurable P :=
    Finset.measurable_prod _ fun i _ => (measurable_wt (l i)).comp (measurable_pi_apply i)
  have hG : Measurable fun y : EuclideanSpace ℂ (Fin n) => P (WithLp.ofLp y) :=
    hP.comp (EuclideanSpace.equiv (Fin n) ℂ).continuous.measurable
  have h1 : ∀ y : EuclideanSpace ℂ (Fin n),
      ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖Matrix.toEuclideanLin b y‖) ^ K)⁻¹) ≤
        P (WithLp.ofLp (R y)) := by
    intro y
    refine weight_le hK l _ (norm_nonneg _) (norm_nonneg _) (fun i => ?_) (fun i => ?_)
    · rw [← R.norm_map y]
      exact PiLp.norm_apply_le (R y) i
    · rw [← R.norm_map (Matrix.toEuclideanLin b y)]
      refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le (R (Matrix.toEuclideanLin b y)) i)
      rw [hR, repr_apply_lin hb, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ ∫⁻ y, P (WithLp.ofLp (R y)) ∂m := lintegral_mono h1
    _ = ∫⁻ y, P (WithLp.ofLp y) ∂m := (map_isometry m R).lintegral_comp hG
    _ = c * ∫⁻ x, P x := hc P hP
    _ ≤ c * ENNReal.ofReal ((2 * I0.toReal) ^ n * (∏ i, (1 + l i ^ 2))⁻¹) := by
        gcongr
        exact pi_bound l
    _ = ENNReal.ofReal (c * (2 * I0.toReal) ^ n * (detW b)⁻¹) := by
        rw [detW_eq hb, mul_assoc, ENNReal.ofReal_mul (p := (c : ℝ)) (by positivity),
          ENNReal.ofReal_coe_nnreal]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Vol
end
end

section
section
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
open scoped ComplexOrder
noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound

theorem exists_schwartz_coord : ∀ (W : Type) [Fintype W] (n M N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)),
    Continuous e → Continuous e.symm → ∀ f : SchwartzMap (Fin N → ℝ) ℂ,
    ∃ g : SchwartzMap (TupV W n M) ℂ, ∀ x, g x = f (e (tupCoord x)) := by
  intro W _ n M N e he he' f
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (tupCoord.trans (e.toRealLinearEquiv he he')) f,
    fun x => rfl⟩

theorem integral_eq_coord : ∀ (W : Type) [Fintype W] (n M : ℕ) (μ : Measure (W → Fin n → Fin M → ℂ)),
    μ.IsAddHaarMeasure → ∃ c : ℝ, 0 ≤ c ∧ ∀ F : (W → Fin n → Fin M → ℂ) → ℂ,
    ∫ X, F X ∂μ = (c : ℂ) * ∫ x : TupV W n M, F (tupCoord x) := by
  intro W _ n M μ hμ
  have hν : (Measure.map tupCoord (volume : Measure (TupV W n M))).IsAddHaarMeasure :=
    tupCoord.isAddHaarMeasure_map _
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • Measure.map tupCoord (volume : Measure (TupV W n M)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul μ (Measure.map tupCoord (volume : Measure (TupV W n M)))⟩
  refine ⟨(c : ℝ), NNReal.coe_nonneg _, fun F => ?_⟩
  have hemb : MeasurableEmbedding (tupCoord : TupV W n M → (W → Fin n → Fin M → ℂ)) :=
    tupCoord.toHomeomorph.measurableEmbedding
  rw [hc, integral_smul_nnreal_measure, hemb.integral_map, NNReal.smul_def, Complex.real_smul]

private theorem two_mul_sum_quarter_inv_mul_two_mul_sum_eq {M : ℕ} (A : Matrix (Fin M) (Fin M) ℂ) (hA : A.det ≠ 0)
    (v : Fin M → ℂ) (p : Fin M) :
    (2 : ℂ) * ∑ j, ((4 : ℂ)⁻¹ • A⁻¹) p j * ((2 : ℂ) * ∑ l, A j l * v l) = v p := by
  have h1 : ∑ j, A⁻¹ p j * ∑ l, A j l * v l = v p := by
    have h := congrFun (Matrix.mulVec_mulVec v A⁻¹ A) p
    rw [Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec] at h
    simpa [Matrix.mulVec, dotProduct] using h
  calc (2 : ℂ) * ∑ j, ((4 : ℂ)⁻¹ • A⁻¹) p j * ((2 : ℂ) * ∑ l, A j l * v l)
      = ∑ j, A⁻¹ p j * ∑ l, A j l * v l := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul]
        ring
    _ = v p := h1

theorem norm_diag_le_polar : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ),
    (∀ w, (J w).det ≠ 0) → ∃ C : ℝ, 1 ≤ C ∧ ∀ (b : W → Matrix (Fin n) (Fin n) ℂ) (y : TupV W n M)
      (k : W × Fin M), ‖Matrix.toEuclideanLin (b k.1).transpose (y k)‖ ≤ C * ‖polarOp J b y‖ := by
  intro W _ n M J hJ
  have hinv : ∀ z : TupV W n M,
      mixOp (fun w => (4 : ℂ)⁻¹ • (J w)⁻¹) (mixOp J z) = z := by
    intro z
    ext k a
    obtain ⟨w, p⟩ := k
    simp only [mixOp_apply]
    simp
    exact two_mul_sum_quarter_inv_mul_two_mul_sum_eq (J w) (hJ w) (fun l => z (w, l) a) p
  let T : TupV W n M →L[ℝ] TupV W n M :=
    LinearMap.toContinuousLinearMap ((mixOp (fun w => (4 : ℂ)⁻¹ • (J w)⁻¹)).restrictScalars ℝ)
  refine ⟨max 1 ‖T‖, le_max_left _ _, fun b y k => ?_⟩
  rw [← diagOp_apply]
  calc ‖diagOp b y k‖ ≤ ‖diagOp b y‖ := PiLp.norm_apply_le _ _
    _ = ‖T (polarOp J b y)‖ := by
        rw [polarOp_apply]
        simp only [T, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_restrictScalars, hinv]
    _ ≤ ‖T‖ * ‖polarOp J b y‖ := T.le_opNorm _
    _ ≤ max 1 ‖T‖ * ‖polarOp J b y‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem lintegral_prod_le : ∀ (W : Type) [Fintype W] (n M : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ h : W × Fin M → EuclideanSpace ℂ (Fin n) → ENNReal, (∀ k, Measurable (h k)) →
    ∫⁻ y : TupV W n M, ∏ k, h k (y k) ≤ ENNReal.ofReal C * ∏ k, ∫⁻ z, h k z := by
  intro W _ n M
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : W × Fin M => EuclideanSpace ℂ (Fin n))
  have hν : (Measure.map L (volume : Measure (TupV W n M))).IsAddHaarMeasure :=
    L.isAddHaarMeasure_map _
  have hπ : (Measure.pi fun _ : W × Fin M => (volume : Measure (EuclideanSpace ℂ (Fin n)))).IsAddHaarMeasure := by
    haveI : ∀ _ : W × Fin M, (volume : Measure (EuclideanSpace ℂ (Fin n))).IsAddHaarMeasure :=
      fun _ => inferInstance
    haveI : MeasurableAdd (EuclideanSpace ℂ (Fin n)) := inferInstance
    first
      | exact Measure.pi.isAddHaarMeasure _
      | exact Measure.pi.isAddHaarMeasure
      | exact @Measure.pi.isAddHaarMeasure (W × Fin M) _ (fun _ => EuclideanSpace ℂ (Fin n)) _
          (fun _ => volume) _ _ _ _ _
  have hνπ := Measure.isAddLeftInvariant_eq_smul (Measure.map L (volume : Measure (TupV W n M)))
    (Measure.pi fun _ : W × Fin M => (volume : Measure (EuclideanSpace ℂ (Fin n))))
  refine ⟨(Measure.addHaarScalarFactor (Measure.map L (volume : Measure (TupV W n M)))
    (Measure.pi fun _ : W × Fin M => (volume : Measure (EuclideanSpace ℂ (Fin n)))) : ℝ),
    NNReal.coe_nonneg _, fun h hh => le_of_eq ?_⟩
  have hm : Measurable fun Y : W × Fin M → EuclideanSpace ℂ (Fin n) => ∏ k, h k (Y k) :=
    Finset.measurable_prod _ fun k _ => (hh k).comp (measurable_pi_apply k)
  have hmap := lintegral_map hm L.continuous.measurable (μ := (volume : Measure (TupV W n M)))
  rw [hνπ] at hmap
  rw [lintegral_smul_measure, PI.AprimeInfG.lintegral_fintype_prod h hh] at hmap
  rw [ENNReal.ofReal_coe_nnreal]
  exact hmap.symm.trans (by rw [ENNReal.smul_def, smul_eq_mul])

theorem sum_four_swap_pairs_alt {α β : Type} [Fintype α] [Fintype β] (t : α → β → α → β → ℂ) :
    ∑ i, ∑ c, ∑ j, ∑ a, t i c j a = ∑ j, ∑ a, ∑ i, ∑ c, t i c j a := by
  calc ∑ i, ∑ c, ∑ j, ∑ a, t i c j a = ∑ i, ∑ j, ∑ c, ∑ a, t i c j a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ c, ∑ a, t i c j a := Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ a, ∑ c, t i c j a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ i, ∑ c, t i c j a := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

def sesq {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (b : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Fin n → Fin M → ℂ) : ℂ :=
  ∑ i, ∑ c, ∑ j, ∑ a, (starRingEnd ℂ) (X c i) * J i j * b a c * Y a j

theorem trace_gram {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (b : Matrix (Fin n) (Fin n) ℂ)
    (X : Fin n → Fin M → ℂ) : Matrix.trace (b * gramC J X) = sesq J b X X := by
  have h : Matrix.trace (b * gramC J X) =
      ∑ a, ∑ c, ∑ i, ∑ j, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramC, Finset.mul_sum]
  rw [h]
  unfold sesq
  calc ∑ a, ∑ c, ∑ i, ∑ j, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j)
      = ∑ c, ∑ a, ∑ i, ∑ j, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j) := Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ a, ∑ j, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ c, ∑ a, ∑ j, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j) := Finset.sum_comm
    _ = ∑ i, ∑ c, ∑ j, ∑ a, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sesq_add_left {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (b : Matrix (Fin n) (Fin n) ℂ)
    (X X' Y : Fin n → Fin M → ℂ) : sesq J b (X + X') Y = sesq J b X Y + sesq J b X' Y := by
  simp only [sesq, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem sesq_add_right {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (b : Matrix (Fin n) (Fin n) ℂ)
    (X Y Y' : Fin n → Fin M → ℂ) : sesq J b X (Y + Y') = sesq J b X Y + sesq J b X Y' := by
  simp only [sesq, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem sesq_conj {n M : ℕ} {J : Matrix (Fin M) (Fin M) ℂ} {b : Matrix (Fin n) (Fin n) ℂ}
    (hJ : J.IsHermitian) (hb : b.IsHermitian) (X Y : Fin n → Fin M → ℂ) :
    (starRingEnd ℂ) (sesq J b Y X) = sesq J b X Y := by
  have hJ' : ∀ i j, (starRingEnd ℂ) (J i j) = J j i := fun i j => by
    rw [starRingEnd_apply]; exact hJ.apply j i
  have hb' : ∀ i j, (starRingEnd ℂ) (b i j) = b j i := fun i j => by
    rw [starRingEnd_apply]; exact hb.apply j i
  simp only [sesq, map_sum, map_mul, Complex.conj_conj, hJ', hb']
  refine Eq.trans ?_ (sum_four_swap_pairs_alt _).symm
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sesq_re_add {n M : ℕ} {J : Matrix (Fin M) (Fin M) ℂ} {b : Matrix (Fin n) (Fin n) ℂ}
    (hJ : J.IsHermitian) (hb : b.IsHermitian) (X Y : Fin n → Fin M → ℂ) :
    (sesq J b (X + Y) (X + Y)).re =
      (sesq J b X X).re + (sesq J b Y Y).re + 2 * (sesq J b X Y).re := by
  rw [sesq_add_left, sesq_add_right, sesq_add_right]
  have h := congrArg Complex.re (sesq_conj hJ hb X Y)
  rw [Complex.conj_re] at h
  simp only [Complex.add_re]
  rw [h]
  ring

theorem inner_polarOp {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (b : W → Matrix (Fin n) (Fin n) ℂ) (x y : TupV W n M) :
    inner ℝ x (polarOp J b y) =
      ∑ w, 2 * (sesq (J w) (b w) (tupCoord x w) (tupCoord y w)).re := by
  rw [polarOp_apply, PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hre : ∀ u v : EuclideanSpace ℂ (Fin n), inner ℝ u v = RCLike.re (inner ℂ u v) := by
    intro u v
    first
      | rfl
      | (simp only [PiLp.inner_apply, map_sum]
         exact Finset.sum_congr rfl fun a _ => by first | rfl | exact Complex.real_inner_eq_re_inner _ _)
  have key : ∑ p, inner ℂ (x (w, p)) (mixOp J (diagOp b y) (w, p)) =
      2 * sesq (J w) (b w) (tupCoord x w) (tupCoord y w) := by
    simp only [PiLp.inner_apply, mixOp_apply, diagOp_apply, tupCoord_apply]
    simp [sesq, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  calc ∑ p, inner ℝ (x (w, p)) (mixOp J (diagOp b y) (w, p))
      = ∑ p, RCLike.re (inner ℂ (x (w, p)) (mixOp J (diagOp b y) (w, p))) :=
        Finset.sum_congr rfl fun p _ => hre _ _
    _ = RCLike.re (∑ p, inner ℂ (x (w, p)) (mixOp J (diagOp b y) (w, p))) := (map_sum _ _ _).symm
    _ = 2 * (sesq (J w) (b w) (tupCoord x w) (tupCoord y w)).re := by rw [key]; simp

theorem phase_polar : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ),
    (∀ w, (J w).IsHermitian) → ∀ b : W → Matrix (Fin n) (Fin n) ℂ, (∀ w, (b w).IsHermitian) →
    ∀ x y : TupV W n M, phaseM J b (tupCoord (x + y)) =
      phaseM J b (tupCoord x) + phaseM J b (tupCoord y) + inner ℝ x (polarOp J b y) := by
  intro W _ n M J hJ b hb x y
  simp only [phaseM, trace_gram, map_add, Pi.add_apply, inner_polarOp]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => sesq_re_add (hJ w) (hb w) _ _

theorem continuous_phase {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (b : W → Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun x : TupV W n M => phaseM J b (tupCoord x) := by
  have h : Continuous (fun X : W → Fin n → Fin M → ℂ => phaseM J b X) := by
    simp only [phaseM, trace_gram, sesq]
    refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
    fun_prop
  exact h.comp tupCoord.continuous

theorem detW_transpose {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) : detW b.transpose = detW b := by
  unfold detW
  rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + b.transpose * b.transpose = (1 + b * b).transpose by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul], Matrix.det_transpose]

theorem detW_pos {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : 0 < detW b := by
  rw [Vol.detW_eq hb]
  exact Finset.prod_pos fun i _ => by positivity

theorem weight_le (κ : Type) [Fintype κ] (L : ℕ) (C r s : ℝ) (u v : κ → ℝ) (hC : 1 ≤ C)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (hur : ∀ k, u k ≤ r)
    (hvs : ∀ k, v k ≤ C * s) :
    ((1 + r) ^ (Fintype.card κ * L))⁻¹ * ((1 + s) ^ (Fintype.card κ * L))⁻¹ ≤
      (C ^ L) ^ Fintype.card κ * ∏ k, (((1 + u k) ^ L)⁻¹ * ((1 + v k) ^ L)⁻¹) := by
  have hr1 : 0 < 1 + r := by linarith
  have hs1 : 0 < 1 + s := by linarith
  have hC0 : 0 < C := by linarith
  have hD : C ^ L ≠ 0 := pow_ne_zero _ hC0.ne'
  have key : ∀ k, ((1 + r) ^ L)⁻¹ * ((C ^ L)⁻¹ * ((1 + s) ^ L)⁻¹) ≤
      ((1 + u k) ^ L)⁻¹ * ((1 + v k) ^ L)⁻¹ := by
    intro k
    have hu1 : 0 < 1 + u k := by linarith [hu k]
    have hv1 : 0 < 1 + v k := by linarith [hv k]
    have h1 : ((1 + r) ^ L)⁻¹ ≤ ((1 + u k) ^ L)⁻¹ := by
      apply inv_anti₀ (pow_pos hu1 L)
      exact pow_le_pow_left₀ hu1.le (by linarith [hur k]) L
    have h2 : (C ^ L)⁻¹ * ((1 + s) ^ L)⁻¹ ≤ ((1 + v k) ^ L)⁻¹ := by
      rw [← mul_inv, ← mul_pow]
      apply inv_anti₀ (pow_pos hv1 L)
      apply pow_le_pow_left₀ hv1.le
      nlinarith [hvs k]
    exact mul_le_mul h1 h2 (mul_nonneg (inv_nonneg.mpr (pow_nonneg hC0.le L))
      (inv_nonneg.mpr (pow_nonneg hs1.le L))) (inv_nonneg.mpr (pow_nonneg hu1.le L))
  calc ((1 + r) ^ (Fintype.card κ * L))⁻¹ * ((1 + s) ^ (Fintype.card κ * L))⁻¹
      = (C ^ L) ^ Fintype.card κ *
          ∏ _k : κ, (((1 + r) ^ L)⁻¹ * ((C ^ L)⁻¹ * ((1 + s) ^ L)⁻¹)) := by
        rw [Finset.prod_const, Finset.card_univ,
          show ((1 + r) ^ L)⁻¹ * ((C ^ L)⁻¹ * ((1 + s) ^ L)⁻¹) =
            (C ^ L)⁻¹ * (((1 + r) ^ L)⁻¹ * ((1 + s) ^ L)⁻¹) by ring,
          mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hD, one_pow, one_mul, mul_pow,
          inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm L]
    _ ≤ (C ^ L) ^ Fintype.card κ * ∏ k, (((1 + u k) ^ L)⁻¹ * ((1 + v k) ^ L)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (pow_nonneg hC0.le L) _)
        exact Finset.prod_le_prod (fun k _ => mul_nonneg (inv_nonneg.mpr (pow_nonneg hr1.le L))
          (mul_nonneg (inv_nonneg.mpr (pow_nonneg hC0.le L)) (inv_nonneg.mpr (pow_nonneg hs1.le L))))
          (fun k _ => key k)

theorem sq_prod_rpow {W : Type} [Fintype W] (M : ℕ) (D : W → ℝ) (hD : ∀ w, 0 < D w) :
    (∏ w, D w ^ (-(M : ℝ) / 2)) ^ 2 = ∏ w, ((D w)⁻¹) ^ M := by
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro w _
  have h0 := (hD w).le
  rw [← Real.rpow_mul_natCast h0, show (-(M : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -(M : ℝ) by push_cast; ring,
    Real.rpow_neg h0, Real.rpow_natCast, inv_pow]

private theorem coreC_comp_eq_integral_tupCoord_phase {W : Type} [Fintype W] {n M N : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ))
    (f : SchwartzMap (Fin N → ℝ) ℂ) (g : SchwartzMap (TupV W n M) ℂ)
    (hg : ∀ x, g x = f (e (tupCoord x))) (c : ℝ)
    (hc : ∀ F : (W → Fin n → Fin M → ℂ) → ℂ, ∫ X, F X ∂μ = (c : ℂ) * ∫ x : TupV W n M, F (tupCoord x))
    (b : W → hermC n) :
    coreC J μ (fun X => f (e X)) b = (c : ℂ) * ∫ x, g x * Complex.exp (2 * Real.pi * Complex.I *
      ((phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) (tupCoord x) : ℝ) : ℂ)) := by
  unfold coreC
  rw [hc]
  simp only [hg]

theorem core_bound : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ), (∀ w, (J w).IsHermitian) → (∀ w, (J w).det ≠ 0) →
  ∀ (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  ∃ C : ℝ, ∀ b : W → hermC n, ‖coreC J μ (fun X => f (e X)) b‖ ≤
    C * ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2) := by
  intro W _ n M J hJ hJd N e he he' f μ hμ
  obtain ⟨c, hc0, hc⟩ := integral_eq_coord W n M μ hμ
  obtain ⟨g, hg⟩ := exists_schwartz_coord W n M N e he he' f
  obtain ⟨C2, hC2, hdiag⟩ := norm_diag_le_polar W n M J hJd
  obtain ⟨C3, hC3, hprod⟩ := lintegral_prod_le W n M
  obtain ⟨C1, hC1, hweyl⟩ :=
    Weyl.weyl_differencing (TupV W n M) g (Fintype.card (W × Fin M) * (3 * n))
  obtain ⟨C4, hC4, hvol⟩ :=
    Vol.volume_bound n (3 * n) le_rfl (volume : Measure (EuclideanSpace ℂ (Fin n))) inferInstance
  have hA0 : 0 ≤ (C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) :=
    pow_nonneg (pow_nonneg (by linarith) _) _
  have hK0 : 0 ≤ C1 * (C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) * C3 * C4 ^ Fintype.card (W × Fin M) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1 hA0) hC3) (pow_nonneg hC4 _)
  refine ⟨c * Real.sqrt (C1 * (C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) * C3 *
    C4 ^ Fintype.card (W × Fin M)), fun b => ?_⟩
  have hB : ∀ w, (b w : Matrix (Fin n) (Fin n) ℂ).IsHermitian := fun w => mem_hermC.mp (b w).2
  have hd : ∀ w, 0 < detW (b w : Matrix (Fin n) (Fin n) ℂ) := fun w => detW_pos (hB w)
  have hcore := coreC_comp_eq_integral_tupCoord_phase J μ e f g hg c hc b
  have hhm : ∀ k : W × Fin M, Measurable fun z : EuclideanSpace ℂ (Fin n) =>
      ENNReal.ofReal (((1 + ‖z‖) ^ (3 * n))⁻¹ *
        ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose z‖) ^ (3 * n))⁻¹) := by
    intro k
    have hlin : Continuous (Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose) :=
      LinearMap.continuous_of_finiteDimensional _
    fun_prop
  have hpt : ∀ y : TupV W n M,
      ENNReal.ofReal (((1 + ‖y‖) ^ (Fintype.card (W × Fin M) * (3 * n)))⁻¹ *
        ((1 + ‖polarOp J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) y‖) ^
          (Fintype.card (W × Fin M) * (3 * n)))⁻¹) ≤
      ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M)) *
        ∏ k, ENNReal.ofReal (((1 + ‖y k‖) ^ (3 * n))⁻¹ *
          ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose (y k)‖) ^
            (3 * n))⁻¹) := by
    intro y
    have hwl := weight_le (W × Fin M) (3 * n) C2 ‖y‖
      ‖polarOp J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) y‖ (fun k => ‖y k‖)
      (fun k => ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose (y k)‖) hC2
      (norm_nonneg _) (norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun k => PiLp.norm_apply_le y k) (fun k => hdiag (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) y k)
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => by positivity), ← ENNReal.ofReal_mul hA0]
    exact ENNReal.ofReal_le_ofReal hwl
  have hkv : ∀ k : W × Fin M, ∫⁻ z : EuclideanSpace ℂ (Fin n),
      ENNReal.ofReal (((1 + ‖z‖) ^ (3 * n))⁻¹ *
        ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose z‖) ^ (3 * n))⁻¹) ≤
      ENNReal.ofReal (C4 * (detW (b k.1 : Matrix (Fin n) (Fin n) ℂ))⁻¹) := by
    intro k
    have h := hvol _ (hB k.1).transpose
    rwa [detW_transpose] at h
  have hP0 : ∀ k : W × Fin M, 0 ≤ C4 * (detW (b k.1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ :=
    fun k => mul_nonneg hC4 (inv_nonneg.mpr (hd k.1).le)
  have hint : ∫⁻ y : TupV W n M,
      ENNReal.ofReal (((1 + ‖y‖) ^ (Fintype.card (W × Fin M) * (3 * n)))⁻¹ *
        ((1 + ‖polarOp J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) y‖) ^
          (Fintype.card (W × Fin M) * (3 * n)))⁻¹) ≤
      ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) *
        (C3 * ∏ k : W × Fin M, (C4 * (detW (b k.1 : Matrix (Fin n) (Fin n) ℂ))⁻¹))) := by
    calc _ ≤ ∫⁻ y : TupV W n M, ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M)) *
            ∏ k, ENNReal.ofReal (((1 + ‖y k‖) ^ (3 * n))⁻¹ *
              ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose (y k)‖) ^
                (3 * n))⁻¹) := lintegral_mono hpt
      _ = ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M)) *
            ∫⁻ y : TupV W n M, ∏ k, ENNReal.ofReal (((1 + ‖y k‖) ^ (3 * n))⁻¹ *
              ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose (y k)‖) ^
                (3 * n))⁻¹) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M)) *
            (ENNReal.ofReal C3 * ∏ k : W × Fin M, ∫⁻ z : EuclideanSpace ℂ (Fin n),
              ENNReal.ofReal (((1 + ‖z‖) ^ (3 * n))⁻¹ *
                ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose z‖) ^
                  (3 * n))⁻¹)) := by
          gcongr
          exact hprod (fun k z => ENNReal.ofReal (((1 + ‖z‖) ^ (3 * n))⁻¹ *
            ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose z‖) ^
              (3 * n))⁻¹)) hhm
      _ ≤ ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M)) *
            (ENNReal.ofReal C3 * ∏ k : W × Fin M,
              ENNReal.ofReal (C4 * (detW (b k.1 : Matrix (Fin n) (Fin n) ℂ))⁻¹)) := by
          gcongr with k
          exact hkv k
      _ = _ := by
          rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => hP0 k), ← ENNReal.ofReal_mul hC3,
            ← ENNReal.ofReal_mul hA0]
  have hP : ∏ k : W × Fin M, (C4 * (detW (b k.1 : Matrix (Fin n) (Fin n) ℂ))⁻¹) =
      C4 ^ Fintype.card (W × Fin M) *
        (∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2)) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      sq_prod_rpow M (fun w => detW (b w : Matrix (Fin n) (Fin n) ℂ)) hd, Fintype.prod_prod_type]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hQ : 0 ≤ ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2) :=
    Finset.prod_nonneg fun w _ => Real.rpow_nonneg (hd w).le _
  have hw := hweyl (fun x => phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) (tupCoord x))
    (polarOp J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)))
    (continuous_phase J _) (phase_polar W n M J hJ _ hB)
  have hsqE := hw.trans (mul_le_mul' le_rfl hint)
  rw [← ENNReal.ofReal_mul hC1, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC1 (mul_nonneg hA0
    (mul_nonneg hC3 (Finset.prod_nonneg fun k _ => hP0 k)))), hP] at hsqE
  have hsq : ‖∫ x, g x * Complex.exp (2 * Real.pi * Complex.I *
        ((phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) (tupCoord x) : ℝ) : ℂ))‖ ^ 2 ≤
      (C1 * (C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) * C3 * C4 ^ Fintype.card (W × Fin M)) *
        (∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2)) ^ 2 := by
    refine hsqE.trans (le_of_eq ?_)
    ring
  rw [hcore, norm_mul, Complex.norm_of_nonneg hc0, mul_assoc c]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  calc _ = |‖∫ x, g x * Complex.exp (2 * Real.pi * Complex.I *
        ((phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) (tupCoord x) : ℝ) : ℂ))‖| :=
        (abs_norm _).symm
    _ ≤ Real.sqrt ((C1 * (C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) * C3 *
          C4 ^ Fintype.card (W × Fin M)) *
        (∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2)) ^ 2) := Real.abs_le_sqrt hsq
    _ = _ := by rw [Real.sqrt_mul hK0, Real.sqrt_sq hQ]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound
end
end

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_orbital_integral_hua_bound : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ), (∀ w, (J w).IsHermitian) → (∀ w, (J w).det ≠ 0) →
  ∀ (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  ∃ C : ℝ, ∀ b : W → hermC n, ‖coreC J μ (fun X => f (e X)) b‖ ≤
    C * ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound
end
