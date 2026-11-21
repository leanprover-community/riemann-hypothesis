import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCosSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StereographicMeasureChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MobiusChangeOfVariables
import BuildAid.ForwardExisting

section
section
set_option autoImplicit false

open MeasureTheory
open scoped ComplexOrder ENNReal

noncomputable section

namespace GlobalTheory.LineCos.FsLaw

open GlobalTheory.LineCos

theorem re_det_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) : 0 < G.det.re :=
  (Complex.pos_iff.1 hG.det_pos).1

theorem corner_eq {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) : G 0 0 = ((G 0 0).re : ℂ) := by
  have h := hG.isHermitian.apply 0 0
  exact (Complex.conj_eq_iff_re.1 h).symm

theorem hform_single (G : Matrix (Fin 2) (Fin 2) ℂ) (w : Fin 2 → ℂ) :
    hform G w (Pi.single 0 1) = w 0 * G 0 0 + w 1 * G 1 0 := by
  simp [hform, Fin.sum_univ_two]

theorem re_hform_mul {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (w : Fin 2 → ℂ) :
    (hform G w w).re * (G 0 0).re = ‖w 0 * G 0 0 + w 1 * G 1 0‖ ^ 2 + G.det.re * ‖w 1‖ ^ 2 := by
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.1 (hG.isHermitian.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.1 (hG.isHermitian.apply 1 1)
  have h01 : G 0 1 = starRingEnd ℂ (G 1 0) := (hG.isHermitian.apply 0 1).symm
  simp only [hform, Fin.sum_univ_two, Matrix.det_fin_two, h01, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.conj_re, Complex.conj_im,
    h00, h11]
  ring

theorem measurable_lineVec (s : Bool) (i : Fin 2) : Measurable fun x : ℂ => lineVec s x i := by
  cases s
  · fin_cases i
    · exact measurable_const
    · exact measurable_id
  · fin_cases i
    · exact measurable_id
    · exact measurable_const

theorem measurable_hform (G : Matrix (Fin 2) (Fin 2) ℂ) {a b : ℂ → Fin 2 → ℂ} (ha : ∀ i, Measurable fun x => a x i)
    (hb : ∀ i, Measurable fun x => b x i) : Measurable fun x => hform G (a x) (b x) := by
  unfold hform
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact ((ha i).mul (Complex.continuous_conj.measurable.comp (hb j))).mul_const _

theorem measurable_cosSq (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) : Measurable (cosSq s G) := by
  have h1 : Measurable fun x : ℂ => hform G (lineVec s x) (Pi.single (0 : Fin 2) (1 : ℂ)) :=
    measurable_hform G (b := fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) (measurable_lineVec s) fun _ => measurable_const
  have h2 : Measurable fun x : ℂ => (hform G (lineVec s x) (lineVec s x)).re :=
    Complex.measurable_re.comp (measurable_hform G (measurable_lineVec s) (measurable_lineVec s))
  exact (h1.norm.pow_const 2).div (h2.mul_const _)

theorem lintegral_reflect (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, g (1 - t) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo,
    ← lintegral_sub_left_eq_self ((Set.Ioo (0 : ℝ) 1).indicator g) 1]
  congr 1
  funext t
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · have : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [Set.indicator_of_mem ht, Set.indicator_of_mem this]
  · have : 1 - t ∉ Set.Ioo (0 : ℝ) 1 := fun h => ht ⟨by linarith [h.2], by linarith [h.1]⟩
    simp only [Set.indicator_of_notMem ht, Set.indicator_of_notMem this]

theorem lintegral_false {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, ENNReal.ofReal (G.det.re / (Real.pi * (hform G (lineVec false x) (lineVec false x)).re ^ 2)) *
      g (cosSq false G x) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have ha : 0 < a := re_corner_pos hG
  have hD : 0 < D := re_det_pos hG
  have hG0 : G 0 0 = (a : ℂ) := corner_eq hG
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hc : ((Real.sqrt D / a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (div_pos (Real.sqrt_pos.2 hD) ha).ne'
  have hH : Measurable fun x : ℂ =>
      g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) := by
    have : Measurable fun x : ℂ => g (1 / (1 + ‖x‖ ^ 2)) := hg.comp (by fun_prop)
    fun_prop
  rw [← GlobalTheory.FibLine.lintegral_comp_fsDens g hg,
    ← GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius (G 1 0 / a) _ hc _ hH]
  refine lintegral_congr_ae ?_
  filter_upwards [GlobalTheory.FibLine.UnitaryInv.ae_affine_ne 1 (G 1 0 / a) (Or.inl one_ne_zero)] with x hx
  have hsq := re_hform_mul hG (lineVec false x)
  have hone := hform_single G (lineVec false x)
  have hw0 : lineVec false x 0 = 1 := rfl
  have hw1 : lineVec false x 1 = x := rfl
  have hp : 1 * G 0 0 + x * G 1 0 = a * (1 + G 1 0 / a * x) := by
    rw [hG0]; field_simp
  rw [hw0, hw1, hp] at hsq hone
  set q : ℝ := ‖1 + G 1 0 / a * x‖ with hq_def
  have hq : 0 < q := norm_pos_iff.2 hx
  have hn : ‖(a : ℂ) * (1 + G 1 0 / a * x)‖ = a * q := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hcn : ‖((Real.sqrt D / a : ℝ) : ℂ)‖ ^ 2 = D / a ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hD.le]
  have hy : ‖((Real.sqrt D / a : ℝ) : ℂ) * x / (1 + G 1 0 / a * x)‖ ^ 2 = D / a ^ 2 * ‖x‖ ^ 2 / q ^ 2 := by
    rw [norm_div, norm_mul, div_pow, mul_pow, hcn]
  have hj : ‖((Real.sqrt D / a : ℝ) : ℂ) / (1 + G 1 0 / a * x) ^ 2‖ ^ 2 = D / a ^ 2 / q ^ 4 := by
    rw [norm_div, norm_pow, div_pow, hcn, ← pow_mul]
  rw [hn, ← ha_def, ← hD_def] at hsq
  have hh : (hform G (lineVec false x) (lineVec false x)).re = ((a * q) ^ 2 + D * ‖x‖ ^ 2) / a :=
    eq_div_of_mul_eq ha.ne' hsq
  have hcos : cosSq false G x = 1 / (1 + D / a ^ 2 * ‖x‖ ^ 2 / q ^ 2) := by
    unfold cosSq
    rw [hone, hn, ← ha_def, hsq]
    field_simp
  have hpi := Real.pi_pos
  rw [hy, hj, hcos, hh, mul_left_comm, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

theorem lintegral_true {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, ENNReal.ofReal (G.det.re / (Real.pi * (hform G (lineVec true x) (lineVec true x)).re ^ 2)) *
      g (cosSq true G x) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have ha : 0 < a := re_corner_pos hG
  have hD : 0 < D := re_det_pos hG
  have hG0 : G 0 0 = (a : ℂ) := corner_eq hG
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hc : ((a / Real.sqrt D : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (div_pos ha (Real.sqrt_pos.2 hD)).ne'
  have hg' : Measurable fun t : ℝ => g (1 - t) := hg.comp (by fun_prop)
  have hH : Measurable fun x : ℂ =>
      g (1 - 1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) := by
    have : Measurable fun x : ℂ => g (1 - 1 / (1 + ‖x‖ ^ 2)) := hg.comp (by fun_prop)
    fun_prop
  rw [← lintegral_reflect, ← GlobalTheory.FibLine.lintegral_comp_fsDens _ hg',
    ← GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius 0 _ hc _ hH,
    ← lintegral_sub_right_eq_self _ (G 1 0 / a)]
  refine lintegral_congr fun x => ?_
  have hsq := re_hform_mul hG (lineVec true (x - G 1 0 / a))
  have hone := hform_single G (lineVec true (x - G 1 0 / a))
  have hw0 : lineVec true (x - G 1 0 / a) 0 = x - G 1 0 / a := rfl
  have hw1 : lineVec true (x - G 1 0 / a) 1 = 1 := rfl
  have hp : (x - G 1 0 / a) * G 0 0 + 1 * G 1 0 = a * x := by
    rw [hG0]; field_simp; ring
  rw [hw0, hw1, hp] at hsq hone
  have hn : ‖(a : ℂ) * x‖ = a * ‖x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hcn : ‖((a / Real.sqrt D : ℝ) : ℂ)‖ ^ 2 = a ^ 2 / D := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hD.le]
  have hy : ‖((a / Real.sqrt D : ℝ) : ℂ) * x / (1 + 0 * x)‖ ^ 2 = a ^ 2 / D * ‖x‖ ^ 2 := by
    rw [zero_mul, add_zero, div_one, norm_mul, mul_pow, hcn]
  have hj : ‖((a / Real.sqrt D : ℝ) : ℂ) / (1 + 0 * x) ^ 2‖ ^ 2 = a ^ 2 / D := by
    rw [zero_mul, add_zero, one_pow, div_one, hcn]
  rw [hn, ← ha_def, ← hD_def, norm_one, one_pow, mul_one] at hsq
  have hh : (hform G (lineVec true (x - G 1 0 / a)) (lineVec true (x - G 1 0 / a))).re = ((a * ‖x‖) ^ 2 + D) / a :=
    eq_div_of_mul_eq ha.ne' hsq
  have hcos : cosSq true G (x - G 1 0 / a) = 1 - 1 / (1 + a ^ 2 / D * ‖x‖ ^ 2) := by
    unfold cosSq
    rw [hone, hn, ← ha_def, hsq]
    field_simp
    ring
  have hpi := Real.pi_pos
  rw [hy, hj, hcos, hh, mul_left_comm, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp
  ring

theorem map_cosSq_fs (G : Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (hG : G.PosDef) :
    Measure.map (cosSq s G)
        (volume.withDensity fun x : ℂ => ENNReal.ofReal (G.det.re /
          (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2))) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hd : Measurable fun x : ℂ => ENNReal.ofReal (G.det.re /
      (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2)) := by
    have := Complex.measurable_re.comp (measurable_hform G (measurable_lineVec s) (measurable_lineVec s))
    exact (measurable_const.div ((this.pow_const 2).const_mul _)).ennreal_ofReal
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg (measurable_cosSq s G),
    lintegral_withDensity_eq_lintegral_mul _ hd (g := fun x => g (cosSq s G x)) (hg.comp (measurable_cosSq s G)),
    ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  cases s
  · exact lintegral_false hG g hg
  · exact lintegral_true hG g hg

end GlobalTheory.LineCos.FsLaw
end
end

open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosine_square_pushforward_uniform : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ) (s : Bool), G.PosDef →
    Measure.map (GlobalTheory.LineCos.cosSq s G)
        (volume.withDensity fun x : ℂ => ENNReal.ofReal (G.det.re /
          (Real.pi * (GlobalTheory.LineCos.hform G (GlobalTheory.LineCos.lineVec s x) (GlobalTheory.LineCos.lineVec s x)).re ^ 2))) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  atlas_forward_decl GlobalTheory.LineCos.FsLaw.map_cosSq_fs
end

section
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder

namespace GlobalTheory.LineCos

def splitLin (d : ℕ) : V (d + 1) ≃ₗ[ℝ] (Fin d → ℂ) × ℂ where
  toFun z := (base z, fib z)
  invFun p := WithLp.toLp 2 (Fin.snoc p.1 p.2 : Fin (d + 1) → ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [fib]
    · simp [base]
  right_inv p := by
    ext i
    · simp [base]
    · simp [fib]

theorem exists_lintegral_le_iterated (d : ℕ) : ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : V (d + 1) → ENNReal,
    ∫⁻ z, F z ≤ c * ∫⁻ b : Fin d → ℂ, ∫⁻ x : ℂ, F ((splitLin d).symm (b, x)) := by
  let e : V (d + 1) ≃L[ℝ] (Fin d → ℂ) × ℂ := (splitLin d).toContinuousLinearEquiv
  let em : V (d + 1) ≃ᵐ (Fin d → ℂ) × ℂ := e.toHomeomorph.toMeasurableEquiv
  haveI : Measure.IsAddHaarMeasure (Measure.map e (volume : Measure (V (d + 1)))) := inferInstance
  haveI : Measure.IsAddHaarMeasure (volume : Measure ((Fin d → ℂ) × ℂ)) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin d → ℂ)) (volume : Measure ℂ)
  have h := Measure.isAddLeftInvariant_eq_smul (Measure.map e (volume : Measure (V (d + 1))))
    (volume : Measure ((Fin d → ℂ) × ℂ))
  refine ⟨Measure.addHaarScalarFactor (Measure.map e (volume : Measure (V (d + 1))))
    (volume : Measure ((Fin d → ℂ) × ℂ)), ENNReal.coe_ne_top, fun F => ?_⟩
  have h1 : ∫⁻ z, F z = ∫⁻ p, F (e.symm p) ∂(Measure.map e (volume : Measure (V (d + 1)))) := by
    have := lintegral_map_equiv (μ := (volume : Measure (V (d + 1)))) (fun p => F (e.symm p)) em
    simpa [em] using this.symm
  rw [h1]
  conv_lhs => rw [h]
  rw [lintegral_smul_measure]
  refine mul_le_mul_right ?_ _
  exact lintegral_prod_le (μ := (volume : Measure (Fin d → ℂ))) (ν := (volume : Measure ℂ)) (fun p => F (e.symm p))

def fsDensity (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  G.det.re / (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2)

theorem fsDensity_pos (s : Bool) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) : 0 < fsDensity s G x :=
  div_pos (Complex.pos_iff.1 hG.det_pos).1
    (mul_pos Real.pi_pos (pow_pos (re_hform_pos hG (lineVec_ne_zero s x)) 2))

theorem continuousOn_fsDensity {d : ℕ} {O : Set (V (d + 1))} {G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ} (s : Bool)
    (hc : ContinuousOn (fun z => G (base z)) O) (hp : ∀ z ∈ O, (G (base z)).PosDef) :
    ContinuousOn (fun z => fsDensity s (G (base z)) (fib z)) O := by
  have he : ∀ i j, ContinuousOn (fun z => G (base z) i j) O := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)
  have hx : Continuous (fun z : V (d + 1) => fib z) := by
    unfold fib
    fun_prop
  have hw : ∀ i, Continuous (fun z : V (d + 1) => lineVec s (fib z) i) := fun i => by
    cases s
    · fin_cases i
      · exact continuous_const
      · exact hx
    · fin_cases i
      · exact hx
      · exact continuous_const
  have hh : ContinuousOn (fun z => hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))) O := by
    unfold hform
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    exact (((hw i).mul ((Complex.continuous_conj).comp (hw j))).continuousOn).mul (he i j)
  have hdet : ContinuousOn (fun z => (G (base z)).det) O :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hc
  refine (Complex.continuous_re.comp_continuousOn hdet).div
    (continuousOn_const.mul ((Complex.continuous_re.comp_continuousOn hh).pow 2)) fun z hz => ?_
  exact (mul_pos Real.pi_pos (pow_pos (re_hform_pos (hp z hz) (lineVec_ne_zero s _)) 2)).ne'

theorem measurable_cosSq (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) : Measurable (cosSq s G) := by
  have hw : ∀ i, Continuous (fun x : ℂ => lineVec s x i) := fun i => by
    cases s
    · fin_cases i
      · exact continuous_const
      · exact continuous_id
    · fin_cases i
      · exact continuous_id
      · exact continuous_const
  have hh : ∀ (b : ℂ → Fin 2 → ℂ), (∀ j, Continuous fun z => b z j) →
      Continuous (fun z => hform G (lineVec s z) (b z)) := fun b hb => by
    unfold hform
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hw i).mul ((Complex.continuous_conj).comp (hb j))).mul continuous_const
  exact ((hh (fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) fun j => continuous_const).norm.pow 2).measurable.div
    ((Complex.continuous_re.comp (hh _ hw)).mul continuous_const).measurable

theorem lintegral_fsDensity_indicator (s : Bool) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫⁻ x, (cosSq s G ⁻¹' A).indicator (fun x => ENNReal.ofReal (fsDensity s G x)) x =
      volume.restrict (Icc (0 : ℝ) 1) A := by
  rw [← GlobalTheory.T.cosine_square_pushforward_uniform G s hG, Measure.map_apply (measurable_cosSq s G) hA,
    withDensity_apply _ (measurable_cosSq s G hA), lintegral_indicator (measurable_cosSq s G hA)]
  rfl

theorem exists_map_cosSq_le (d : ℕ) (T : Set (V (d + 1))) (ρ : V (d + 1) → ℝ)
    (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (z₀ : V (d + 1))
    (hT : IsOpen T) (hz₀ : z₀ ∈ T) (hρ : ContinuousOn ρ T) (hG : ContinuousOn (fun z => G (base z)) T)
    (hp : ∀ z ∈ T, (G (base z)).PosDef) :
    ∃ N : Set (V (d + 1)), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ T ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map (fun z => cosSq s (G (base z)) (fib z))
          ((volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)) ≤
        C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨c, hc, hF⟩ := exists_lintegral_le_iterated d
  have hfs := continuousOn_fsDensity s hG hp
  have h0 := fsDensity_pos s (hp z₀ hz₀) (fib z₀)
  set R : ℝ := (|ρ z₀| + 1) / fsDensity s (G (base z₀)) (fib z₀) with hR
  have hR0 : 0 ≤ R := by positivity
  have hb : Continuous (fun z : V (d + 1) => base z) := by
    unfold base
    fun_prop
  let K : Set (Fin d → ℂ) := Metric.ball (base z₀) 1
  let N : Set (V (d + 1)) := (T ∩ (fun z => R * fsDensity s (G (base z)) (fib z) - ρ z) ⁻¹' Ioi 0) ∩
    (fun z => base z) ⁻¹' K
  have hN : IsOpen N :=
    (((continuousOn_const.mul hfs).sub hρ).isOpen_inter_preimage hT isOpen_Ioi).inter
      (Metric.isOpen_ball.preimage hb)
  have hNT : N ⊆ T := fun z hz => hz.1.1
  refine ⟨N, hN, ⟨⟨hz₀, ?_⟩, Metric.mem_ball_self one_pos⟩, hNT, c * (ENNReal.ofReal R * volume K),
    ENNReal.mul_ne_top hc (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne), ?_⟩
  · show 0 < R * fsDensity s (G (base z₀)) (fib z₀) - ρ z₀
    rw [hR, div_mul_cancel₀ _ h0.ne']
    linarith [le_abs_self (ρ z₀)]
  set f : V (d + 1) → ℝ := fun z => cosSq s (G (base z)) (fib z) with hf
  have hf' : Measurable (N.piecewise f 0) :=
    ((continuousOn_cosSq s hG hp).mono hNT).measurable_piecewise continuousOn_const hN.measurableSet
  have hae : f =ᵐ[(volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)] N.piecewise f 0 := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [ae_restrict_mem hN.measurableSet] with z hz
    rw [Set.piecewise_eq_of_mem _ _ _ hz]
  rw [Measure.map_congr hae, Measure.le_iff]
  intro A hA
  rw [Measure.map_apply hf' hA, withDensity_apply _ (hf' hA), Measure.restrict_restrict (hf' hA),
    ← lintegral_indicator ((hf' hA).inter hN.measurableSet), Measure.smul_apply, smul_eq_mul]
  refine (hF _).trans ?_
  rw [mul_assoc c]
  refine mul_le_mul_right ?_ _
  have key : ∀ b : Fin d → ℂ, ∫⁻ x : ℂ, (N.piecewise f 0 ⁻¹' A ∩ N).indicator (fun z => ENNReal.ofReal (ρ z))
      ((splitLin d).symm (b, x)) ≤
      K.indicator (fun _ => ENNReal.ofReal R * volume.restrict (Icc (0 : ℝ) 1) A) b := by
    intro b
    have hbase : ∀ x, base ((splitLin d).symm (b, x)) = b := fun x =>
      congrArg Prod.fst ((splitLin d).apply_symm_apply (b, x))
    have hfib : ∀ x, fib ((splitLin d).symm (b, x)) = x := fun x =>
      congrArg Prod.snd ((splitLin d).apply_symm_apply (b, x))
    by_cases hex : ∃ x, (splitLin d).symm (b, x) ∈ N
    · obtain ⟨x₀, hx₀⟩ := hex
      have hbK : b ∈ K := by
        have := hx₀.2
        rwa [mem_preimage, hbase] at this
      have hGb : (G b).PosDef := by
        have := hp _ (hNT hx₀)
        rwa [hbase] at this
      rw [indicator_of_mem hbK, ← lintegral_fsDensity_indicator s hGb hA,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      by_cases hx : (splitLin d).symm (b, x) ∈ N.piecewise f 0 ⁻¹' A ∩ N
      · have h1 : x ∈ cosSq s (G b) ⁻¹' A := by
          have := hx.1
          rw [mem_preimage, Set.piecewise_eq_of_mem _ _ _ hx.2, hf] at this
          simpa only [hbase, hfib, mem_preimage] using this
        have h2 : 0 < R * fsDensity s (G b) x - ρ ((splitLin d).symm (b, x)) := by
          have := hx.2.1.2
          simpa only [mem_preimage, hbase, hfib, mem_Ioi] using this
        simp only [indicator_of_mem hx, indicator_of_mem h1]
        rw [← ENNReal.ofReal_mul hR0]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · simp only [indicator_of_notMem hx]
        exact zero_le
    · have : ∀ x : ℂ, (N.piecewise f 0 ⁻¹' A ∩ N).indicator (fun z => ENNReal.ofReal (ρ z))
          ((splitLin d).symm (b, x)) = 0 := fun x => indicator_of_notMem (fun h => hex ⟨x, h.2⟩) _
      simp only [this, lintegral_zero]
      exact zero_le
  refine (lintegral_mono key).trans (le_of_eq ?_)
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const]
  ring

end GlobalTheory.LineCos
end
end

open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_bound_near_point : ∀ (d : ℕ) (T : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1))) (ρ : ReciprocityTheory.L2DbarEstimates.V (d + 1) → ℝ)
    (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (z₀ : ReciprocityTheory.L2DbarEstimates.V (d + 1)),
    IsOpen T → z₀ ∈ T → ContinuousOn ρ T → ContinuousOn (fun z => G (GlobalTheory.LineCos.base z)) T →
    (∀ z ∈ T, (G (GlobalTheory.LineCos.base z)).PosDef) →
    ∃ N : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1)), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ T ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map (fun z => GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z))
          ((volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)) ≤
        C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  atlas_forward_decl GlobalTheory.LineCos.exists_map_cosSq_le
end
