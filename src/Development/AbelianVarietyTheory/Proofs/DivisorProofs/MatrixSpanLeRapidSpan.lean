import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
import BuildAid.ForwardExisting

section
section
noncomputable section

open Classical MeasureTheory NumberField

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

theorem isRapidInf_colU : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (r : ℕ)
    (f : SchwartzMap (Fin a → GlobalTheory.CuspRep.Cinf E) ℂ),
    GlobalTheory.JSW.IsRapidInf (volume : Measure (Fin a → GlobalTheory.CuspRep.Cinf E)) (fun x => f x) (GlobalTheory.JSW.colU r) := by
  intro E _ _ _ a r f
  haveI : (volume : Measure (Fin a → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hc : Continuous fun x : Fin a → Cinf E => toL (colU r x).val := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun x : Fin a → Cinf E =>
      (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)
    split_ifs
    · exact continuous_const.add (continuous_apply i)
    · exact continuous_const.add continuous_const
  have hci : Continuous fun x : Fin a → Cinf E => toL ((colU r x)⁻¹).val := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun x : Fin a → Cinf E =>
      (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j - (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)
    split_ifs
    · exact continuous_const.sub (continuous_apply i)
    · exact continuous_const.sub continuous_const
  set c₁ : ℝ := ‖(1 : Cinf E)‖
  have hent : ∀ (s : Cinf E) (x : Fin a → Cinf E), ‖s‖ ≤ 1 →
      ‖toL ((1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then s * x i else 0))‖ ≤ c₁ + ‖x‖ := by
    intro s x hs
    refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
    change ‖(1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then s * x i else 0)‖ ≤ _
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Matrix.one_apply]; split_ifs
      · exact le_rfl
      · simp [c₁]
    · split_ifs
      · exact (norm_mul_le _ _).trans ((mul_le_mul hs (norm_le_pi_norm x i) (norm_nonneg _) zero_le_one).trans (by simp))
      · simp
  have hH : ∀ x : Fin a → Cinf E, height (colU r x) ≤ (1 + 2 * c₁) + 2 * ‖x‖ := by
    intro x
    have e1 : (colU r x).val = (1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (1 : Cinf E) * x i else 0) := by
      simp [colU]
    have e2 : ((colU r x)⁻¹).val = (1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (-1 : Cinf E) * x i else 0) := by
      change 1 - _ = _
      rw [sub_eq_add_neg]
      congr 1
      ext i j w
      simp only [Matrix.neg_apply, Matrix.of_apply]
      split_ifs <;> simp
    have n1 : ‖(-1 : Cinf E)‖ ≤ 1 := by
      rw [norm_neg]; exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    have n0 : ‖(1 : Cinf E)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    unfold height
    rw [e1, e2]
    linarith [hent 1 x n0, hent (-1) x n1]
  refine ⟨f.continuous.measurable, ?_, fun N => ?_⟩
  · refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable
  · set A : ℝ := 1 + 2 * c₁
    have hA : 0 ≤ A := by positivity
    have hdom : Integrable fun x : Fin a → Cinf E => (A + 2 * ‖x‖) ^ N * ‖f x‖ := by
      have e : (fun x : Fin a → Cinf E => (A + 2 * ‖x‖) ^ N * ‖f x‖) = fun x =>
          ∑ m ∈ Finset.range (N + 1), (2 ^ m * A ^ (N - m) * (N.choose m : ℝ)) * (‖x‖ ^ m * ‖f x‖) := by
        funext x
        rw [add_comm, add_pow, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [mul_pow]; ring
      rw [e]
      exact integrable_finset_sum _ fun m _ => (f.integrable_pow_mul volume m).const_mul _
    have hht : Continuous fun x : Fin a → Cinf E => height (colU r x) := by
      unfold height
      exact (continuous_const.add hc.norm).add hci.norm
    refine Integrable.mono' hdom ((f.continuous.norm.mul (hht.pow N)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : 1 ≤ height (colU r x) := one_le_height _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (hH x) N) (norm_nonneg _)

end GlobalTheory.JSW
end
end

open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_rapid_decay_column : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (r : ℕ) (f : SchwartzMap (Fin a → GlobalTheory.CuspRep.Cinf E) ℂ), GlobalTheory.JSW.IsRapidInf (volume : Measure (Fin a → GlobalTheory.CuspRep.Cinf E)) (fun x => f x) (GlobalTheory.JSW.colU r) := by
  atlas_forward_decl GlobalTheory.JSW.isRapidInf_colU
end

section
section
noncomputable section

open Classical MeasureTheory NumberField Topology

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def unitOrOne (x : Lie E a) : GL (Fin a) (Cinf E) :=
  if h : IsUnit (Matrix.of x) then h.unit else 1

theorem unitOrOne_val (x : Lie E a) :
    (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E)) = (invSet E a).piecewise (fun y => Matrix.of y) (fun _ => 1) x := by
  by_cases hx : x ∈ invSet E a
  · rw [Set.piecewise_eq_of_mem _ _ _ hx, unitOrOne, dif_pos (show IsUnit (Matrix.of x) from hx)]; rfl
  · rw [Set.piecewise_eq_of_notMem _ _ _ hx, unitOrOne, dif_neg (show ¬ IsUnit (Matrix.of x) from hx)]; rfl

theorem measurable_unitOrOne : Measurable fun x : Lie E a => (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E)) := by
  have e : (fun x : Lie E a => (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E))) =
      (invSet E a).piecewise (fun y => Matrix.of y) (fun _ => 1) := funext unitOrOne_val
  rw [e]
  exact Measurable.piecewise isOpen_invSet.measurableSet measurable_id measurable_const

theorem continuousAt_height_unitOrOne {x : Lie E a} (hx : x ∈ invSet E a) :
    ContinuousAt (fun y : Lie E a => height (unitOrOne y)) x := by
  have hev : (fun y : Lie E a => height (unitOrOne y)) =ᶠ[𝓝 x]
      fun y => 1 + ‖y‖ + ‖toL ((Matrix.of y)⁻¹)‖ := by
    filter_upwards [isOpen_invSet.mem_nhds hx] with y hy
    have h1 : ((unitOrOne y : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = Matrix.of y := by
      rw [unitOrOne, dif_pos (show IsUnit (Matrix.of y) from hy)]; rfl
    have h2 : (((unitOrOne y)⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = (Matrix.of y)⁻¹ := by
      rw [Matrix.coe_units_inv, h1]
    simp only [height, h1, h2]
    rfl
  refine ContinuousAt.congr ?_ hev.symm
  have hinv : ContinuousAt (fun y : Matrix (Fin a) (Fin a) (Cinf E) => y⁻¹) (Matrix.of x) := by
    refine continuousAt_matrix_inv _ ?_
    have hu : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
    rw [← hu.unit_spec]
    exact NormedRing.inverse_continuousAt hu.unit
  exact (continuousAt_const.add continuousAt_id.norm).add (hinv.comp (f := fun y : Lie E a => Matrix.of y)
    continuousAt_id).norm

theorem IsTestInf.isRapidInf {f : Lie E a → ℂ} (hf : IsTestInf f) :
    IsRapidInf (volume : Measure (Lie E a)) f unitOrOne := by
  refine ⟨hf.1.continuous.measurable, measurable_unitOrOne, fun N => ?_⟩
  have hc : Continuous fun x => ‖f x‖ * height (unitOrOne x) ^ N := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ tsupport f
    · exact hf.1.continuous.continuousAt.norm.mul ((continuousAt_height_unitOrOne (hf.2.2 hx)).pow N)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
  have hs : HasCompactSupport fun x => ‖f x‖ * height (unitOrOne x) ^ N :=
    hf.2.1.norm.mul_right
  exact hc.integrable_of_hasCompactSupport hs

theorem isRapidInf_and_smoothInf_eq_kerInf :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (f : Lie E a → ℂ), IsTestInf f →
      IsRapidInf (volume : Measure (Lie E a)) f (fun x : Lie E a =>
        if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (Cinf E))) ∧
      ∀ F : GA E a → ℂ, smoothInf f F = kerInf (volume : Measure (Lie E a)) f (fun x : Lie E a =>
        if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (Cinf E))) F := by
  intro E _ _ _ a f hf
  refine ⟨hf.isRapidInf, fun F => funext fun g => ?_⟩
  simp only [smoothInf, kerInf]
  congr 1
  funext x
  by_cases hx : IsUnit (Matrix.of x)
  · rw [chart, dif_pos hx, dif_pos hx]
  · have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hf.2.2 h)
    simp [h0]

end GlobalTheory.JSW
end
end

open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_smooth_kernel_representation : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (f : GlobalTheory.CuspRep.Lie E a → ℂ), GlobalTheory.JSW.IsTestInf f → GlobalTheory.JSW.IsRapidInf (volume : Measure (GlobalTheory.CuspRep.Lie E a)) f (fun x : GlobalTheory.CuspRep.Lie E a => if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (GlobalTheory.CuspRep.Cinf E))) ∧ ∀ F : GlobalTheory.CuspRep.GA E a → ℂ, GlobalTheory.JSW.smoothInf f F = GlobalTheory.JSW.kerInf (volume : Measure (GlobalTheory.CuspRep.Lie E a)) f (fun x : GlobalTheory.CuspRep.Lie E a => if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (GlobalTheory.CuspRep.Cinf E))) F := by
  atlas_forward_decl GlobalTheory.JSW.isRapidInf_and_smoothInf_eq_kerInf
end

section
section
open Classical MeasureTheory NumberField

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

theorem mspan_le_rspan : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π : GlobalTheory.CuspRep.CuspSub E a), GlobalTheory.JSW.mspan π ≤ GlobalTheory.JSW.rspan π := by
  intro E _ _ _ a π
  refine sInf_le ⟨fun φ hφ => mem_rspan hφ, fun F hF h => rt_mem_rspan hF h, fun F hF f hf => ?_,
    fun F hF r f => ?_⟩
  · obtain ⟨hk, he⟩ := GlobalTheory.T.archimedean_smooth_kernel_representation f hf
    rw [he F]
    exact kerInf_mem_rspan hF _ hk
  · have e : colConv r f F = kerInf (volume : Measure (Fin a → Cinf E)) (fun x => f x) (colU r) F := rfl
    rw [e]
    exact kerInf_mem_rspan hF _ (GlobalTheory.T.schwartz_rapid_decay_column r f)

end GlobalTheory.JSW
end

open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_span_le_rapid_span : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : GlobalTheory.CuspRep.CuspSub E a), GlobalTheory.JSW.mspan π ≤ GlobalTheory.JSW.rspan π := by
  atlas_forward_decl GlobalTheory.JSW.mspan_le_rspan
end
