import ReciprocityTheory.L2DbarEstimates.LeviForms.TwBound
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bergman
import ReciprocityTheory.L2DbarEstimates.LeviForms.EvLevi
import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
import ReciprocityTheory.L2DbarEstimates.LeviForms.TwistLevi
import ReciprocityTheory.L2DbarEstimates.LeviForms.ShellBound
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.LeviForms.ApplyTw
import ReciprocityTheory.L2DbarEstimates.LeviForms.FxExpNegWgtLeShell
import ReciprocityTheory.L2DbarEstimates.LeviForms.Ot0
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetMonoDetOneAdd
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq

section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

noncomputable section

def llShift (c t : ℝ) : ℝ :=
  Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) * (t + c) +
    (1 - Real.smoothTransition ((t + 3 * c / 4) / (c / 4)))







def llLog (c t : ℝ) : ℝ := Real.log (llShift c t)





end

end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff


end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem basic_exp_bound (x : ℝ) (hx : 1 ≤ x) :
    (x + 1) ^ 2 + (x + Real.log x) ≤ 2 * Real.exp x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have h4 := Real.sum_le_exp_of_nonneg hx0 4
  simp [Finset.sum_range_succ, Nat.factorial] at h4
  have hl := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x)
  nlinarith [sq_nonneg (x - 7 / 5), mul_nonneg hx0 (sq_nonneg (x - 7 / 5)),
    mul_nonneg (by linarith : (0:ℝ) ≤ x - 1) (sq_nonneg (x - 7 / 5))]

theorem basic_exp_seven : Real.exp 7 ≤ 1250 := by
  have h := Real.exp_one_lt_d9
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 7 ≤ (2.7182818286 : ℝ) ^ 7 := by gcongr
    _ ≤ 1250 := by norm_num

theorem basic_real (A ε : ℝ) (hε : 0 < ε) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    let X := 1 + Real.log (1 + ε ^ 2) - Real.log (A + ε ^ 2)
    1 ≤ X ∧ 1 ≤ X + Real.log X ∧ 1 + 1 / X ≤ 2 ∧ X + Real.log X ≤ (X + 1) ^ 2 ∧
      X ≤ 1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2) ∧
      A + ε ^ 2 = (1 + ε ^ 2) * Real.exp (1 - X) := by
  intro X
  have he2 : 0 < ε ^ 2 := by positivity
  have hQ : 0 < A + ε ^ 2 := by linarith
  have hlog : Real.log (A + ε ^ 2) ≤ Real.log (1 + ε ^ 2) :=
    Real.log_le_log hQ (by linarith)
  have hX : 1 ≤ X := by simp only [X]; linarith
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlX' := Real.log_le_sub_one_of_pos hX0
  refine ⟨hX, by linarith, ?_, by nlinarith, ?_, ?_⟩
  · have : 1 / X ≤ 1 := by rw [div_le_one hX0]; exact hX
    linarith
  · have : Real.log (ε ^ 2) ≤ Real.log (A + ε ^ 2) := Real.log_le_log he2 (by linarith)
    simp only [X]; linarith
  · have h1 : (1 : ℝ) - X = Real.log (A + ε ^ 2) - Real.log (1 + ε ^ 2) := by simp only [X]; ring
    rw [h1, Real.exp_sub, Real.exp_log hQ, Real.exp_log (by positivity)]
    field_simp

theorem basic (n : ℕ) (M : Type u) : BasicStatement n M := by
  intro g ph ph2 r j ε δ hr hε hA
  have hev : ∀ x, 0 ≤ ev n g ph r x ∧ ev n g ph r x ≤ 1 := by
    intro x
    have hr2 : 0 < r ^ 2 := by positivity
    refine ⟨by unfold ev; positivity, ?_⟩
    unfold ev
    rw [div_le_one hr2]; exact hA x
  have hR : ∀ x, _ := fun x => basic_real (ev n g ph r x) ε hε (hev x).1 (hev x).2
  have hxx : ∀ x, xx n g ph r ε x =
      1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2) := fun x => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨h1, h2, h3, h4, -⟩ := hR x
    simp only [eta, kap, hxx]
    exact ⟨h1, h2, h3, h4⟩
  · refine ⟨Real.log (1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2) +
      Real.log (1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2))), fun x => ?_⟩
    obtain ⟨h1, h2, -, -, h5, -⟩ := hR x
    simp only [twist, eta, hxx]
    set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)
    set B := 1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2)
    have hl0 : 0 ≤ Real.log (X + Real.log X) := Real.log_nonneg h2
    have hlB : Real.log X ≤ Real.log B := Real.log_le_log (by linarith) h5
    have : Real.log (X + Real.log X) ≤ Real.log (B + Real.log B) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [abs_neg, abs_of_nonneg hl0]; exact this
  · intro h50 x hx
    obtain ⟨h1, h2, -, -, -, -⟩ := hR x
    simp only [eta, hxx]
    set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)
    have hlX : 0 ≤ Real.log X := Real.log_nonneg h1
    have he2 : 0 < ε ^ 2 := by positivity
    have hQ : ev n g ph r x + ε ^ 2 ≤ 2 * ε ^ 2 := by linarith
    have hQ0 : 0 < ev n g ph r x + ε ^ 2 := by linarith [(hev x).1]
    have hsm : 2 * ε ^ 2 ≤ Real.exp (-7) := by
      have hε2 : ε ^ 2 ≤ (1 / 50) ^ 2 := by gcongr
      have : (1 : ℝ) / 1250 ≤ Real.exp (-7) := by
        rw [Real.exp_neg, one_div]; exact inv_anti₀ (Real.exp_pos 7) basic_exp_seven
      nlinarith
    have hlQ : Real.log (ev n g ph r x + ε ^ 2) ≤ -7 := by
      rw [Real.log_le_iff_le_exp hQ0]; linarith
    have hl1 : 0 ≤ Real.log (1 + ε ^ 2) := Real.log_nonneg (by linarith)
    simp only [X] at hlX ⊢
    linarith
  · intro hn hδ hδε x
    obtain ⟨h1, -, -, -, -, h6⟩ := hR x
    have hD := basic_exp_bound _ h1
    simp only [eta, hxx, wgt, lw] at hD ⊢
    set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)
    set A := ev n g ph r x
    set E := Real.exp (-ph2 x - ((n : ℝ) + j) * ph x)
    set D := (X + 1) ^ 2 + (X + Real.log X)
    have hA0 : 0 ≤ A := (hev x).1
    have hAδ : 0 < A + δ ^ 2 := by positivity
    have hD0 : 0 < D := by
      have : 0 ≤ Real.log X := Real.log_nonneg h1
      positivity
    have hE : 0 < E := Real.exp_pos _
    have hexp : Real.exp (-(ph2 x + ((n : ℝ) + j) * ph x + n * Real.log (A + δ ^ 2))) =
        E / (A + δ ^ 2) ^ n := by
      rw [show -(ph2 x + ((n : ℝ) + j) * ph x + n * Real.log (A + δ ^ 2)) =
        (-ph2 x - ((n : ℝ) + j) * ph x) - n * Real.log (A + δ ^ 2) by ring, Real.exp_sub,
        ← Real.log_pow, Real.exp_log (by positivity)]
    rw [hexp]

    have hpow : (A + δ ^ 2) ^ n ≤ (1 + ε ^ 2) ^ n * Real.exp (1 - X) := by
      have hle : A + δ ^ 2 ≤ (1 + ε ^ 2) * Real.exp (1 - X) := by
        rw [← h6]; have : δ ^ 2 ≤ ε ^ 2 := by gcongr
        linarith
      calc (A + δ ^ 2) ^ n ≤ ((1 + ε ^ 2) * Real.exp (1 - X)) ^ n := by gcongr
        _ = (1 + ε ^ 2) ^ n * Real.exp (1 - X) ^ n := by rw [mul_pow]
        _ ≤ (1 + ε ^ 2) ^ n * Real.exp (1 - X) := by
          gcongr
          exact pow_le_of_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
            (by omega)
    have hkey : (A + δ ^ 2) ^ n * D ≤ 2 * Real.exp 1 * (1 + ε ^ 2) ^ n := by
      have h2 : Real.exp (1 - X) * D ≤ 2 * Real.exp 1 := by
        rw [Real.exp_sub]
        rw [div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos X)]
        nlinarith [Real.exp_pos 1]
      calc (A + δ ^ 2) ^ n * D ≤ (1 + ε ^ 2) ^ n * Real.exp (1 - X) * D := by gcongr
        _ = (1 + ε ^ 2) ^ n * (Real.exp (1 - X) * D) := by ring
        _ ≤ (1 + ε ^ 2) ^ n * (2 * Real.exp 1) := by gcongr
        _ = 2 * Real.exp 1 * (1 + ε ^ 2) ^ n := by ring
    rw [div_div, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hkey hE.le]

end ReciprocityTheory.L2DbarEstimates.I
end

section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

universe u

noncomputable section

def dualSig (s : ℝ) : ℝ := 3 / 4 + (s - 3 / 4) * Real.smoothTransition ((s - 3 / 4) * 8)

lemma dualSig_contDiff : ContDiff ℝ ∞ dualSig := by
  unfold dualSig
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).mul contDiff_const)))

lemma dualSig_ge (s : ℝ) : 3 / 4 ≤ dualSig s := by
  unfold dualSig
  rcases le_or_gt s (3 / 4) with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by nlinarith)]
    simp
  · have := Real.smoothTransition.nonneg ((s - 3 / 4) * 8)
    nlinarith

lemma dualSig_eq {s : ℝ} (hs : 7 / 8 ≤ s) : dualSig s = s := by
  unfold dualSig
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

lemma add_log_pos_of_three_quarters_le {s : ℝ} (hs : 3 / 4 ≤ s) : 0 < s + Real.log s := by
  have h0 : 0 < s := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos h0
  have h2 : s⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ h0 (by norm_num)]
    linarith
  linarith

def dualK (c t : ℝ) : ℝ := -Real.log (dualSig (c - t) + Real.log (dualSig (c - t)))

lemma dualK_contDiff (c : ℝ) : ContDiff ℝ ∞ (dualK c) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => dualSig (c - t)) :=
    dualSig_contDiff.comp (contDiff_const.sub contDiff_id)
  have hpos : ∀ t, 0 < dualSig (c - t) := fun t => by linarith [dualSig_ge (c - t)]
  have hl : ContDiff ℝ ∞ (fun t : ℝ => Real.log (dualSig (c - t))) :=
    hs.log (fun t => (hpos t).ne')
  have hsum : ContDiff ℝ ∞ (fun t : ℝ => dualSig (c - t) + Real.log (dualSig (c - t))) := hs.add hl
  have := hsum.log (fun t => (add_log_pos_of_three_quarters_le (dualSig_ge (c - t))).ne')
  exact this.neg

lemma dualK_eq {c t : ℝ} (h : 7 / 8 ≤ c - t) :
    dualK c t = -Real.log ((c - t) + Real.log (c - t)) := by
  unfold dualK
  rw [dualSig_eq h]

lemma dualK_deriv {c t : ℝ} (h : 1 ≤ c - t) :
    deriv (dualK c) t = (1 + 1 / (c - t)) / ((c - t) + Real.log (c - t)) := by
  have hev : dualK c =ᶠ[𝓝 t] fun u => -Real.log ((c - u) + Real.log (c - u)) := by
    have : ∀ᶠ u in 𝓝 t, u < t + 1 / 8 := eventually_lt_nhds (by linarith)
    filter_upwards [this] with u hu
    exact dualK_eq (by linarith)
  rw [hev.deriv_eq]
  have hs0 : c - t ≠ 0 := by linarith
  have hpos : 0 < (c - t) + Real.log (c - t) := add_log_pos_of_three_quarters_le (by linarith)
  have h1 : HasDerivAt (fun u : ℝ => c - u) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub c
  have h2 := h1.log hs0
  have h4 : HasDerivAt (fun u => -Real.log ((c - u) + Real.log (c - u)))
      (-((-1 + -1 / (c - t)) / ((c - t) + Real.log (c - t)))) t :=
    ((h1.add h2).log hpos.ne').neg
  rw [h4.deriv]
  field_simp
  ring

lemma dual_dbarDot_comp_real {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ)
    (hk : ContDiff ℝ ∞ k) (f : M → ℝ) (hf : CkR n z 1 f) (x : M) (ξ : Fin n → ℂ) :
    ‖dbarDot n z (fun y => (k (f y) : ℂ)) x ξ‖ =
      |deriv k (f x)| * ‖dDot n z (fun y => (f y : ℂ)) x ξ‖ := by
  have : dbarDot n z (fun y => (k (f y) : ℂ)) x ξ =
      ((deriv k (f x) : ℝ) : ℂ) * (starRingEnd ℂ) (dDot n z (fun y => (f y : ℂ)) x ξ) := by
    unfold dbarDot dDot
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [db_comp_real n z k hk f hf i x, db_ofReal, map_mul]
    ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]

theorem dual (n : ℕ) (M : Type u) [TopologicalSpace M]
    (hT : TwistLeviStatement n M) (hB : BasicStatement n M) : DualStatement n M := by
  intro z g ph ph2 r j ε δ hz hg hph hphL hph2 hph2L hr hj hε hδ hbd
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun x ξ => ?_, fun x ξ _ => ?_, fun x ξ _ => ?_⟩ <;> simp [dbarDot, Levi]
  obtain ⟨hB1, -, -, -⟩ := hB g ph ph2 r j ε δ hr hε hbd
  obtain ⟨-, -, hT1, hT2⟩ := hT z g ph ph2 r j ε δ hz hg hph hphL hph2 hph2L hr hj hε hδ hbd
  obtain ⟨hW, -, -, -⟩ := hT z g ph ph2 r j ε ε hz hg hph hphL hph2 hph2L hr hj hε hε hbd
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlw : SmoothR n z (lw n g ph r ε) := by
    have e : (fun y => (lw n g ph r ε y : ℂ)) = fun y => (1 / (n : ℂ)) *
        (((wgt n g ph ph2 r j ε y : ℝ) : ℂ) - (ph2 y : ℂ) - ((n : ℂ) + j) * (ph y : ℂ)) := by
      funext y
      unfold wgt
      push_cast
      field_simp
      ring
    unfold SmoothR
    rw [e]
    exact Smooth.mul _ _ _ _ (Smooth.const _ _ _)
      (Smooth.sub _ _ _ _ (Smooth.sub _ _ _ _ hW hph2) (Smooth.mul _ _ _ _ (Smooth.const _ _ _) hph))
  have hlw1 : CkR n z 1 (lw n g ph r ε) := SmoothR.ckR n z 1 _ hlw
  have hev0 : ∀ y, 0 ≤ ev n g ph r y := fun y => by unfold ev; positivity
  have hxx : ∀ y, xx n g ph r ε y = (1 + Real.log (1 + ε ^ 2)) - lw n g ph r ε y := fun y => rfl
  have htw : (fun y => (twist n g ph r ε y : ℂ)) =
      fun y => ((dualK (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε y) : ℝ) : ℂ) := by
    funext y
    rw [dualK_eq (by rw [← hxx]; linarith [(hB1 y).1])]
    unfold twist eta
    rw [hxx]
  have hevf : (fun y => (ev n g ph r y : ℂ)) =
      fun y => (((fun t => Real.exp t - ε ^ 2) (lw n g ph r ε y) : ℝ) : ℂ) := by
    funext y
    simp only
    unfold lw
    rw [Real.exp_log (by have := hev0 y; positivity)]
    push_cast
    ring
  have hnT : ∀ x ξ, ‖dbarDot n z (fun y => (twist n g ph r ε y : ℂ)) x ξ‖ =
      kap n g ph r ε x / eta n g ph r ε x * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ := by
    intro x ξ
    rw [htw, dual_dbarDot_comp_real n z _ (dualK_contDiff _) _ hlw1,
      dualK_deriv (by rw [← hxx]; exact (hB1 x).1)]
    rw [← hxx]
    congr 1
    rw [abs_of_nonneg]
    · rfl
    · have h1 := (hB1 x).1
      have h2 := (hB1 x).2.1
      unfold eta at h2
      positivity
  have hnE : ∀ x ξ, ‖dbarDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ =
      (ev n g ph r x + ε ^ 2) * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ := by
    intro x ξ
    rw [hevf, dual_dbarDot_comp_real n z _ (Real.contDiff_exp.sub contDiff_const) _ hlw1]
    congr 1
    simp only [deriv_sub_const, Real.deriv_exp]
    unfold lw
    rw [Real.exp_log (by have := hev0 x; positivity), abs_of_nonneg (by have := hev0 x; positivity)]
  refine ⟨fun x ξ => ?_, fun x ξ hx => ?_, fun x ξ hx => ?_⟩
  · rw [hnT]
    set X := xx n g ph r ε x
    set E := eta n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h1 := hT1 x ξ
    have hX : 1 ≤ X := (hB1 x).1
    have hE : 1 ≤ E := (hB1 x).2.1
    have hk : kap n g ph r ε x = 1 + 1 / X := rfl
    have hb : bfun n g ph r ε x = (X + 1) ^ 2 / ((X + 1) ^ 2 + E) := rfl
    rw [hk] at h1 ⊢
    rw [hb]
    have hid : ((1 + 1 / X) / E) ^ 2 =
        (X + 1) ^ 2 / ((X + 1) ^ 2 + E) * (1 / (X ^ 2 * E) + ((1 + 1 / X) / E) ^ 2) := by
      have : X ≠ 0 := by positivity
      have : E ≠ 0 := by positivity
      have : (X + 1) ^ 2 + E ≠ 0 := by positivity
      field_simp
      ring
    rw [mul_pow, hid, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · rw [hnT]
    set X := xx n g ph r ε x
    set E := eta n g ph r ε x
    set K := kap n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h1 := hT1 x ξ
    have h2 := hT2 x ξ hx
    have hX : 1 ≤ X := (hB1 x).1
    have hE : 1 ≤ E := (hB1 x).2.1
    have hK2 : K ≤ 2 := (hB1 x).2.2.1
    have hK1 : 1 ≤ K := by
      have : K = 1 + 1 / X := rfl
      rw [this]
      have : 0 < 1 / X := by positivity
      linarith
    have hΘ : 0 ≤ Θ := le_trans (by positivity) h1
    have hE0 : 0 < E := by linarith
    calc (K / E * D) ^ 2 = K / E ^ 2 * (K * D ^ 2) := by field_simp
      _ ≤ K / E ^ 2 * (E * Θ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K / E * Θ := by field_simp
      _ ≤ 2 / E * Θ := mul_le_mul_of_nonneg_right (by gcongr) hΘ
  · rw [hnE]
    set E := eta n g ph r ε x
    set K := kap n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h2 := hT2 x ξ hx
    have hK1 : 1 ≤ K := by
      have : K = 1 + 1 / xx n g ph r ε x := rfl
      rw [this]
      have : 0 < 1 / xx n g ph r ε x := by have := (hB1 x).1; positivity
      linarith
    have hev := hev0 x
    have hQ : (ev n g ph r x + ε ^ 2) ^ 2 ≤ 4 * ε ^ 4 := by nlinarith
    have hD : D ^ 2 ≤ E * Θ := le_trans (le_mul_of_one_le_left (by positivity) hK1) h2
    calc ((ev n g ph r x + ε ^ 2) * D) ^ 2 = (ev n g ph r x + ε ^ 2) ^ 2 * D ^ 2 := by ring
      _ ≤ 4 * ε ^ 4 * D ^ 2 := mul_le_mul_of_nonneg_right hQ (by positivity)
      _ ≤ 4 * ε ^ 4 * (E * Θ) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = 4 * ε ^ 4 * E * Θ := by ring

end

end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

namespace SmoothCutoff

noncomputable def bump (s : ℝ) : ℝ :=
  Real.smoothTransition (20 * (s - 1 / 2)) * Real.smoothTransition (20 * (1 - s))

theorem bump_contDiff : ContDiff ℝ ∞ bump := by
  unfold bump
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

theorem bump_continuous : Continuous bump := bump_contDiff.continuous

theorem bump_nonneg (s : ℝ) : 0 ≤ bump s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bump_le_one (s : ℝ) : bump s ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem bump_of_le_half {s : ℝ} (h : s ≤ 1 / 2) : bump s = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem bump_of_one_le {s : ℝ} (h : 1 ≤ s) : bump s = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (x := 20 * (1 - s)) (by linarith), mul_zero]

theorem bump_of_mem {s : ℝ} (h1 : 11 / 20 ≤ s) (h2 : s ≤ 19 / 20) : bump s = 1 := by
  unfold bump
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

noncomputable def prim (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, bump s

theorem prim_hasDerivAt (t : ℝ) : HasDerivAt prim (bump t) t :=
  (bump_continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem deriv_prim : deriv prim = bump := funext fun t => (prim_hasDerivAt t).deriv

theorem prim_contDiff : ContDiff ℝ ∞ prim :=
  contDiff_infty_iff_deriv.2
    ⟨fun t => (prim_hasDerivAt t).differentiableAt, by rw [deriv_prim]; exact bump_contDiff⟩

theorem prim_monotone : Monotone prim :=
  monotone_of_deriv_nonneg (fun t => (prim_hasDerivAt t).differentiableAt)
    (fun t => by rw [deriv_prim]; exact bump_nonneg t)

theorem prim_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : prim t = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro s hs
  apply bump_of_le_half
  have := (Set.mem_uIcc.1 hs)
  rcases this with h | h <;> linarith [h.1, h.2]

theorem prim_of_one_le {t : ℝ} (ht : 1 ≤ t) : prim t = prim 1 := by
  unfold prim
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (bump_continuous.intervalIntegrable _ _) (bump_continuous.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (a := 1) (b := t) (g := fun _ => (0 : ℝ)),
    intervalIntegral.integral_zero, add_zero]
  intro s hs
  rw [Set.uIcc_of_le ht] at hs
  exact bump_of_one_le hs.1

theorem prim_one_ge : 2 / 5 ≤ prim 1 := by
  unfold prim
  have hi : ∀ a b : ℝ, IntervalIntegrable bump volume a b :=
    fun a b => bump_continuous.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 19 / 20) (hi _ _) (hi _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := 11 / 20) (hi _ _) (hi _ _)]
  have h1 : 0 ≤ ∫ s in (0 : ℝ)..11 / 20, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h3 : 0 ≤ ∫ s in (19 / 20 : ℝ)..1, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h2 : ∫ s in (11 / 20 : ℝ)..19 / 20, bump s = 2 / 5 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp; norm_num
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact bump_of_mem hs.1 hs.2
  linarith

theorem prim_nonneg (t : ℝ) : 0 ≤ prim t := by
  have := prim_monotone (min_le_left t (1 / 2))
  rwa [prim_of_le_half (min_le_right t (1 / 2))] at this

theorem prim_le (t : ℝ) : prim t ≤ prim 1 := by
  have := prim_monotone (le_max_left t 1)
  rwa [prim_of_one_le (le_max_right t 1)] at this

noncomputable def chi (t : ℝ) : ℝ := 1 - prim t / prim 1

theorem chi_hasDerivAt (t : ℝ) : HasDerivAt chi (-(bump t / prim 1)) t :=
  ((prim_hasDerivAt t).div_const (prim 1)).const_sub 1

theorem isCutoff_chi : IsCutoff chi := by
  have hI : 0 < prim 1 := by linarith [prim_one_ge]
  refine ⟨contDiff_const.sub (prim_contDiff.div_const _), ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp [chi, prim_of_le_half ht]
  · intro t ht
    simp [chi, prim_of_one_le ht, hI.ne']
  · intro t
    have h0 : 0 ≤ prim t / prim 1 := div_nonneg (prim_nonneg t) hI.le
    have h1 : prim t / prim 1 ≤ 1 := (div_le_one hI).2 (prim_le t)
    constructor <;> simp only [chi] <;> linarith
  · intro t
    rw [(chi_hasDerivAt t).deriv, abs_neg, abs_of_nonneg (div_nonneg (bump_nonneg t) hI.le),
      div_le_iff₀ hI]
    nlinarith [bump_le_one t, prim_one_ge]

end SmoothCutoff

theorem cutoff : CutoffStatement := ⟨SmoothCutoff.chi, SmoothCutoff.isCutoff_chi⟩

end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Module Set
open scoped ENNReal ContDiff

theorem polar_finrank (n : ℕ) : finrank ℝ (V n) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

private theorem nontrivial_V_of_one_le (n : ℕ) (hn : 1 ≤ n) : Nontrivial (ReciprocityTheory.L2DbarEstimates.V n) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [polar_finrank]; omega)

theorem polar_ballReal (n : ℕ) (hn : 1 ≤ n) :
    (volume : Measure (V n)).real (ball 0 1) = Real.pi ^ n / (Nat.factorial n : ℝ) := by
  have hG : Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ) := by
    rw [show ((2 * n : ℕ) : ℝ) / 2 + 1 = (n : ℝ) + 1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial n
  have hs : Real.sqrt Real.pi ^ (2 * n) = Real.pi ^ n := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have hpos : (0 : ℝ) ≤ Real.pi ^ n / (n.factorial : ℝ) := by positivity
  have := nontrivial_V_of_one_le n hn
  rw [measureReal_def, InnerProductSpace.volume_ball, polar_finrank, hG, hs,
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal hpos]

theorem polar_radial (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in Ioi (0:ℝ), y ^ (2 * n - 1) •
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y =
      Real.log (b / a) / 2 := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hb : 0 < b := ha.trans_le hab
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsab : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have hpt : ∀ y : ℝ, y ^ (2 * n - 1) •
      (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y =
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => t⁻¹) y := by
    intro y
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Icc (Real.sqrt a) (Real.sqrt b)
    · rw [if_pos hy, if_pos hy]
      have hy0 : 0 < y := hsa.trans_le hy.1
      rw [smul_eq_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      have hsplit : (y ^ 2) ^ (k + 1) = y ^ (2 * k + 1) * y := by ring
      rw [hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy0.ne'), one_mul]
    · rw [if_neg hy, if_neg hy, smul_zero]
  calc ∫ y in Ioi (0:ℝ), y ^ (2 * n - 1) •
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y
      = ∫ y in Ioi (0:ℝ), (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => t⁻¹) y := by
        exact congrArg _ (funext hpt)
    _ = ∫ y in Icc (Real.sqrt a) (Real.sqrt b), y⁻¹ := by
        rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
          Set.inter_eq_left.mpr (show Icc (Real.sqrt a) (Real.sqrt b) ⊆ Ioi 0 from
            fun y hy => hsa.trans_le hy.1)]
    _ = Real.log (Real.sqrt b / Real.sqrt a) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsab,
          integral_inv_of_pos hsa hsb]
    _ = Real.log (b / a) / 2 := by
        rw [Real.log_div hsb.ne' hsa.ne', Real.log_sqrt hb.le, Real.log_sqrt ha.le,
          Real.log_div hb.ne' ha.ne']
        ring

theorem polar (n : ℕ) : PolarStatement n := by
  intro hn a b ha hab
  have := nontrivial_V_of_one_le n hn
  have hb : 0 < b := ha.trans_le hab
  have hsa0 := Real.sqrt_nonneg a
  have hsb0 := Real.sqrt_nonneg b
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hmem : ∀ y : ReciprocityTheory.L2DbarEstimates.V n, (a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b) ↔
      (Real.sqrt a ≤ ‖y‖ ∧ ‖y‖ ≤ Real.sqrt b) := by
    intro y
    have h0 := norm_nonneg y
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · calc Real.sqrt a ≤ Real.sqrt (‖y‖ ^ 2) := Real.sqrt_le_sqrt h1
          _ = ‖y‖ := Real.sqrt_sq h0
      · calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq h0).symm
          _ ≤ Real.sqrt b := Real.sqrt_le_sqrt h2
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  have hSc : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} := by
    have h1 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2} :=
      isClosed_le continuous_const (continuous_norm.pow 2)
    have h2 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | ‖y‖ ^ 2 ≤ b} :=
      isClosed_le (continuous_norm.pow 2) continuous_const
    exact h1.inter h2
  have hsub : {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} ⊆ closedBall 0 (b + 1) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    have h0 := norm_nonneg y
    have h2 : ‖y‖ ^ 2 ≤ b := hy.2
    nlinarith [mul_self_nonneg (‖y‖ - 1)]
  have hK : IsCompact {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} :=
    (isCompact_closedBall (0 : ReciprocityTheory.L2DbarEstimates.V n) (b + 1)).of_isClosed_subset hSc hsub
  have hcont : ContinuousOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} :=
    (continuous_norm.pow 2).continuousOn.rpow_const
      (fun y hy => Or.inl (ha.trans_le (hy : a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b).1).ne')
  have hint_r : IntegrableOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} volume :=
    hcont.integrableOn_compact hK
  have hnn : 0 ≤ᵐ[volume.restrict {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}]
      (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) :=
    ae_of_all _ (fun y => Real.rpow_nonneg (by positivity) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_r hnn]
  congr 1
  have hpt : ∀ y : ReciprocityTheory.L2DbarEstimates.V n,
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}.indicator
          (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) y =
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ := by
    intro y
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}
    · rw [if_pos hy, if_pos (show ‖y‖ ∈ Icc (Real.sqrt a) (Real.sqrt b) from (hmem y).1 hy)]
    · rw [if_neg hy, if_neg (show ‖y‖ ∉ Icc (Real.sqrt a) (Real.sqrt b) from
        fun h => hy ((hmem y).2 h))]
  have hI : ∫ y in {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}, (‖y‖ ^ 2) ^ (-(n : ℝ)) =
      ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ := by
    rw [← integral_indicator hSc.measurableSet]
    exact congrArg _ (funext hpt)
  have hP : ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ =
      (2 * n : ℕ) • (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)).real (ball 0 1) • ∫ y in Ioi (0:ℝ),
        y ^ (2 * n - 1) • (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y := by
    rw [integral_fun_norm_addHaar (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)), polar_finrank]
  rw [hI, hP, polar_ballReal n hn, polar_radial n hn a b ha hab,
    nsmul_eq_mul, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem covDet (n : ℕ) (f' : V n →L[ℂ] V n) :
    |(f'.restrictScalars ℝ : V n →L[ℝ] V n).det| =
      ‖LinearMap.det (f' : V n →ₗ[ℂ] V n)‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

theorem cov (n : ℕ) : CovStatement n := by
  intro W G f hW hG hinj _
  have hd : ∀ y ∈ W, HasFDerivWithinAt G ((fderiv ℂ G y).restrictScalars ℝ) W y := fun y hy =>
    (((hG y hy).differentiableAt (hW.mem_nhds hy)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hW.measurableSet hd hinj f]
  simp only [covDet]

end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal

theorem vanish_lintegral_ball_smul (n : ℕ) (F : V n → ℝ≥0∞) (hF : Measurable F) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∫⁻ y in ball (0 : V n) 1, F (ρ • y) =
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| * ∫⁻ y in ball (0 : V n) ρ, F y := by
  have hind : ∀ y : V n, (ball (0 : V n) 1).indicator (fun y => F (ρ • y)) y =
      (ball (0 : V n) ρ).indicator F (ρ • y) := by
    intro y
    have hm : ρ • y ∈ ball (0 : V n) ρ ↔ y ∈ ball (0 : V n) 1 := by
      simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      exact mul_lt_iff_lt_one_right hρ
    by_cases h : y ∈ ball (0 : V n) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hm.mp h'))]
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  simp_rw [hind]
  have hFm : Measurable ((ball (0 : V n) ρ).indicator F) := hF.indicator measurableSet_ball
  rw [← lintegral_map hFm (measurable_const_smul ρ), Measure.map_addHaar_smul _ hρ.ne',
    lintegral_smul_measure, smul_eq_mul]

theorem vanish_div (n : ℕ) (hn : 1 ≤ n) (hDiv : C.MVDivStatement) {ρ c : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝[>] 0)) :
    Tendsto (fun k => ∫⁻ y in ball (0 : V n) ρ,
      ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ)))) atTop (𝓝 ∞) := by
  have hn0 : 0 < n := hn
  have hcr : 0 < c * ρ ^ 2 := by positivity
  obtain ⟨hδ0, hδpos⟩ := tendsto_nhdsWithin_iff.mp hδ
  have hη : Tendsto (fun k => δ k / (c * ρ ^ 2)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hδ0.div_const (c * ρ ^ 2)
    · exact hδpos.mono fun k hk => div_pos hk hcr
  have hΦ := (hDiv n hn0).comp hη
  set K : ℝ≥0∞ := ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
    ENNReal.ofReal ((c * ρ ^ 2) ^ (-(n : ℝ))) with hK
  have hK0 : K ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hlim := ENNReal.Tendsto.const_mul (a := K) hΦ (Or.inl ENNReal.top_ne_zero)
  rw [ENNReal.mul_top hK0] at hlim
  refine hlim.congr' ?_
  filter_upwards [hδpos] with k hk
  have hk' : 0 < δ k := hk
  have hG : Measurable fun y : V n => ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) := by
    fun_prop
  have hs := vanish_lintegral_ball_smul n _ hG hρ
  have hd : ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  have hrhs : ∫⁻ y in ball (0 : V n) ρ, ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) =
      ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
        ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ((c * ‖ρ • y‖ ^ 2 + δ k) ^ (-(n : ℝ))) := by
    rw [hs, ← mul_assoc, hd, one_mul]
  show K * _ = _
  rw [hrhs, hK, mul_assoc]
  congr 1
  simp only [Function.comp_apply]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun z => ?_)
  have hz : 0 ≤ ‖z‖ ^ 2 + δ k / (c * ρ ^ 2) := by positivity
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hcr.le hz]
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  field_simp

theorem vanish (n : ℕ) (hMV : C.MVStatement) (hDiv : C.MVDivStatement) : VanishStatement n := by
  intro hn ρ c C0 δ u hρ hc hδ hu hb
  have hW := vanish_div n hn hDiv hρ hc hδ
  set W : ℕ → ℝ≥0∞ := fun k => ∫⁻ y in ball (0 : V n) ρ,
    ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) with hWdef
  have hmv : ∀ k, ‖u k 0‖ₑ ^ 2 * W k ≤ ENNReal.ofReal C0 := by
    intro k
    have hr : Measurable fun t : ℝ => ENNReal.ofReal ((c * t ^ 2 + δ k) ^ (-(n : ℝ))) := by
      fun_prop
    have h1 := hMV n 0 ρ (u k) _ (hu k) hr
    simp only [sub_zero] at h1
    refine le_trans h1 (le_trans (le_of_eq ?_) (hb k))
    refine lintegral_congr (fun y => ?_)
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hbd : ∀ᶠ k in atTop, ‖u k 0‖ₑ ^ 2 ≤ ENNReal.ofReal C0 / W k := by
    filter_upwards [hW.eventually (lt_mem_nhds ENNReal.one_lt_top)] with k hk
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (lt_trans zero_lt_one hk)))
      (Or.inr ENNReal.ofReal_ne_top)]
    exact hmv k
  have hq : Tendsto (fun k => ENNReal.ofReal C0 / W k) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_div (a := ENNReal.ofReal C0) hW (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have hsq : Tendsto (fun k => ‖u k 0‖ₑ ^ 2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq
      (Filter.Eventually.of_forall fun _ => bot_le) hbd
  have hr : Tendsto (fun k => ‖u k 0‖ ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsq
    simpa [Function.comp_def, ENNReal.toReal_pow] using this
  have hn' : Tendsto (fun k => ‖u k 0‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hr
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn'

end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff





end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

noncomputable section

theorem macof_fderiv_apply_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (u : V n) : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y u) U := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2.clm_apply contDiffOn_const

theorem macof_wd_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) : ContDiffOn ℝ ∞ (wd n j g) U := by
  unfold wd
  exact ((macof_fderiv_apply_contDiffOn hU hg _).sub
    (contDiffOn_const.mul (macof_fderiv_apply_contDiffOn hU hg _))).div_const 2

theorem macof_wdb_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) : ContDiffOn ℝ ∞ (wdb n j g) U := by
  unfold wdb
  exact ((macof_fderiv_apply_contDiffOn hU hg _).add
    (contDiffOn_const.mul (macof_fderiv_apply_contDiffOn hU hg _))).div_const 2

def macofDet (n : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℂ) ℂ where
  toMultilinearMap :=
    ((Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap).restrictScalars ℝ
  cont := by
    show Continuous fun v : Fin n → Fin n → ℂ => Matrix.det (Matrix.of v)
    exact continuous_id.matrix_det

def macofRow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap.toLinearMap M i

theorem macofRow_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (u : Fin n → ℂ) :
    macofRow M i u = (M.updateRow i u).det := rfl

theorem macof_hasFDerivAt_det {n : ℕ} (B : V n → Matrix (Fin n) (Fin n) ℂ) (y : V n)
    (B' : Fin n → Fin n → (V n →L[ℝ] ℂ))
    (hB : ∀ i l, HasFDerivAt (fun w => B w i l) (B' i l) y) (v : V n) :
    fderiv ℝ (fun w => (B w).det) y v =
      ∑ i, ((B y).updateRow i (fun l => B' i l v)).det := by
  have hrows : HasFDerivAt (fun w => (fun i l => B w i l : Fin n → Fin n → ℂ))
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun l => B' i l) y :=
    hasFDerivAt_pi.2 fun i => hasFDerivAt_pi.2 fun l => hB i l
  have hcomp := ((macofDet n).hasFDerivAt (fun i l => B y i l)).comp y hrows
  have hc2 : HasFDerivAt (fun w => (B w).det)
      (((macofDet n).linearDeriv fun i l => B y i l).comp
        (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun l => B' i l)) y := hcomp
  rw [hc2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    ContinuousLinearMap.pi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

theorem macof_swap {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n} (h : i ≠ j)
    (e c : Fin n → ℂ) :
    ((M.updateRow i e).updateRow j c).det = -((M.updateRow j e).updateRow i c).det := by
  have hB : (M.updateRow j e).updateRow i c =
      ((M.updateRow i e).updateRow j c).submatrix (Equiv.swap i j) id := by
    ext a b
    simp only [Matrix.submatrix_apply, id]
    rcases eq_or_ne a i with rfl | ha
    · simp [Matrix.updateRow_apply, h]
    rcases eq_or_ne a j with rfl | hb
    · simp [Matrix.updateRow_apply, h, ha, Ne.symm h]
    · simp [Matrix.updateRow_apply, ha, hb, Equiv.swap_apply_of_ne_of_ne ha hb]
  rw [hB, Matrix.det_permute, Equiv.Perm.sign_swap h]
  simp

private theorem wd_wd_comm_of_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {G : V n → ℂ}
    (hG : ContDiffOn ℝ ∞ G U) (i j : Fin n) {y : V n} (hy : y ∈ U) :
    wd n j (wd n i G) y = wd n i (wd n j G) y := by
  have hGa : ContDiffAt ℝ ∞ G y := hG.contDiffAt (hU.mem_nhds hy)
  have hsym := hGa.isSymmSndFDerivAt (by first | (simp; norm_cast) | simp | norm_cast)
  have hD2 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) y) y :=
    ((hGa.fderiv_right (m := 1) (by first | norm_cast | simp)).differentiableAt
      (by first | simp | decide)).hasFDerivAt
  have key : ∀ (a : Fin n) (v : V n), fderiv ℝ (wd n a G) y v =
      (fderiv ℝ (fderiv ℝ G) y v (bas n a) -
        Complex.I * fderiv ℝ (fderiv ℝ G) y v (Complex.I • bas n a)) / 2 := by
    intro a v
    have h1 : HasFDerivAt (fun w => fderiv ℝ G w (bas n a))
        ((fderiv ℝ (fderiv ℝ G) y).flip (bas n a)) y := by
      have h0 := hD2.clm_apply (hasFDerivAt_const (bas n a) y)
      simpa using h0
    have h2 : HasFDerivAt (fun w => fderiv ℝ G w (Complex.I • bas n a))
        ((fderiv ℝ (fderiv ℝ G) y).flip (Complex.I • bas n a)) y := by
      have h0 := hD2.clm_apply (hasFDerivAt_const (Complex.I • bas n a) y)
      simpa using h0
    have h3 := (h1.sub (h2.const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    have hwd : wd n a G = fun w =>
        (fderiv ℝ G w (bas n a) - Complex.I * fderiv ℝ G w (Complex.I • bas n a)) / 2 := by
      funext w
      rfl
    have h4 : HasFDerivAt (fun w =>
        (fderiv ℝ G w (bas n a) - Complex.I * fderiv ℝ G w (Complex.I • bas n a)) / 2)
        ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ G) y).flip (bas n a) -
          Complex.I • (fderiv ℝ (fderiv ℝ G) y).flip (Complex.I • bas n a))) y := by
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.sub_apply]
      ring
    rw [hwd, h4.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  show (fderiv ℝ (wd n i G) y (bas n j) - Complex.I * fderiv ℝ (wd n i G) y (Complex.I • bas n j)) / 2 =
    (fderiv ℝ (wd n j G) y (bas n i) - Complex.I * fderiv ℝ (wd n j G) y (Complex.I • bas n i)) / 2
  rw [key i, key i, key j, key j, hsym (bas n j) (bas n i), hsym (bas n j) (Complex.I • bas n i),
    hsym (Complex.I • bas n j) (bas n i), hsym (Complex.I • bas n j) (Complex.I • bas n i)]
  ring

theorem macof_main (n : ℕ) : MACofStatement n := by
  intro U f hU hf y hy k
  have hg : ContDiffOn ℝ ∞ (fun w' => (f w' : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  have hent : ∀ i l, ContDiffOn ℝ ∞ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) U :=
    fun i l => macof_wd_contDiffOn hU (macof_wdb_contDiffOn hU hg l) i
  have hd : ∀ i l, DifferentiableAt ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y :=
    fun i l => ((hent i l).contDiffAt (hU.mem_nhds hy)).differentiableAt (by first | simp | decide)
  have hwd : ∀ (j : Fin n) (F : V n → ℂ), wd n j F y =
      (fderiv ℝ F y (bas n j) - Complex.I * fderiv ℝ F y (Complex.I • bas n j)) / 2 :=
    fun j F => rfl
  have hdz : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n), (M.updateRow i 0).det = 0 :=
    fun M i => by rw [← macofRow_apply, map_zero]
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin n → Fin n → ℂ, ∀ i j, Z i j = if i = j then 0 else
      (((cHess n (fun w' => (f w' : ℂ)) y).updateRow j (Pi.single k 1)).updateRow i
        (fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y)).det :=
    ⟨_, fun _ _ => rfl⟩
  have hterm : ∀ j, wd n j (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y =
      ∑ i, Z i j := by
    intro j
    have hfun : (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) =
        fun w => ((cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)).det := by
      funext w
      rw [Matrix.adjugate_apply]
    have hB : ∀ i l, HasFDerivAt
        (fun w => ((cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)) i l)
        (if i = j then 0 else fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y) y := by
      intro i l
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.updateRow_self, if_true]
        exact hasFDerivAt_const _ _
      · simp only [Matrix.updateRow_ne hij, if_neg hij]
        exact (hd i l).hasFDerivAt
    have hdet := macof_hasFDerivAt_det
      (fun w => (cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)) y _ hB
    try beta_reduce at hdet
    rw [hfun, hwd, hdet, hdet, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hZ]
    by_cases hij : i = j
    · simp only [if_pos hij, ContinuousLinearMap.zero_apply]
      simp only [← Pi.zero_def, hdz]
      first | ring | simp
    · simp only [if_neg hij]
      rw [← macofRow_apply, ← macofRow_apply, ← macofRow_apply]
      have hρ : (fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y) =
          (2 : ℂ)⁻¹ • ((fun l => fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y (bas n j)) -
            Complex.I • (fun l => fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y
              (Complex.I • bas n j))) := by
        funext l
        simp only [hwd, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [hρ, map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul]
      ring
  have hanti : ∀ i j, Z i j = -Z j i := by
    intro i j
    rw [hZ, hZ]
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      have hc : (fun l => wd n i (fun w => cHess n (fun w' => (f w' : ℂ)) w j l) y) =
          fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y := by
        funext l
        exact wd_wd_comm_of_contDiffOn hU (macof_wdb_contDiffOn hU hg l) j i hy
      rw [hc, macof_swap _ hij, neg_neg]
  simp only [hterm]
  have hS : ∑ j, ∑ i, Z i j = -∑ j, ∑ i, Z i j := by
    calc ∑ j, ∑ i, Z i j = ∑ j, ∑ i, -Z j i :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hanti i j
      _ = -∑ j, ∑ i, Z j i := by simp only [Finset.sum_neg_distrib]
      _ = -∑ j, ∑ i, Z i j := by rw [Finset.sum_comm]
  linear_combination hS / 2

end

theorem maCof (n : ℕ) : MACofStatement n := macof_main n

end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

namespace MongeAmpereIntegrability

variable {n : ℕ}

theorem integrable_wd {H : V n → ℂ} (hH : ContDiff ℝ 1 H) (hc : HasCompactSupport H)
    (j : Fin n) : Integrable (wd n j H) := by
  have h1 : Continuous fun y => fderiv ℝ H y (bas n j) :=
    (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h2 : Continuous fun y => fderiv ℝ H y (Complex.I • bas n j) :=
    (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcont : Continuous (wd n j H) := (h1.sub (continuous_const.mul h2)).div_const 2
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hc.isCompact fun y hy => ?_)
  exact (wd_zero_of_eqOn (isClosed_tsupport H).isOpen_compl
    (fun w hw => image_eq_zero_of_notMem_tsupport hw) j hy).1

end MongeAmpereIntegrability

theorem ma (n : ℕ) (hCof : MACofStatement n) : MAStatement n := by
  intro Ω ph v hΩ hph hv hvc hsub
  have hvo : ContDiffOn ℝ ∞ v Ω := hv.contDiffOn
  have hP : ContDiffOn ℝ ∞ (fun w => (ph w : ℂ)) Ω := MongeAmpereIntegrability.cdo_ofReal hph
  have hQ : ContDiffOn ℝ ∞ (fun w => (v w : ℂ)) univ := MongeAmpereIntegrability.cdo_ofReal hv.contDiffOn
  have hKc : IsOpen (tsupport v)ᶜ := (isClosed_tsupport v).isOpen_compl
  have hv0 : ∀ w ∈ (tsupport v)ᶜ, (v w : ℂ) = 0 := fun w hw => by
    simp [image_eq_zero_of_notMem_tsupport hw]
  have hQ1 : ∀ k, ∀ w ∈ (tsupport v)ᶜ, wdb n k (fun w => (v w : ℂ)) w = 0 := fun k w hw =>
    (MongeAmpereIntegrability.wd_zero_of_eqOn hKc hv0 k hw).2
  have hB0 : ∀ y ∉ tsupport v, cHess n (fun w => (v w : ℂ)) y = 0 := by
    intro y hy
    ext j k
    simp only [cHess, Matrix.of_apply, Matrix.zero_apply]
    exact (MongeAmpereIntegrability.wd_zero_of_eqOn hKc (hQ1 k) j hy).1
  have hQ1c : ∀ k, ContDiffOn ℝ ∞ (wdb n k (fun w => (v w : ℂ))) univ := fun k =>
    (MongeAmpereIntegrability.cdo_wd isOpen_univ hQ k).2
  have hBc : ∀ j k, ContDiffOn ℝ ∞ (fun y => cHess n (fun w => (v w : ℂ)) y j k) univ := by
    intro j k
    simp only [cHess, Matrix.of_apply]
    exact (MongeAmpereIntegrability.cdo_wd isOpen_univ (hQ1c k) j).1
  have hAc : ∀ j k, ContDiffOn ℝ ∞ (fun y => cHess n (fun w => (ph w : ℂ)) y j k) Ω := by
    intro j k
    simp only [cHess, Matrix.of_apply]
    exact (MongeAmpereIntegrability.cdo_wd hΩ (MongeAmpereIntegrability.cdo_wd hΩ hP k).2 j).1
  set D : ℝ → V n → ℂ := fun t y => ∑ k, ∑ j,
    (cHess n (fun w => (ph w : ℂ)) y + (t : ℂ) • cHess n (fun w => (v w : ℂ)) y).adjugate k j *
      cHess n (fun w => (v w : ℂ)) y j k with hD
  have hD0 : ∀ t, ∀ y ∉ tsupport v, D t y = 0 := by
    intro t y hy
    simp [hD, hB0 y hy]
  have hm : ∀ y (t : ℝ), cHess n (fun w => (ph w : ℂ)) y + (t : ℂ) • cHess n (fun w => (v w : ℂ)) y =
      Matrix.of fun i j => cHess n (fun w => (ph w : ℂ)) y i j +
        (t : ℂ) * cHess n (fun w => (v w : ℂ)) y i j := by
    intro y t; ext i j; simp
  have hDc : ContinuousOn (fun p : V n × ℝ => D p.2 p.1) (Ω ×ˢ univ) := by
    simp only [hD, hm]
    refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun j _ =>
      ContinuousOn.mul ?_ ?_
    · refine MongeAmpereIntegrability.cont_adj (fun i l (p : V n × ℝ) => cHess n (fun w => (ph w : ℂ)) p.1 i l +
        (p.2 : ℂ) * cHess n (fun w => (v w : ℂ)) p.1 i l) (fun i l => ?_) k j
      have h1 : ContinuousOn (fun p : V n × ℝ => cHess n (fun w => (ph w : ℂ)) p.1 i l)
          (Ω ×ˢ univ) := (hAc i l).continuousOn.comp continuousOn_fst fun p hp => hp.1
      have h2 : ContinuousOn (fun p : V n × ℝ => cHess n (fun w => (v w : ℂ)) p.1 i l)
          (Ω ×ˢ univ) := (hBc i l).continuousOn.comp continuousOn_fst fun p _ => mem_univ _
      have h3 : ContinuousOn (fun p : V n × ℝ => (p.2 : ℂ)) (Ω ×ˢ univ) :=
        (Complex.continuous_ofReal.comp continuous_snd).continuousOn
      exact h1.add (h3.mul h2)
    · exact (hBc j k).continuousOn.comp continuousOn_fst fun p _ => mem_univ _
  have hFTC : ∀ y, ∫ t in (0 : ℝ)..1, D t y =
      (cHess n (fun w => (ph w : ℂ)) y + cHess n (fun w => (v w : ℂ)) y).det -
        (cHess n (fun w => (ph w : ℂ)) y).det := by
    intro y
    have hcont : Continuous fun t : ℝ => D t y := by
      rw [← continuousOn_univ]
      simp only [hD, hm]
      refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun j _ =>
        ContinuousOn.mul ?_ continuousOn_const
      exact MongeAmpereIntegrability.cont_adj (fun i l (t : ℝ) => cHess n (fun w => (ph w : ℂ)) y i l +
        (t : ℂ) * cHess n (fun w => (v w : ℂ)) y i l)
        (fun i l => (continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)).continuousOn) k j
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => MongeAmpereIntegrability.hasDerivAt_det (cHess n (fun w => (ph w : ℂ)) y)
        (cHess n (fun w => (v w : ℂ)) y) t) (hcont.intervalIntegrable 0 1)]
    simp
  have hDint : ∀ t : ℝ, ∫ y in Ω, D t y = 0 := by
    intro t
    set f : V n → ℝ := fun w => ph w + t * v w with hf_def
    have hf : ContDiffOn ℝ ∞ f Ω := hph.add (contDiffOn_const.mul hvo)
    have hF : ContDiffOn ℝ ∞ (fun w => (f w : ℂ)) Ω := MongeAmpereIntegrability.cdo_ofReal hf
    have hHc : ∀ k j, ContDiffOn ℝ ∞
        (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) Ω := fun k j =>
      MongeAmpereIntegrability.cdo_adj (fun i l w => wd n i (wdb n l (fun w' => (f w' : ℂ))) w)
        (fun i l => (MongeAmpereIntegrability.cdo_wd hΩ (MongeAmpereIntegrability.cdo_wd hΩ hF l).2 i).1) k j
    set G : Fin n → Fin n → V n → ℂ := fun k j w =>
      (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j * wdb n k (fun w => (v w : ℂ)) w with hG
    have hG0 : ∀ k j, ∀ w ∉ tsupport v, G k j w = 0 := fun k j w hw => by
      simp [hG, hQ1 k w hw]
    have hGc : ∀ k j, ContDiff ℝ 1 (G k j) := by
      intro k j
      rw [contDiff_iff_contDiffAt]
      intro w
      by_cases hw : w ∈ Ω
      · exact (((hHc k j).mul ((hQ1c k).mono (subset_univ _))).contDiffAt
          (hΩ.mem_nhds hw)).of_le (by simp)
      · have hwK : w ∉ tsupport v := fun h => hw (hsub h)
        have he : G k j =ᶠ[𝓝 w] fun _ => (0 : ℂ) :=
          Filter.eventually_of_mem (hKc.mem_nhds hwK) fun x hx => hG0 k j x hx
        exact contDiffAt_const.congr_of_eventuallyEq he
    have hGs : ∀ k j, HasCompactSupport (G k j) := fun k j =>
      HasCompactSupport.intro hvc.isCompact (hG0 k j)
    have hpt : ∀ y, D t y = ∑ k, ∑ j, wd n j (G k j) y := by
      intro y
      by_cases hy : y ∈ Ω
      · have hHy : cHess n (fun w' => (f w' : ℂ)) y = cHess n (fun w => (ph w : ℂ)) y +
            (t : ℂ) • cHess n (fun w => (v w : ℂ)) y := MongeAmpereIntegrability.cHess_add_smul hΩ hph hvo t hy
        simp only [hD]
        rw [← hHy]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hc := hCof Ω f hΩ hf y hy k
        have d1 : ∀ j, DifferentiableAt ℝ
            (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y := fun j =>
          ((hHc k j).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
        have d2 : DifferentiableAt ℝ (wdb n k (fun w => (v w : ℂ))) y :=
          ((hQ1c k).differentiableOn (by simp)).differentiableAt Filter.univ_mem
        have e : ∀ j, wd n j (G k j) y =
            wd n j (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y *
              wdb n k (fun w => (v w : ℂ)) y +
            (cHess n (fun w' => (f w' : ℂ)) y).adjugate k j *
              wd n j (wdb n k (fun w => (v w : ℂ))) y := fun j =>
          ChartWirtingerDerivatives.wd_mul' n j _ _ y (d1 j) d2
        simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hc, zero_mul, zero_add]
        rfl
      · have hyK : y ∉ tsupport v := fun h => hy (hsub h)
        rw [hD0 t y hyK]
        symm
        refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => ?_
        exact (MongeAmpereIntegrability.wd_zero_of_eqOn hKc (hG0 k j) j hyK).1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => hD0 t y (fun h => hy (hsub h)))]
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun j _ =>
      MongeAmpereIntegrability.integrable_wd (hGc k j) (hGs k j) j)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_finsetSum _ (fun j _ => MongeAmpereIntegrability.integrable_wd (hGc k j) (hGs k j) j)]
    exact Finset.sum_eq_zero fun j _ => integral_wd_eq_zero n j (G k j) (hGc k j) (hGs k j)
  have hInt : Integrable (Function.uncurry fun (y : V n) (t : ℝ) => D t y)
      ((volume.restrict Ω).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    refine IntegrableOn.of_forall_sdiff_eq_zero (s := tsupport v ×ˢ Icc (0 : ℝ) 1) ?_
      (hΩ.measurableSet.prod measurableSet_Ioc) ?_
    · exact ContinuousOn.integrableOn_compact (hvc.isCompact.prod isCompact_Icc)
        (hDc.mono fun p hp => ⟨hsub hp.1, mem_univ _⟩)
    · rintro ⟨y, t⟩ ⟨⟨_, ht⟩, hn⟩
      have hyK : y ∉ tsupport v := fun h => hn ⟨h, Ioc_subset_Icc_self ht⟩
      exact hD0 t y hyK
  calc ∫ y in Ω, ((cHess n (fun w => ((ph w + v w : ℝ) : ℂ)) y).det -
        (cHess n (fun w => (ph w : ℂ)) y).det)
      = ∫ y in Ω, ∫ t in Ioc (0 : ℝ) 1, D t y := by
        refine setIntegral_congr_fun hΩ.measurableSet fun y hy => ?_
        have h1 := MongeAmpereIntegrability.cHess_add_smul hΩ hph hvo 1 hy
        simp only [one_mul, Complex.ofReal_one, one_smul] at h1
        rw [h1, ← intervalIntegral.integral_of_le zero_le_one, hFTC y]
    _ = ∫ t in Ioc (0 : ℝ) 1, ∫ y in Ω, D t y := integral_integral_swap hInt
    _ = 0 := by simp [hDint]

end

end ReciprocityTheory.L2DbarEstimates.I
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (hH : HStatement n M) (hC : HoloClosedNeed n M) :
    TWStatement n M := by
  intro X ps Ph F0 a b hps hPh hCb hlevi hF0 hF0w ha hb ha0 hb0 _ hA hB
  refine ⟨bergmanExists n M hC X ps F0 hps
    (Smooth.continuous n X.z X.isLocalHomeomorph F0 hF0).measurable hF0w, ?_⟩
  exact twBound n M hH X ps Ph F0 a b hps hPh hCb hlevi hF0 hF0w ha hb ha0 hb0 hA hB

end ReciprocityTheory.L2DbarEstimates.I
end
