import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalPolyDegreeSlashAction
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariablesStatement

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem norm_eval_smul_mul_im_rpow : ∀ (w : ℕ) (σ : SL(2, ℤ)) (P : ℂ[X]) (τ : ℍ), P ∈ degreeLT ℂ (w + 1) → ‖P.eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-(w : ℝ) / 2) = ‖(slP w (mat σ) P).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
  intro w σ P τ hP
  have hden : denom σ τ = ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) := by
    rw [ModularGroup.denom_apply]
  have hj : ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have hc : ((σ • τ : ℍ) : ℂ) = (((mat σ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 0 1 : ℤ) : ℂ)) /
      (((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ)) := by
    rw [specialLinearGroup_apply]
    simp
  have him := ModularGroup.im_smul_eq_div_normSq σ τ
  rw [hden] at him
  rw [eval_polySlash w (mat σ) P τ hP hj, ← hc, him]
  set j := ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) with hjdef
  have hn : 0 < ‖j‖ := norm_pos_iff.2 hj
  have hτ : 0 < τ.im := τ.im_pos
  rw [Complex.normSq_eq_norm_sq, Real.div_rpow hτ.le (by positivity), norm_mul, norm_pow]
  have h2 : (‖j‖ ^ 2) ^ (-(w : ℝ) / 2) = (‖j‖ ^ w)⁻¹ := by
    rw [← Real.rpow_natCast ‖j‖ 2, ← Real.rpow_mul hn.le, ← Real.rpow_natCast ‖j‖ w,
      ← Real.rpow_neg hn.le]
    congr 1
    push_cast
    ring
  rw [h2, div_inv_eq_mul]
  ring

end GlobalTheory.HeckeFamilyMatrices
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eval_smul_mul_im_rpow_polyDegreeSlash : ∀ (w : ℕ) (σ : SL(2, ℤ)) (P : ℂ[X]) (τ : ℍ), P ∈ degreeLT ℂ (w + 1) → ‖P.eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-(w : ℝ) / 2) = ‖(slP w (mat σ) P).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
  atlas_forward_decl GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow
end

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
open scoped Manifold Pointwise

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_norm_le_exp_of_one_le_im (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] (k : ℤ)
    (g : CuspForm G k) :
    ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖g τ‖ ≤ C * Real.exp (-c * τ.im) := by
  obtain ⟨c, hc, hd⟩ := CuspFormClass.exp_decay_atImInfty' (Γ := G) (k := k) g
  obtain ⟨C₀, hC₀⟩ := CuspFormClass.petersson_bounded_left k G g g
  obtain ⟨D, hD, h⟩ := hd.exists_pos
  rw [Asymptotics.IsBigOWith, atImInfty, eventually_comap, eventually_atTop] at h
  obtain ⟨y, hy⟩ := h
  have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ UpperHalfPlane.I)
  set M : ℝ := 1 + C₀ * |y| ^ k.natAbs with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨max D (M * Real.exp (c * |y|)), c, hc, fun τ hτ => ?_⟩
  rcases le_total y τ.im with h1 | h1
  · have h2 := hy _ h1 τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · have hy' : τ.im ≤ |y| := h1.trans (le_abs_self y)
    have hp : ‖g τ‖ ^ 2 * τ.im ^ k ≤ C₀ := by
      have := hC₀ τ
      simp only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj, norm_zpow,
        Complex.norm_real, Real.norm_of_nonneg τ.im_pos.le] at this
      calc _ = ‖g τ‖ * ‖g τ‖ * τ.im ^ k := by ring
        _ ≤ C₀ := this
    have hpos := τ.im_pos
    have hk : 1 ≤ τ.im ^ k * τ.im ^ k.natAbs := by
      rw [← zpow_natCast, ← zpow_add₀ hpos.ne']
      exact one_le_zpow₀ hτ (by omega)
    have h4 : ‖g τ‖ ^ 2 ≤ C₀ * |y| ^ k.natAbs :=
      calc ‖g τ‖ ^ 2 ≤ ‖g τ‖ ^ 2 * (τ.im ^ k * τ.im ^ k.natAbs) :=
            le_mul_of_one_le_right (by positivity) hk
        _ = ‖g τ‖ ^ 2 * τ.im ^ k * τ.im ^ k.natAbs := by ring
        _ ≤ C₀ * |y| ^ k.natAbs := by gcongr
    have h5 : ‖g τ‖ ≤ M := by nlinarith [sq_nonneg (‖g τ‖ - 1), norm_nonneg (g τ)]
    have h3 : 1 ≤ Real.exp (c * |y|) * Real.exp (-c * τ.im) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc ‖g τ‖ ≤ M := h5
      _ ≤ M * (Real.exp (c * |y|) * Real.exp (-c * τ.im)) := le_mul_of_one_le_right hM0 h3
      _ = M * Real.exp (c * |y|) * Real.exp (-c * τ.im) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem cuspForm_slash_holo_decay : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex →
    ∀ (f : CuspForm Γ k) (σ : SL(2, ℤ)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] σ) ∧
      ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖(⇑f ∣[k] σ) τ‖ ≤ C * Real.exp (-c * τ.im) := by
  intro Γ k hΓ f σ
  have : ((ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹) • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Γ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ σ)⁻¹
  exact ⟨(CuspForm.translate f (σ : GL (Fin 2) ℝ)).holo',
    cuspForm_norm_le_exp_of_one_le_im _ k (CuspForm.translate f (σ : GL (Fin 2) ℝ))⟩

end GlobalTheory.HeckeFamilyMatrices
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex → ∀ (f : CuspForm Γ k) (σ : SL(2, ℤ)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] σ) ∧ ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖(⇑f ∣[k] σ) τ‖ ≤ C * Real.exp (-c * τ.im) := by
  atlas_forward_decl GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay
end

section
section
open MeasureTheory Filter Topology Set

namespace GlobalTheory

theorem cauchy_parallelogram_upper_half_plane :
    ∀ (g : ℂ → ℂ) (τ : ℂ) (S : ℝ), DifferentiableOn ℂ g {z : ℂ | 0 < z.im} → 0 < τ.im → 0 ≤ S →
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I) := by
  intro g τ S hg hτ hS
  set φ : ℝ × ℝ → ℂ := fun x => Complex.I + (x.1 : ℂ) * (τ - Complex.I) + (x.2 : ℂ) * Complex.I
    with hφdef
  set L : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (τ - Complex.I) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I with hLdef
  have hφL : φ = fun x => Complex.I + L x := by
    funext x; simp [φ, L, Complex.real_smul]; ring
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpos : ∀ x : ℝ × ℝ, 0 ≤ x.1 → x.1 ≤ 1 → 0 ≤ x.2 → 0 < (φ x).im := by
    rintro ⟨t, s⟩ h0 h1 h2
    simp only [φ, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    rcases h1.lt_or_eq with h | h
    · nlinarith [mul_nonneg h0 hτ.le]
    · subst h; simp at *; nlinarith
  have hφc : Continuous φ := by
    rw [hφL]; exact continuous_const.add L.continuous
  have hcont : ContinuousOn (fun x => g (φ x)) (uIcc (0:ℝ) 1 ×ˢ uIcc (0:ℝ) S) := by
    refine hg.continuousOn.comp hφc.continuousOn ?_
    intro x hx
    rw [uIcc_of_le zero_le_one, uIcc_of_le hS] at hx
    exact hpos x hx.1.1 hx.1.2 hx.2.1
  set F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun x =>
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv g (φ x))).restrictScalars ℝ).comp L
  have hder : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) ×ˢ Ioo (min (0:ℝ) S) (max (0:ℝ) S),
      HasFDerivAt (fun x => g (φ x)) (F' x) x := by
    intro x hx
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one, min_eq_left hS, max_eq_right hS] at hx
    have hz : 0 < (φ x).im := hpos x hx.1.1.le hx.1.2.le hx.2.1.le
    have hgd : HasDerivAt g (deriv g (φ x)) (φ x) :=
      (hg.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hφd : HasFDerivAt φ L x := by
      rw [hφL]; exact L.hasFDerivAt.const_add _
    exact (hgd.hasFDerivAt.restrictScalars ℝ).comp x hφd
  have key := integral2_divergence_prod_of_hasFDerivAt
    (fun x => Complex.I * g (φ x)) (fun x => -(τ - Complex.I) * g (φ x))
    (fun x => Complex.I • F' x) (fun x => (-(τ - Complex.I)) • F' x) 0 0 1 S
    (continuousOn_const.mul hcont) (continuousOn_const.mul hcont)
    (fun x hx => (hder x hx).const_mul _) (fun x hx => (hder x hx).const_mul _)
    (by
      have : (fun x : ℝ × ℝ => (Complex.I • F' x) (1, 0) + ((-(τ - Complex.I)) • F' x) (0, 1))
          = fun _ => 0 := by
        funext x; simp [F', L]; ring
      rw [this]; exact integrableOn_zero)
  have hzero : ∀ x : ℝ × ℝ, (Complex.I • F' x) (1, 0) + ((-(τ - Complex.I)) • F' x) (0, 1) = 0 := by
    intro x; simp [F', L]; ring
  simp only [hzero, intervalIntegral.integral_zero, intervalIntegral.integral_const_mul] at key
  have e1 : ∀ s : ℝ, φ (1, s) = τ + s * Complex.I := by
    intro s; simp only [φ]; push_cast; ring
  have e0 : ∀ s : ℝ, φ (0, s) = Complex.I + s * Complex.I := by
    intro s; simp only [φ]; push_cast; ring
  have eS : ∀ t : ℝ, φ (t, S) = Complex.I + t * (τ - Complex.I) + S * Complex.I := fun _ => rfl
  have eT : ∀ t : ℝ, φ (t, 0) = Complex.I + t * (τ - Complex.I) := by
    intro t; simp only [φ]; push_cast; ring
  simp only [e1, e0, eS, eT] at key
  linear_combination -key

end GlobalTheory
end

open MeasureTheory Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_segment_eq_parallelogram_sides : ∀ (g : ℂ → ℂ) (τ : ℂ) (S : ℝ), DifferentiableOn ℂ g {z : ℂ | 0 < z.im} → 0 < τ.im → 0 ≤ S →
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I) := by
  atlas_forward_decl GlobalTheory.cauchy_parallelogram_upper_half_plane
end

section
section
open MeasureTheory Filter Topology Set

namespace GlobalTheory

theorem vertRay_expPow_weight_integrableOn (c : ℝ) (m : ℕ) (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-c * s) * (1 + s) ^ m) (Ioi 0) := by
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = c / 2 := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; positivity
  have hI : IntegrableOn (fun s : ℝ =>
      ((m.factorial : ℝ) / b ^ m * Real.exp b) * Real.exp (-b * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hb).const_mul _
  refine Integrable.mono' hI ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : (0:ℝ) ≤ s := le_of_lt hs
    have h1 := Real.pow_div_factorial_le_exp (b * (1 + s)) (mul_nonneg hb.le (by linarith)) m
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith) _))]
    have hf : (0:ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
    rw [div_le_iff₀ hf, mul_pow] at h1
    have key : (1 + s) ^ m ≤ (m.factorial : ℝ) / b ^ m * Real.exp (b * (1 + s)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb m)]
      linarith [h1]
    have he : Real.exp (b * (1 + s)) = Real.exp b * Real.exp (b * s) := by
      rw [← Real.exp_add]; ring_nf
    have hcs : Real.exp (-c * s) * Real.exp (b * s) = Real.exp (-b * s) := by
      rw [← Real.exp_add]; congr 1; rw [hbdef]; ring
    calc Real.exp (-c * s) * (1 + s) ^ m
        ≤ Real.exp (-c * s) * ((m.factorial : ℝ) / b ^ m * Real.exp (b * (1 + s))) :=
          mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
      _ = ((m.factorial : ℝ) / b ^ m * Real.exp b) * (Real.exp (-c * s) * Real.exp (b * s)) := by
          rw [he]; ring
      _ = ((m.factorial : ℝ) / b ^ m * Real.exp b) * Real.exp (-b * s) := by rw [hcs]

theorem vertRay_integral_expPow_bound : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ),
    ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) ∧
      ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖ ≤
        K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m *
          ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := by
  intro g K c m τ hg hc hb hτ
  have hK : 0 ≤ K := by
    have h := hb Complex.I (by simp)
    have hpos : 0 < Real.exp (-c * Complex.I.im) * (1 + ‖Complex.I‖) ^ m := by positivity
    by_contra hneg
    have hneg' : K < 0 := not_le.mp hneg
    have : K * Real.exp (-c * Complex.I.im) * (1 + ‖Complex.I‖) ^ m < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg' hpos
    linarith [norm_nonneg (g Complex.I)]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m := ⟨_, rfl⟩
  rw [← hA]
  have hw := vertRay_expPow_weight_integrableOn c m hc
  have hbound : ∀ s : ℝ, 0 < s →
      ‖g (τ + s * Complex.I)‖ ≤ A * (Real.exp (-c * s) * (1 + s) ^ m) := by
    intro s hs
    have him : (τ + s * Complex.I).im = τ.im + s := by simp
    have h1 := hb (τ + s * Complex.I) (by rw [him]; linarith)
    rw [him] at h1
    have hn : ‖τ + s * Complex.I‖ ≤ ‖τ‖ + s := by
      calc ‖τ + s * Complex.I‖ ≤ ‖τ‖ + ‖(s:ℂ) * Complex.I‖ := norm_add_le _ _
        _ = ‖τ‖ + s := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hp : (1 + ‖τ + s * Complex.I‖) ^ m ≤ (1 + ‖τ‖) ^ m * (1 + s) ^ m := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [mul_nonneg (norm_nonneg τ) hs.le]
    have he : Real.exp (-c * (τ.im + s)) = Real.exp (-c * τ.im) * Real.exp (-c * s) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖g (τ + s * Complex.I)‖
        ≤ K * Real.exp (-c * (τ.im + s)) * (1 + ‖τ + s * Complex.I‖) ^ m := h1
      _ ≤ K * Real.exp (-c * (τ.im + s)) * ((1 + ‖τ‖) ^ m * (1 + s) ^ m) :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg hK (Real.exp_pos _).le)
      _ = A * (Real.exp (-c * s) * (1 + s) ^ m) := by rw [he, hA]; ring
  have hmeas : AEStronglyMeasurable (fun s : ℝ => g (τ + s * Complex.I))
      (volume.restrict (Ioi 0)) := by
    have hc' : ContinuousOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) := by
      refine ContinuousOn.comp (g := g) (f := fun s : ℝ => τ + s * Complex.I) hg (by fun_prop) ?_
      intro s hs
      have him : (τ + s * Complex.I).im = τ.im + s := by simp
      show 0 < (τ + s * Complex.I).im
      rw [him]
      linarith [mem_Ioi.mp hs]
    exact hc'.aestronglyMeasurable measurableSet_Ioi
  have hae : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0:ℝ))),
      ‖g (τ + s * Complex.I)‖ ≤ A * (Real.exp (-c * s) * (1 + s) ^ m) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => hbound s hs)
  have hint : IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) :=
    Integrable.mono' (hw.const_mul A) hmeas hae
  refine ⟨hint, ?_⟩
  calc ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖
      ≤ ∫ s in Ioi (0:ℝ), A * (Real.exp (-c * s) * (1 + s) ^ m) :=
        norm_integral_le_of_norm_le (hw.const_mul A) hae
    _ = A * ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := integral_const_mul A _

end GlobalTheory
end

open MeasureTheory Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ), ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) ∧
      ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖ ≤
        K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m * ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := by
  atlas_forward_decl GlobalTheory.vertRay_integral_expPow_bound
end

section
section
open MeasureTheory Filter Topology Set

namespace GlobalTheory

theorem top_side_integral_tendsto_zero : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ), ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    Tendsto (fun S : ℝ => ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop (𝓝 0) := by
  intro g K c m τ _ hc hg hτ
  set B : ℝ := 2 + ‖τ - Complex.I‖ with hB
  have hB0 : 0 ≤ B := by positivity
  set F : ℝ → ℝ := fun S => |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m with hF
  have hpt : ∀ S : ℝ, 0 ≤ S → ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖g (Complex.I + t * (τ - Complex.I) + S * Complex.I)‖ ≤ F S := by
    intro S hS t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    set z := Complex.I + t * (τ - Complex.I) + S * Complex.I with hz
    have him : z.im = 1 + t * (τ.im - 1) + S := by
      simp [hz]
    have him1 : 1 + S ≤ z.im := by
      rw [him]; nlinarith
    have hnorm : 1 + ‖z‖ ≤ B + S := by
      have h1 : ‖z‖ ≤ ‖Complex.I‖ + ‖(t:ℂ) * (τ - Complex.I)‖ + ‖(S:ℂ) * Complex.I‖ := by
        rw [hz]; exact norm_add₃_le
      have h2 : ‖(t:ℂ) * (τ - Complex.I)‖ ≤ ‖τ - Complex.I‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        exact mul_le_of_le_one_left (norm_nonneg _) ht1
      have h3 : ‖(S:ℂ) * Complex.I‖ = S := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
      rw [Complex.norm_I] at h1
      rw [hB]; linarith
    have he : Real.exp (-c * z.im) ≤ Real.exp (-c * (1 + S)) := Real.exp_le_exp.mpr (by nlinarith)
    have hp : (1 + ‖z‖) ^ m ≤ (B + S) ^ m := pow_le_pow_left₀ (by positivity) hnorm m
    calc ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m := hg z (by linarith)
      _ ≤ |K| * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m := by
          gcongr; exact le_abs_self K
      _ ≤ |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m :=
          mul_le_mul (mul_le_mul_of_nonneg_left he (abs_nonneg K)) hp (by positivity) (by positivity)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun S : ℝ => c * (B + S)) atTop atTop :=
      (tendsto_atTop_add_const_left atTop B tendsto_id).const_mul_atTop hc
    have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp h1).const_mul
      (|K| * (c ^ m)⁻¹ * Real.exp (c * B - c))
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards with S
    have hcm : c ^ m ≠ 0 := pow_ne_zero _ hc.ne'
    have hexp : Real.exp (c * B - c) * Real.exp (-(c * (B + S))) = Real.exp (-c * (1 + S)) := by
      rw [← Real.exp_add]; ring_nf
    simp only [Function.comp, hF]
    rw [mul_pow]
    calc |K| * (c ^ m)⁻¹ * Real.exp (c * B - c) * (c ^ m * (B + S) ^ m * Real.exp (-(c * (B + S))))
        = |K| * (Real.exp (c * B - c) * Real.exp (-(c * (B + S)))) * ((c ^ m)⁻¹ * c ^ m) * (B + S) ^ m := by ring
      _ = |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m := by rw [hexp, inv_mul_cancel₀ hcm, mul_one]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0:ℝ)] with S hS
  have := intervalIntegral.norm_integral_le_of_norm_le_const (hpt S hS)
  rwa [sub_zero, abs_one, mul_one] at this

end GlobalTheory
end

open MeasureTheory Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_integral_shifted_segment_zero_of_exp_decay : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ), ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    Tendsto (fun S : ℝ => ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop (𝓝 0) := by
  atlas_forward_decl GlobalTheory.top_side_integral_tendsto_zero
end

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
open MeasureTheory Filter Topology Set

namespace GlobalTheory.HeckeFamilyMatrices

theorem eichler_tail_cauchy (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) (hc : 0 < c)
    (hb : ∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) (hτ : 1 ≤ τ.im) :
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in Ioi (0:ℝ), g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)) := by
  have hI : (1:ℝ) ≤ Complex.I.im := by simp
  have i1 := (GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le g K c m Complex.I hg.continuousOn hc hb hI).1
  have i2 := (GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le g K c m τ hg.continuousOn hc hb hτ).1
  have t1 := intervalIntegral_tendsto_integral_Ioi 0 i1 tendsto_id
  have t2 := intervalIntegral_tendsto_integral_Ioi 0 i2 tendsto_id
  have t3 := GlobalTheory.T.tendsto_integral_shifted_segment_zero_of_exp_decay g K c m τ hg.continuousOn hc hb hτ
  have hlim : Tendsto (fun S : ℝ => Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop
      (𝓝 (Complex.I * (∫ s in Ioi (0:ℝ), g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)) + (τ - Complex.I) * 0)) :=
    ((t1.const_mul _).sub (t2.const_mul _)).add (t3.const_mul _)
  rw [mul_zero, add_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_ge_atTop 0] with S hS
  exact GlobalTheory.T.integral_segment_eq_parallelogram_sides g τ S hg (by linarith) hS

theorem eichler_tail : ∀ (w : ℕ) (F : ℍ → ℂ) (C c : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → 0 < c →
    (∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) →
    ∃ (L : ℂ[X]) (C' : ℝ), ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w,
      ‖(eichler w F τ - L).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
  intro w F C c hF hc hbd
  set G : ℂ → ℂ := F ∘ UpperHalfPlane.ofComplex with hGdef
  have hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} := UpperHalfPlane.mdifferentiable_iff.mp hF
  let g : ℕ → ℂ → ℂ := fun j z => G z * (-z) ^ (w - j)
  have hg : ∀ j, DifferentiableOn ℂ (g j) {z : ℂ | 0 < z.im} := fun j =>
    hG.mul ((differentiable_id.neg.pow _).differentiableOn)
  have hgb : ∀ j, ∀ z : ℂ, 1 ≤ z.im → ‖g j z‖ ≤ C * Real.exp (-c * z.im) * (1 + ‖z‖) ^ w := by
    intro j z hz
    have hz0 : 0 < z.im := by linarith
    have h1 : ‖G z‖ ≤ C * Real.exp (-c * z.im) := by
      have := hbd ⟨z, hz0⟩ hz
      simpa [hGdef, Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz0] using this
    have h2 : ‖(-z) ^ (w - j)‖ ≤ (1 + ‖z‖) ^ w := by
      rw [norm_pow, norm_neg]
      calc ‖z‖ ^ (w - j) ≤ (1 + ‖z‖) ^ (w - j) := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        _ ≤ (1 + ‖z‖) ^ w := pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Nat.sub_le _ _)
    calc ‖g j z‖ = ‖G z‖ * ‖(-z) ^ (w - j)‖ := norm_mul _ _
      _ ≤ C * Real.exp (-c * z.im) * (1 + ‖z‖) ^ w :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  set M : ℝ := ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ w
  set Lp : ℂ[X] := ∑ j ∈ Finset.range (w + 1),
      Polynomial.C ((w.choose j : ℂ) * (Complex.I * ∫ s in Ioi (0:ℝ), g j (Complex.I + s * Complex.I))) * X ^ j
    with hLp
  refine ⟨Lp, 2 ^ w * C * M, ?_⟩
  intro τ hτ j hj
  have hj' : j ∈ Finset.range (w + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hc1 : (eichler w F τ).coeff j = (w.choose j : ℂ) * ∫ t in (0 : ℝ)..1,
      (F ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I) := by
    rw [eichler, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hb; rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
    · intro h; exact absurd hj' h
  have hc2 : Lp.coeff j = (w.choose j : ℂ) * (Complex.I * ∫ s in Ioi (0:ℝ), g j (Complex.I + s * Complex.I)) := by
    rw [hLp, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hb; rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
    · intro h; exact absurd hj' h
  have hint : (∫ t in (0 : ℝ)..1,
      (F ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) =
      ((τ : ℂ) - Complex.I) * ∫ t in (0:ℝ)..1, g j (Complex.I + t * ((τ : ℂ) - Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; simp only [g, hGdef]; ring
  have hL5 := eichler_tail_cauchy (g j) C c w (τ : ℂ) (hg j) hc (hgb j) hτ
  have hkey : (eichler w F τ - Lp).coeff j = -((w.choose j : ℂ) * Complex.I * ∫ s in Ioi (0:ℝ), g j ((τ : ℂ) + s * Complex.I)) := by
    rw [Polynomial.coeff_sub, hc1, hc2, hint, hL5]; ring
  rw [hkey, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one]
  have hb3 := (GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le (g j) C c w (τ : ℂ) (hg j).continuousOn hc (hgb j) hτ).2
  have hch : ‖(w.choose j : ℂ)‖ ≤ 2 ^ w := by
    rw [Complex.norm_natCast]; exact_mod_cast Nat.choose_le_two_pow w j
  have hnn : 0 ≤ C * Real.exp (-c * τ.im) * (1 + ‖(τ:ℂ)‖) ^ w * M := (norm_nonneg _).trans hb3
  calc ‖(w.choose j : ℂ)‖ * ‖∫ s in Ioi (0:ℝ), g j ((τ : ℂ) + s * Complex.I)‖
      ≤ 2 ^ w * (C * Real.exp (-c * τ.im) * (1 + ‖(τ:ℂ)‖) ^ w * M) :=
        mul_le_mul hch hb3 (norm_nonneg _) (by positivity)
    _ = 2 ^ w * C * M * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
        ring

end GlobalTheory.HeckeFamilyMatrices
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerIntegralFromI_tail_exponential_decay : ∀ (w : ℕ) (F : ℍ → ℂ) (C c : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → 0 < c → (∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) → ∃ (L : ℂ[X]) (C' : ℝ), ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(eichler w F τ - L).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
  atlas_forward_decl GlobalTheory.HeckeFamilyMatrices.eichler_tail
end

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerLimit

theorem trunc_mem (w : ℕ) (R : ℂ[X]) :
    (∑ j ∈ Finset.range (w + 1), C (R.coeff j) * X ^ j) ∈ degreeLT ℂ (w + 1) := by
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast Finset.mem_range.1 hj

theorem trunc_coeff (w : ℕ) (R : ℂ[X]) {j : ℕ} (hj : j ≤ w) :
    (∑ i ∈ Finset.range (w + 1), C (R.coeff i) * X ^ i).coeff j = R.coeff j := by
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_of_le hj]

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  unfold eichler
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast Finset.mem_range.1 hj

theorem bound_rate {F : ℍ → ℂ} {C c c' : ℝ} (hc : c' ≤ c)
    (hF : ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) :
    ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ max C 0 * Real.exp (-c' * τ.im) := by
  intro τ hτ
  refine (hF τ hτ).trans ?_
  have h1 : Real.exp (-c * τ.im) ≤ Real.exp (-c' * τ.im) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg (sub_nonneg.2 hc) (τ.im_pos.le)])
  calc C * Real.exp (-c * τ.im) ≤ max C 0 * Real.exp (-c * τ.im) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (-c' * τ.im) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

theorem polySlash_eichler_limit : ∀ (k : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]) (σ : SL(2, ℤ)) (Cf cf Ch ch : ℝ), 2 ≤ k → 0 < cf → 0 < ch → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[(k : ℤ)] σ) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h ∣[(k : ℤ)] σ) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(f ∣[(k : ℤ)] σ) τ‖ ≤ Cf * Real.exp (-cf * τ.im)) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(h ∣[(k : ℤ)] σ) τ‖ ≤ Ch * Real.exp (-ch * τ.im)) → p ∈ degreeLT ℂ (k - 1) → ∃ (Q : ℂ[X]) (C' c : ℝ), Q ∈ degreeLT ℂ (k - 2 + 1) ∧ 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ k - 2, ‖(slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p) - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (k - 2) := by
  intro k f h p σ Cf cf Ch ch hk hcf hch hf hh hfs hhs bf bh _hp
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk f hf σ
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk h hh σ
  have hc : 0 < min cf ch := lt_min hcf hch
  obtain ⟨Lf, Kf, hLf⟩ := GlobalTheory.T.eichlerIntegralFromI_tail_exponential_decay (k - 2) (f ∣[(k : ℤ)] σ) (max Cf 0) (min cf ch) hfs hc
    (bound_rate (min_le_left _ _) bf)
  obtain ⟨Lh, Kh, hLh⟩ := GlobalTheory.T.eichlerIntegralFromI_tail_exponential_decay (k - 2) (h ∣[(k : ℤ)] σ) (max Ch 0) (min cf ch) hhs hc
    (bound_rate (min_le_right _ _) bh)
  set R : ℂ[X] := Lf + C1 - (Lh + C2).map (starRingEnd ℂ) - slP (k - 2) (mat σ) p with hR
  refine ⟨∑ j ∈ Finset.range (k - 2 + 1), C (R.coeff j) * X ^ j, Kf + Kh, min cf ch,
    trunc_mem _ _, hc, ?_⟩
  intro τ hτ j hj
  have key : slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p)
      = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C1
        - (eichler (k - 2) (h ∣[(k : ℤ)] σ) τ + C2).map (starRingEnd ℂ) - slP (k - 2) (mat σ) p := by
    rw [map_sub, map_sub, hC1, ← (GlobalTheory.T.polyDegreeSlashAction_right_action_properties (k - 2) (mat σ) 1 _ (eichler_mem _ _ _)).2.2.2, hC2]
  have e1 := hLf τ hτ j hj
  have e2 := hLh τ hτ j hj
  rw [coeff_sub] at e1 e2
  rw [coeff_sub, key, trunc_coeff _ _ hj, hR]
  simp only [coeff_sub, coeff_add, coeff_map, map_add]
  calc _ = ‖((eichler (k - 2) (f ∣[(k : ℤ)] σ) τ).coeff j - Lf.coeff j)
        - (starRingEnd ℂ) ((eichler (k - 2) (h ∣[(k : ℤ)] σ) τ).coeff j - Lh.coeff j)‖ := by
          congr 1; rw [map_sub]; ring
    _ ≤ _ := norm_sub_le _ _
    _ = ‖(eichler (k - 2) (f ∣[(k : ℤ)] σ) τ).coeff j - Lf.coeff j‖
        + ‖(eichler (k - 2) (h ∣[(k : ℤ)] σ) τ).coeff j - Lh.coeff j‖ := by rw [Complex.norm_conj]
    _ ≤ _ := by rw [add_mul, add_mul]; exact add_le_add e1 e2

end GlobalTheory.EichlerLimit
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerPeriodPolynomial_limit_at_cusp : ∀ (k : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]) (σ : SL(2, ℤ)) (Cf cf Ch ch : ℝ), 2 ≤ k → 0 < cf → 0 < ch → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[(k : ℤ)] σ) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h ∣[(k : ℤ)] σ) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(f ∣[(k : ℤ)] σ) τ‖ ≤ Cf * Real.exp (-cf * τ.im)) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(h ∣[(k : ℤ)] σ) τ‖ ≤ Ch * Real.exp (-ch * τ.im)) → p ∈ degreeLT ℂ (k - 1) → ∃ (Q : ℂ[X]) (C' c : ℝ), Q ∈ degreeLT ℂ (k - 2 + 1) ∧ 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ k - 2, ‖(slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p) - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (k - 2) := by
  atlas_forward_decl GlobalTheory.EichlerLimit.polySlash_eichler_limit
end

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.QConst

open Filter Topology

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private theorem natDegree_lt_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) :
    p.natDegree < w + 1 := by
  rcases eq_or_ne p 0 with rfl | h
  · simp
  · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem norm_eval_le_sum_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (x : ℂ) : ‖p.eval x‖ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j‖ * ‖x‖ ^ j := by
  rw [eval_eq_sum_range' (natDegree_lt_of_mem_degreeLT hp)]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [norm_mul, norm_pow]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem eq_C_of_eval_add_natCast_eq {Q : ℂ[X]} {n : ℕ} (hn : 0 < n)
    (hQ : ∀ x : ℂ, Q.eval (x + n) = Q.eval x) : Q = C (Q.coeff 0) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hroot : ∀ k : ℕ, IsRoot (Q - C (Q.eval 0)) ((k : ℂ) * n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : ((k + 1 : ℕ) : ℂ) * n = (k : ℂ) * n + n := by push_cast; ring
      simp only [IsRoot.def, eval_sub, eval_C] at ih ⊢
      rw [hk, hQ]
      exact ih
  have hinf : Set.Infinite {x | IsRoot (Q - C (Q.eval 0)) x} :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ) * n)
      (fun a b hab => by exact_mod_cast mul_right_cancel₀ hn' hab) hroot
  rw [coeff_zero_eq_eval_zero]
  exact sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem tendsto_exp_neg_mul_mul_add_pow_zero {c : ℝ} (hc : 0 < c) (b : ℝ) (m : ℕ) :
    Tendsto (fun y : ℝ => Real.exp (-c * y) * (b + y) ^ m) atTop (𝓝 0) := by
  have h1 := ((isLittleO_pow_exp_pos_mul_atTop m hc).comp_tendsto
    (tendsto_atTop_add_const_left atTop b tendsto_id)).tendsto_div_nhds_zero
  have h2 := h1.const_mul (Real.exp (c * b))
  rw [mul_zero] at h2
  refine h2.congr fun y => ?_
  simp only [Function.comp_apply, id]
  rw [mul_add, Real.exp_add, neg_mul, Real.exp_neg]
  field_simp

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in

theorem _root_.GlobalTheory.HeckeFamilyMatrices.QConst.qconst : ∀ (w n : ℕ) (V : ℍ → ℂ[X]) (Q : ℂ[X]) (C' c : ℝ), 0 < n → 0 < c → Q ∈ degreeLT ℂ (w + 1) →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    Q = C (Q.coeff 0) := by
  intro w n V Q C' c hn hc hQ hV hper h
  have hT : _root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := by
    unfold _root_.GlobalTheory.HeckeFamilyMatrices.mat
    exact ModularGroup.coe_T_zpow _
  have htrans : ∀ (τ : ℍ) (x : ℂ),
      (V τ).eval x = (V (ModularGroup.T ^ (n : ℤ) • τ)).eval (x + n) := by
    intro τ x
    rw [← hper τ, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ x (hV _) (by rw [hT]; simp), hT]
    simp
  have hbound : ∀ τ : ℍ, 1 ≤ τ.im → ∀ b : ℝ, 1 + ‖(τ : ℂ)‖ ≤ b → ∀ x : ℂ,
      ‖(V τ - Q).eval x‖ ≤ C' * Real.exp (-c * τ.im) * b ^ w *
        ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j := by
    intro τ hτ b hb x
    have hC' : 0 ≤ C' := by
      have h0 := h τ hτ 0 (Nat.zero_le _)
      have : 0 < Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by positivity
      nlinarith [norm_nonneg ((V τ - Q).coeff 0)]
    rw [Finset.mul_sum]
    refine (norm_eval_le_sum_of_mem_degreeLT (Submodule.sub_mem _ (hV τ) hQ) x).trans
      (Finset.sum_le_sum fun j hj => ?_)
    have hj' : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact mul_le_mul_of_nonneg_right ((h τ hτ j hj').trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb w)
        (mul_nonneg hC' (Real.exp_pos _).le))) (by positivity)
  refine eq_C_of_eval_add_natCast_eq hn fun x => ?_
  set M : ℝ := ∑ j ∈ Finset.range (w + 1), ‖x + n‖ ^ j + ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j
  have hest : ∀ y : ℝ, 1 ≤ y → ‖Q.eval (x + n) - Q.eval x‖ ≤
      C' * M * (Real.exp (-c * y) * ((1 + n) + y) ^ w) := by
    intro y hy
    let τ : ℍ := ⟨(y : ℂ) * Complex.I, by simp; linarith⟩
    have hτim : τ.im = y := by simp [τ, UpperHalfPlane.im]
    have hτn : ‖(τ : ℂ)‖ = y := by
      simp [τ, abs_of_pos (show (0 : ℝ) < y by linarith)]
    have hτ'c : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = τ + n := by
      rw [ModularGroup.coe_T_zpow_smul_eq]
      simp
    have hτ'im : (ModularGroup.T ^ (n : ℤ) • τ).im = y := by
      rw [← hτim, ← UpperHalfPlane.coe_im, hτ'c, ← UpperHalfPlane.coe_im]
      simp
    have hτ'n : 1 + ‖((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ)‖ ≤ (1 + n) + y := by
      rw [hτ'c]
      have := norm_add_le (τ : ℂ) (n : ℂ)
      rw [hτn, Complex.norm_natCast] at this
      linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 := hbound τ (by rw [hτim]; exact hy) ((1 + n) + y) (by rw [hτn]; linarith) x
    have e2 := hbound _ (by rw [hτ'im]; exact hy) ((1 + n) + y) hτ'n (x + n)
    rw [hτim] at e1
    rw [hτ'im] at e2
    have hsplit : Q.eval (x + n) - Q.eval x =
        (V τ - Q).eval x - (V (ModularGroup.T ^ (n : ℤ) • τ) - Q).eval (x + n) := by
      simp only [eval_sub, htrans τ x]
      ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    simp only [M]
    ring
  have hlim := (tendsto_exp_neg_mul_mul_add_pow_zero hc (1 + n) w).const_mul (C' * M)
  rw [mul_zero] at hlim
  have hle : ‖Q.eval (x + n) - Q.eval x‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hest⟩)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

end GlobalTheory.HeckeFamilyMatrices.QConst
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_poly_of_periodic_slash_family_const : ∀ (w n : ℕ) (V : ℍ → ℂ[X]) (Q : ℂ[X]) (C' c : ℝ), 0 < n → 0 < c → Q ∈ degreeLT ℂ (w + 1) → (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) → Q = C (Q.coeff 0) := by
  atlas_forward_decl GlobalTheory.HeckeFamilyMatrices.QConst.qconst
end

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem evalDiag_T_step (w n : ℕ) (V : ℍ → ℂ[X]) (hV : ∀ τ, V τ ∈ degreeLT ℂ (w + 1))
    (hT : ∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ)
    (τ : ℍ) :
    (V (ModularGroup.T ^ (n : ℤ) • τ)).eval ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  have hm : mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := ModularGroup.coe_T_zpow _
  have hc : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (τ : ℂ) + n := by
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
    push_cast; ring
  rw [← hT τ, eval_polySlash w _ _ _ (hV _), hm, hc]
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    simp
  · rw [hm]
    simp

theorem evalDiag_T_invariant : ∀ (w n : ℕ) (V : ℍ → ℂ[X]), (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → ∀ (m : ℤ) (τ : ℍ), (V (ModularGroup.T ^ ((n : ℤ) * m) • τ)).eval ((ModularGroup.T ^ ((n : ℤ) * m) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  intro w n V hV hT m
  have step := evalDiag_T_step w n V hV hT
  simp only [zpow_mul]
  induction m using Int.induction_on with
  | zero => intro τ; simp
  | succ k ih =>
    intro τ
    rw [zpow_add_one, mul_smul, ih, step]
  | pred k ih =>
    intro τ
    have e : (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ) - 1) • τ =
        (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ)) • ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ) := by
      rw [zpow_sub_one, mul_smul]
    rw [e, ih, ← step ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ), smul_inv_smul]

end GlobalTheory.HeckeFamilyMatrices
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalDiag_polyValued_invariant_translation_T_zpow_mul : ∀ (w n : ℕ) (V : ℍ → ℂ[X]), (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → ∀ (m : ℤ) (τ : ℍ), (V (ModularGroup.T ^ ((n : ℤ) * m) • τ)).eval ((ModularGroup.T ^ ((n : ℤ) * m) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  atlas_forward_decl GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant
end

section
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

open Filter Topology

private lemma norm_eval_add_C_le_of_coeff_le (w : ℕ) (a z : ℂ) (p : ℂ[X]) (K e : ℝ) (hK : 0 ≤ K)
    (he : 0 ≤ e) (hp : p ∈ degreeLT ℂ (w + 1))
    (hc : ∀ j ≤ w, ‖p.coeff j‖ ≤ K * e * (1 + ‖z‖) ^ w) :
    ‖(p + C a).eval z‖ ≤ ‖a‖ + (w + 1) * (K * e * (1 + ‖z‖) ^ (2 * w)) := by
  have hdeg : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hp)
  rw [eval_add, eval_C, eval_eq_sum_range' hdeg]
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hterm : ∀ j ∈ Finset.range (w + 1),
      ‖p.coeff j * z ^ j‖ ≤ K * e * (1 + ‖z‖) ^ (2 * w) := by
    intro j hj
    have hjw : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [norm_mul, norm_pow]
    have h1 : ‖z‖ ^ j ≤ (1 + ‖z‖) ^ w :=
      (pow_le_pow_left₀ (norm_nonneg z) (by linarith) j).trans (pow_le_pow_right₀ hz1 hjw)
    calc ‖p.coeff j‖ * ‖z‖ ^ j ≤ (K * e * (1 + ‖z‖) ^ w) * (1 + ‖z‖) ^ w :=
          mul_le_mul (hc j hjw) h1 (by positivity) (by positivity)
      _ = K * e * (1 + ‖z‖) ^ (2 * w) := by ring
  calc ‖∑ j ∈ Finset.range (w + 1), p.coeff j * z ^ j + a‖
      ≤ ‖∑ j ∈ Finset.range (w + 1), p.coeff j * z ^ j‖ + ‖a‖ := norm_add_le _ _
    _ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j * z ^ j‖ + ‖a‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (w + 1), K * e * (1 + ‖z‖) ^ (2 * w) + ‖a‖ := by
        gcongr with j hj; exact hterm j hj
    _ = ‖a‖ + (w + 1) * (K * e * (1 + ‖z‖) ^ (2 * w)) := by simp; ring

theorem strip_eval_decay : ∀ (w n : ℕ) (a : ℂ) (V : ℍ → ℂ[X]) (C' c : ℝ), 1 ≤ w → 0 < c →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    ∀ ε > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → 0 ≤ τ.re → τ.re ≤ n →
      ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) < ε := by
  intro w n a V C' c hw hc hV hcoef ε hε
  set K := max C' 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  have hwpos : (0 : ℝ) < (w : ℝ) / 2 := by
    have : (1 : ℝ) ≤ w := by exact_mod_cast hw
    linarith
  have h1 : Tendsto (fun y : ℝ => ‖a‖ * y ^ (-(w : ℝ) / 2)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hwpos).const_mul ‖a‖
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun y => ?_)
    simp only [neg_div]
  have h2 : Tendsto (fun y : ℝ => (w + 1) * (K * 4 ^ w) * (y ^ (2 * w) / Real.exp (c * y)))
      atTop (𝓝 0) := by
    have := ((isLittleO_pow_exp_pos_mul_atTop (2 * w) hc).tendsto_div_nhds_zero).const_mul
      ((w + 1) * (K * 4 ^ w))
    rwa [mul_zero] at this
  have e1 := h1.eventually (gt_mem_nhds (half_pos hε))
  have e2 := h2.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨A0, hA0⟩ := eventually_atTop.1 (e1.and e2)
  refine ⟨max A0 (1 + n), fun τ hA hre hren => ?_⟩
  have hpos : 0 < τ.im := τ.im_pos
  have hy0 : A0 ≤ τ.im := le_trans (le_max_left _ _) hA
  have hyn : 1 + (n : ℝ) ≤ τ.im := le_trans (le_max_right _ _) hA
  have hy1 : 1 ≤ τ.im := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨hf1, hf2⟩ := hA0 τ.im hy0
  have hz : ‖(τ : ℂ)‖ ≤ n + τ.im := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hr : |(τ : ℂ).re| ≤ n := by
      rw [UpperHalfPlane.coe_re, abs_of_nonneg hre]; exact hren
    have hi : |(τ : ℂ).im| = τ.im := by
      rw [UpperHalfPlane.coe_im, abs_of_pos hpos]
    linarith
  have hcb : ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ K * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
    intro j hj
    refine (hcoef τ hy1 j hj).trans ?_
    gcongr
    exact le_max_left _ _
  have hmem : V τ - C a ∈ degreeLT ℂ (w + 1) :=
    Submodule.sub_mem _ (hV τ)
      (mem_degreeLT.2 (lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos w)))
  have hmain := norm_eval_add_C_le_of_coeff_le w a (τ : ℂ) (V τ - C a) K (Real.exp (-c * τ.im)) hK
    (Real.exp_pos _).le hmem hcb
  rw [sub_add_cancel] at hmain
  have hnz : 1 + ‖(τ : ℂ)‖ ≤ 2 * τ.im := by linarith
  have hpow : (1 + ‖(τ : ℂ)‖) ^ (2 * w) ≤ 4 ^ w * τ.im ^ (2 * w) := by
    calc (1 + ‖(τ : ℂ)‖) ^ (2 * w) ≤ (2 * τ.im) ^ (2 * w) :=
          pow_le_pow_left₀ (by positivity) hnz _
      _ = 4 ^ w * τ.im ^ (2 * w) := by rw [mul_pow, pow_mul]; norm_num
  have hT : (w + 1) * (K * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (2 * w))
      ≤ (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
    rw [neg_mul, Real.exp_neg]
    calc (w + 1) * (K * (Real.exp (c * τ.im))⁻¹ * (1 + ‖(τ : ℂ)‖) ^ (2 * w))
        ≤ (w + 1) * (K * (Real.exp (c * τ.im))⁻¹ * (4 ^ w * τ.im ^ (2 * w))) := by gcongr
      _ = (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
        rw [div_eq_mul_inv]; ring
  have hT0 : 0 ≤ (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by positivity
  have hr0 : 0 ≤ τ.im ^ (-(w : ℝ) / 2) := Real.rpow_nonneg hpos.le _
  have hr1 : τ.im ^ (-(w : ℝ) / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hy1 ?_
    have : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    linarith
  calc ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2)
      ≤ (‖a‖ + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)))
          * τ.im ^ (-(w : ℝ) / 2) := by gcongr; linarith
    _ = ‖a‖ * τ.im ^ (-(w : ℝ) / 2)
          + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im))
            * τ.im ^ (-(w : ℝ) / 2) := by ring
    _ ≤ ‖a‖ * τ.im ^ (-(w : ℝ) / 2)
          + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
        exact add_le_add le_rfl (mul_le_of_le_one_right hT0 hr1)
    _ < ε / 2 + ε / 2 := add_lt_add hf1 hf2
    _ = ε := add_halves ε

end GlobalTheory.HeckeFamilyMatrices
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strip_eval_polynomial_decay_mul_im_rpow : ∀ (w n : ℕ) (a : ℂ) (V : ℍ → ℂ[X]) (C' c : ℝ), 1 ≤ w → 0 < c → (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) → ∀ ε > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → 0 ≤ τ.re → τ.re ≤ n → ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) < ε := by
  atlas_forward_decl GlobalTheory.HeckeFamilyMatrices.strip_eval_decay
end

section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Decay

theorem per_exists : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → ∀ σ : SL(2, ℤ), ∃ n : ℕ, 0 < n ∧ σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ ∈ Γ := by
  intro Γ hΓ σ
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero (σ * ModularGroup.T * σ⁻¹)
  refine ⟨n, hn, ?_⟩
  have : (σ * ModularGroup.T * σ⁻¹) ^ n = σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ := by
    rw [zpow_natCast, conj_pow]
  rwa [← this]

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  unfold eichler
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  have := Finset.mem_range.1 hj
  exact_mod_cast this

theorem per_cov (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (U : ℍ → ℂ[X]) (hU : ∀ τ, U τ ∈ degreeLT ℂ (w + 1))
    (heq : ∀ (γ : Γ) (τ : ℍ), slP w (mat γ) (U ((γ : SL(2, ℤ)) • τ)) = U τ) (σ : SL(2, ℤ)) (n : ℕ)
    (hγ : σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ ∈ Γ) (τ : ℍ) :
    slP w (mat (ModularGroup.T ^ (n : ℤ))) (slP w (mat σ) (U (σ • (ModularGroup.T ^ (n : ℤ) • τ)))) =
      slP w (mat σ) (U (σ • τ)) := by
  have h1 := heq ⟨_, hγ⟩ (σ • τ)
  have h2 : ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) • σ • τ = σ • (ModularGroup.T ^ (n : ℤ) • τ) := by
    simp only [← mul_smul]; congr 1; group
  rw [h2] at h1
  rw [← h1]
  have hm' : ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ = σ * ModularGroup.T ^ (n : ℤ) := by
    simp only [Subgroup.coe_mk]; group
  have e1 : slP w (mat (ModularGroup.T ^ (n : ℤ))) (slP w (mat σ) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))) =
      slP w (mat (σ * ModularGroup.T ^ (n : ℤ))) (U (σ • ModularGroup.T ^ (n : ℤ) • τ)) := by
    rw [show mat (σ * ModularGroup.T ^ (n : ℤ)) = mat σ * mat (ModularGroup.T ^ (n : ℤ)) from
      Matrix.SpecialLinearGroup.coe_mul _ _, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w _ _ _ (hU _)).2.1]
  have e2 : slP w (mat σ) (slP w (mat ((⟨_, hγ⟩ : Γ) : SL(2, ℤ))) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))) =
      slP w (mat (((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ)) (U (σ • ModularGroup.T ^ (n : ℤ) • τ)) := by
    rw [show mat (((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ) = mat ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * mat σ from
      Matrix.SpecialLinearGroup.coe_mul _ _, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w _ _ _ (hU _)).2.1]
  rw [e1, e2, hm']

theorem decay_at_cusp : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)) (p : ℂ[X]), p ∈ degreeLT ℂ (k - 1) → (∀ (γ : Γ) (τ : ℍ), slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ) - (eichler (k - 2) ⇑h ((γ : SL(2, ℤ)) • τ)).map (starRingEnd ℂ) - p) = eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p) → ∀ σ : SL(2, ℤ), Filter.Tendsto (fun τ : ℍ => ‖(eichler (k - 2) ⇑f (σ • τ) - (eichler (k - 2) ⇑h (σ • τ)).map (starRingEnd ℂ) - p).eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) UpperHalfPlane.atImInfty (nhds 0) := by
  intro Γ k hΓ hk f h p hp hequiv σ
  have hk2 : 2 ≤ k := by omega
  set w := k - 2 with hw
  have hw1 : 1 ≤ w := by omega
  set U : ℍ → ℂ[X] := fun τ =>
    eichler w ⇑f τ - (eichler w ⇑h τ).map (starRingEnd ℂ) - p with hU
  have hpw : p ∈ degreeLT ℂ (w + 1) := by
    rwa [show w + 1 = k - 1 by omega]
  have hUdeg : ∀ τ, U τ ∈ degreeLT ℂ (w + 1) := by
    intro τ
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (eichler_mem w _ τ) ?_) hpw
    have h0 := eichler_mem w (⇑h) τ
    rw [mem_degreeLT] at h0 ⊢
    exact (degree_map_le).trans_lt h0
  set V : ℍ → ℂ[X] := fun τ => slP w (mat σ) (U (σ • τ)) with hV
  have hVdeg : ∀ τ, V τ ∈ degreeLT ℂ (w + 1) := fun τ => (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat σ) 1 _ (hUdeg _)).1
  have hexp : (-((k : ℝ) - 2) / 2) = -(w : ℝ) / 2 := by
    rw [hw, Nat.cast_sub hk2]; push_cast; ring
  have hfun : (fun τ : ℍ => ‖(U (σ • τ)).eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) =
      fun τ => ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
    funext τ; rw [hexp]; exact GlobalTheory.T.norm_eval_smul_mul_im_rpow_polyDegreeSlash w σ (U (σ • τ)) τ (hUdeg _)
  change Filter.Tendsto (fun τ : ℍ => ‖(U (σ • τ)).eval ((σ • τ : ℍ) : ℂ)‖ *
    (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) _ _
  rw [hfun]
  obtain ⟨n, hn, hγ⟩ := per_exists Γ hΓ σ
  have hVper : ∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ :=
    fun τ => per_cov Γ w U hUdeg hequiv σ n hγ τ
  obtain ⟨hfd, Cf, cf, hcf, hfb⟩ := GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay Γ k hΓ f σ
  obtain ⟨hhd, Ch, ch, hch, hhb⟩ := GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay Γ k hΓ h σ
  obtain ⟨Q, C', c, hQ, hc, hQb⟩ := GlobalTheory.T.eichlerPeriodPolynomial_limit_at_cusp k (⇑f) (⇑h) p σ Cf cf Ch ch hk2 hcf hch
    (CuspFormClass.holo f) (CuspFormClass.holo h) hfd hhd hfb hhb hp
  have hQb' : ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w :=
    hQb
  have hQc := GlobalTheory.T.limit_poly_of_periodic_slash_family_const w n V Q C' c hn hc hQ hVdeg hVper hQb'
  rw [hQc] at hQb'
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨A, hA⟩ := GlobalTheory.T.strip_eval_polynomial_decay_mul_im_rpow w n (Q.coeff 0) V C' c hw1 hc hVdeg hQb' ε hε
  refine (atImInfty_mem _).2 ⟨A, fun τ hτ => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set m : ℤ := -⌊τ.re / n⌋ with hm
  set τ' : ℍ := ModularGroup.T ^ ((n : ℤ) * m) • τ with hτ'
  have hτ'v : τ' = ((((n : ℤ) * m : ℤ)) : ℝ) +ᵥ τ := modular_T_zpow_smul τ _
  have hre : τ'.re = τ.re + n * m := by
    rw [hτ'v]; simp [add_comm]
  have him : τ'.im = τ.im := by
    rw [hτ'v]; simp
  have hg := GlobalTheory.T.evalDiag_polyValued_invariant_translation_T_zpow_mul w n V hVdeg hVper m τ
  have hfl1 : (⌊τ.re / n⌋ : ℝ) ≤ τ.re / n := Int.floor_le _
  have hfl2 : τ.re / n < ⌊τ.re / n⌋ + 1 := Int.lt_floor_add_one _
  have hr1 : 0 ≤ τ'.re := by
    rw [hre, hm]; push_cast
    have := (le_div_iff₀ hnR).1 hfl1
    nlinarith
  have hr2 : τ'.re ≤ n := by
    rw [hre, hm]; push_cast
    have := (div_lt_iff₀ hnR).1 hfl2
    nlinarith
  have := hA τ' (him ▸ hτ) hr1 hr2
  rw [hg, him] at this
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (by positivity)]
  exact this

end GlobalTheory.HeckeFamilyMatrices.Decay
end
