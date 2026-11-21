import Mathlib
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompletedLFunctionNeZeroOfReNonpos

section
section
namespace GlobalTheory.CompanionTheory.ExplChi

open Complex DirichletCharacter

theorem hasDerivAt_Gammaℝ_of_ne {z : ℂ} (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) :
    HasDerivAt Gammaℝ
      (Gammaℝ z * (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2)) z := by
  have hΓ : Gamma (z / 2) ≠ 0 := Gamma_ne_zero hz
  have hd : DifferentiableAt ℂ Gamma (z / 2) := differentiableAt_Gamma _ hz
  have h1 : HasDerivAt (fun w : ℂ => Gamma (w / 2)) (deriv Gamma (z / 2) * (1 / 2)) z :=
    hd.hasDerivAt.comp z ((hasDerivAt_id z).div_const 2)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-z / 2) * Complex.log Real.pi * (-1 / 2)) z :=
    ((hasDerivAt_id z).neg.div_const 2).const_cpow (Or.inl hpi)
  have h3 := h2.mul h1
  have hfun : Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Gamma (w / 2) := by
    funext w; rw [Gammaℝ_def]
  have hval : Gammaℝ z * (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2) =
      (Real.pi : ℂ) ^ (-z / 2) * Complex.log Real.pi * (-1 / 2) * Gamma (z / 2) +
        (Real.pi : ℂ) ^ (-z / 2) * (deriv Gamma (z / 2) * (1 / 2)) := by
    rw [Gammaℝ_def, digamma_def, logDeriv_apply, Complex.ofReal_log Real.pi_pos.le]
    field_simp
  rw [hval, hfun]
  exact h3

theorem Gammaℝ_ne_zero_of_ne {z : ℂ} (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) : Gammaℝ z ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Gammaℝ_def]
  exact mul_ne_zero (by rw [Ne, cpow_eq_zero_iff]; exact fun h => hpi h.1) (Gamma_ne_zero hz)

theorem completed_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hN : N ≠ 1)
    (hχ : χ ≠ 1) {a : ℂ} (ha : χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) {z : ℂ}
    (hz : ∀ n : ℕ, (z + a) / 2 ≠ -(n : ℂ)) (hL : LFunction χ z ≠ 0) :
    completedLFunction χ z ≠ 0 ∧
      deriv (completedLFunction χ) z / completedLFunction χ z =
        -(Real.log Real.pi : ℂ) / 2 + digamma ((z + a) / 2) / 2 +
          deriv (LFunction χ) z / LFunction χ z := by
  have hgf : ∀ w, gammaFactor χ w = Gammaℝ (w + a) := by
    intro w
    rcases ha with ⟨he, rfl⟩ | ⟨ho, rfl⟩
    · rw [he.gammaFactor_def, add_zero]
    · rw [ho.gammaFactor_def]
  have hG : HasDerivAt (fun w : ℂ => Gammaℝ (w + a)) _ z :=
    (hasDerivAt_Gammaℝ_of_ne hz).comp_add_const z a
  have hGne : Gammaℝ (z + a) ≠ 0 := Gammaℝ_ne_zero_of_ne hz
  have hprod : ∀ w, Gammaℝ (w + a) ≠ 0 →
      completedLFunction χ w = Gammaℝ (w + a) * LFunction χ w := by
    intro w hw
    have h := LFunction_eq_completed_div_gammaFactor χ w (Or.inr hN)
    rw [hgf] at h
    rw [h]
    field_simp
  have hev : completedLFunction χ =ᶠ[nhds z] fun w => Gammaℝ (w + a) * LFunction χ w := by
    filter_upwards [hG.continuousAt.eventually_ne hGne] with w hw using hprod w hw
  have hder : HasDerivAt (fun w => Gammaℝ (w + a) * LFunction χ w) _ z :=
    hG.mul (differentiable_LFunction hχ z).hasDerivAt
  have hne : completedLFunction χ z ≠ 0 := by
    rw [hprod z hGne]; exact mul_ne_zero hGne hL
  refine ⟨hne, ?_⟩
  rw [hev.deriv_eq, hder.deriv, hprod z hGne]
  field_simp

theorem logDeriv_LFunction_functional_equation :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N → χ.IsPrimitive →
      ∀ a : ℂ, (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) → ∀ s : ℂ,
        (∀ n : ℕ, (s + a) / 2 ≠ -(n : ℂ)) → (∀ n : ℕ, (1 - s + a) / 2 ≠ -(n : ℂ)) →
        DirichletCharacter.LFunction χ s ≠ 0 →
        DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 →
        deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
          -((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((1 - s + a) / 2) / 2 -
            Complex.digamma ((s + a) / 2) / 2 -
            deriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) /
              DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  intro N _ χ hN hp a ha s hs1 hs2 hL1 hL2
  have hN1 : N ≠ 1 := hN.ne'
  have hχ : χ ≠ 1 := by
    rintro rfl
    rw [isPrimitive_def, conductor_one] at hp
    exact hN1 hp.symm
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have ha' : χ⁻¹.Even ∧ a = 0 ∨ χ⁻¹.Odd ∧ a = 1 := by
    rcases ha with ⟨he, h⟩ | ⟨ho, h⟩
    · refine Or.inl ⟨?_, h⟩
      rw [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', he, inv_one]
    · refine Or.inr ⟨?_, h⟩
      rw [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', ho]
      norm_num
  obtain ⟨A0, eA⟩ := completed_logDeriv χ hN1 hχ ha hs1 hL1
  obtain ⟨B0, eB⟩ := completed_logDeriv χ⁻¹ hN1 hχi ha' hs2 hL2
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set W := rootNumber χ with hW
  have hfe : ∀ w, completedLFunction χ w =
      (N : ℂ) ^ ((1 : ℂ) / 2 - w) * W * completedLFunction χ⁻¹ (1 - w) := by
    intro w
    have h := hp.completedLFunction_one_sub (1 - w)
    rw [sub_sub_cancel] at h
    rw [h]
    congr 3
    ring
  have hc : HasDerivAt (fun w : ℂ => (N : ℂ) ^ ((1 : ℂ) / 2 - w))
      ((N : ℂ) ^ ((1 : ℂ) / 2 - s) * Complex.log N * (-1)) s :=
    ((hasDerivAt_id s).const_sub ((1 : ℂ) / 2)).const_cpow (Or.inl hN0)
  have hB : HasDerivAt (fun w : ℂ => completedLFunction χ⁻¹ (1 - w))
      (-deriv (completedLFunction χ⁻¹) (1 - s)) s :=
    ((differentiable_completedLFunction hχi (1 - s)).hasDerivAt).comp_const_sub 1 s
  have hT := (hc.mul_const W).mul hB
  have hD : deriv (completedLFunction χ) s =
      (N : ℂ) ^ ((1 : ℂ) / 2 - s) * Complex.log N * (-1) * W * completedLFunction χ⁻¹ (1 - s) +
        (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W * (-deriv (completedLFunction χ⁻¹) (1 - s)) := by
    rw [funext hfe]
    exact hT.deriv
  have hA : completedLFunction χ s =
      (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W * completedLFunction χ⁻¹ (1 - s) := hfe s
  have hcW : (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W ≠ 0 := by
    intro h
    rw [h, zero_mul] at hA
    exact A0 hA
  have hlog : deriv (completedLFunction χ) s / completedLFunction χ s =
      -Complex.log N -
        deriv (completedLFunction χ⁻¹) (1 - s) / completedLFunction χ⁻¹ (1 - s) := by
    have hBB : completedLFunction χ⁻¹ (1 - s) *
        (deriv (completedLFunction χ⁻¹) (1 - s) / completedLFunction χ⁻¹ (1 - s)) =
        deriv (completedLFunction χ⁻¹) (1 - s) := mul_div_cancel₀ _ B0
    rw [hD, hA, div_eq_iff (mul_ne_zero hcW B0)]
    linear_combination ((N : ℂ) ^ ((1 : ℂ) / 2 - s) * W) * hBB
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have l1 : ((Real.log (N / Real.pi) : ℝ) : ℂ) = Complex.log N - (Real.log Real.pi : ℂ) := by
    rw [Real.log_div hNpos.ne' Real.pi_ne_zero, ofReal_sub, Complex.ofReal_log hNpos.le,
      ofReal_natCast]
  rw [eA, eB] at hlog
  rw [l1]
  linear_combination hlog

end GlobalTheory.CompanionTheory.ExplChi
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichlet_logDeriv_reflection_formula : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N → χ.IsPrimitive → ∀ a : ℂ, (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) → ∀ s : ℂ, (∀ n : ℕ, (s + a) / 2 ≠ -(n : ℂ)) → (∀ n : ℕ, (1 - s + a) / 2 ≠ -(n : ℂ)) → DirichletCharacter.LFunction χ s ≠ 0 → DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 → deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s = -((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((1 - s + a) / 2) / 2 - Complex.digamma ((s + a) / 2) / 2 - deriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) / DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ExplChi.logDeriv_LFunction_functional_equation
end

section
open Complex Filter Topology Metric Set
open scoped Nat Real

namespace GlobalTheory.CompanionTheory.DigammaLimit

theorem euler_seq_le_Gamma {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) ^ x * (n ! : ℝ) / ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) ≤ Real.Gamma x := by
  have hfe : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp]
    rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have h := Real.BohrMollerup.ge_logGammaSeq (f := Real.log ∘ Real.Gamma)
    Real.convexOn_log_Gamma hfe hx hn
  have hf1 : (Real.log ∘ Real.Gamma) 1 = 0 := by simp [Real.Gamma_one]
  rw [hf1, zero_add] at h
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hP : ∀ j ∈ Finset.range (n + 1), (0 : ℝ) < x + j := fun j _ => by positivity
  have hPpos : 0 < ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) := Finset.prod_pos hP
  have hlog : Real.log ((n : ℝ) ^ x * (n ! : ℝ) / ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ))) =
      Real.BohrMollerup.logGammaSeq x n := by
    rw [Real.log_div (by positivity) hPpos.ne', Real.log_mul (by positivity) hfac.ne',
      Real.log_rpow hn0, Real.log_prod (fun j hj => (hP j hj).ne')]
    rfl
  rw [← hlog] at h
  exact (Real.log_le_log_iff (by positivity) (Real.Gamma_pos_of_pos hx)).1 h

theorem norm_GammaSeq_le {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq w n‖ ≤ Real.Gamma w.re := by
  refine le_trans ?_ (euler_seq_le_Gamma hw hn)
  rw [GammaSeq, norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    norm_prod, Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (by positivity) (Finset.prod_pos fun j _ => by positivity)
  apply Finset.prod_le_prod (fun j _ => by positivity)
  intro j _
  have := Complex.abs_re_le_norm (w + j)
  simp only [add_re, natCast_re] at this
  exact (le_abs_self _).trans this

theorem add_natCast_ne_zero {z : ℂ} (hz : 0 < z.re) (j : ℕ) : z + (j : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp only [add_re, natCast_re, zero_re] at h1
  have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem ne_neg_natCast_of_re_pos {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -(m : ℂ) := by
  intro h
  exact add_natCast_ne_zero hz m (by rw [h]; ring)

theorem differentiableAt_GammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    DifferentiableAt ℂ (fun w => GammaSeq w n) z := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hP : ∀ j ∈ Finset.range (n + 1), z + (j : ℂ) ≠ 0 := fun j _ => add_natCast_ne_zero hz j
  simp only [GammaSeq]
  refine DifferentiableAt.div ?_ ?_ (Finset.prod_ne_zero_iff.2 hP)
  · exact (differentiableAt_id.const_cpow (Or.inl hn')).mul_const _
  · exact DifferentiableAt.fun_finset_prod fun j _ => by fun_prop

theorem logDeriv_GammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun w => GammaSeq w n) z =
      ((Real.log n : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hP : ∀ j ∈ Finset.range (n + 1), z + (j : ℂ) ≠ 0 := fun j _ => add_natCast_ne_zero hz j
  have hd1 : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w) ((n : ℂ) ^ z * Complex.log n * 1) z :=
    (hasDerivAt_id z).const_cpow (Or.inl hn')
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hcp : (n : ℂ) ^ z ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hn']
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) z :=
    DifferentiableAt.fun_finset_prod fun j _ => by fun_prop
  have e1 : (fun w => GammaSeq w n) =
      fun w => ((n : ℂ) ^ w * (n ! : ℂ)) / ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) := rfl
  have l1 : logDeriv (fun w : ℂ => (n : ℂ) ^ w) z = Complex.log n := by
    rw [logDeriv_apply, hd1.deriv]
    field_simp
  have l2 : ∀ j : ℕ, logDeriv (fun w : ℂ => w + (j : ℂ)) z = 1 / (z + (j : ℂ)) := by
    intro j
    rw [logDeriv_apply]
    simp
  rw [e1, logDeriv_div (f := fun w : ℂ => (n : ℂ) ^ w * (n ! : ℂ))
      (g := fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) z
      (mul_ne_zero hcp hfac) (Finset.prod_ne_zero_iff.2 hP)
      (hd1.differentiableAt.mul_const _) hd2,
    logDeriv_mul (f := fun w : ℂ => (n : ℂ) ^ w) (g := fun _ : ℂ => (n ! : ℂ)) z hcp hfac
      hd1.differentiableAt (differentiableAt_const _),
    logDeriv_prod (f := fun (j : ℕ) (w : ℂ) => w + (j : ℂ)) hP (fun j _ => by fun_prop),
    l1, logDeriv_const, Pi.zero_apply, add_zero, Complex.natCast_log]
  simp only [l2]

theorem tendsto_deriv_GammaSeq {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => deriv (fun w => GammaSeq w n) z) atTop (𝓝 (deriv Gamma z)) := by
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = z.re / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; positivity
  obtain ⟨U, hU_def⟩ : ∃ U : Set ℂ, U = {w : ℂ | 0 < w.re} := ⟨_, rfl⟩
  have hUo : IsOpen U := by
    rw [hU_def]
    exact isOpen_lt continuous_const Complex.continuous_re
  have hre : ∀ w ∈ closedBall z r, z.re / 2 ≤ w.re ∧ w.re ≤ 3 * z.re / 2 := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hw
    have h2 := Complex.abs_re_le_norm (w - z)
    have h3 : |w.re - z.re| ≤ r := by
      have := h2.trans h1
      simpa only [sub_re] using this
    rw [abs_le] at h3
    constructor <;> linarith [h3.1, h3.2]
  have hsub : closedBall z r ⊆ U := fun w hw => by
    have := (hre w hw).1
    rw [hU_def]
    show 0 < w.re
    linarith
  have hGd : DifferentiableOn ℂ Gamma U := fun w hw => by
    rw [hU_def] at hw
    exact (differentiableAt_Gamma w (ne_neg_natCast_of_re_pos hw)).differentiableWithinAt
  have hFd : ∀ n : ℕ, n ≠ 0 → DifferentiableOn ℂ (fun w => GammaSeq w n) U := fun n hn w hw => by
    rw [hU_def] at hw
    exact (differentiableAt_GammaSeq hw hn).differentiableWithinAt
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Icc (z.re / 2) (3 * z.re / 2), ‖Real.Gamma x‖ ≤ M := by
    refine isCompact_Icc.exists_bound_of_continuousOn fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    refine (Real.differentiableAt_Gamma fun m h => ?_).continuousAt.continuousWithinAt
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hbd : ∀ n : ℕ, n ≠ 0 → ∀ w ∈ closedBall z r, ‖GammaSeq w n‖ ≤ M := by
    intro n hn w hw
    have h1 := hre w hw
    have h0 : 0 < w.re := by linarith [h1.1]
    exact (norm_GammaSeq_le h0 hn).trans ((le_abs_self _).trans (hM _ ⟨h1.1, h1.2⟩))
  have hc : ∀ θ, circleMap z r θ ∈ closedBall z r := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere z hr.le θ)
  have key : Tendsto (fun n : ℕ => ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • GammaSeq w n) atTop
      (𝓝 (∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • Gamma w)) := by
    simp only [circleIntegral]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => r * ((r ^ 2)⁻¹ * M)) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [eventually_ne_atTop 0] with n hn
      apply Continuous.aestronglyMeasurable
      have hcont : Continuous fun θ : ℝ => GammaSeq (circleMap z r θ) n :=
        (hFd n hn).continuousOn.comp_continuous (continuous_circleMap z r)
          (fun θ => hsub (hc θ))
      have h0 : ∀ θ, (circleMap z r θ - z) ^ 2 ≠ 0 := fun θ =>
        pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hr.ne'))
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 r).mul continuous_const).smul
        (((((continuous_circleMap z r).sub continuous_const).pow 2).inv₀ h0).smul hcont)
    · filter_upwards [eventually_ne_atTop 0] with n hn
      refine Eventually.of_forall fun θ _ => ?_
      simp only [deriv_circleMap, circleMap_sub_center, norm_smul, norm_mul, norm_circleMap_zero,
        Complex.norm_I, norm_inv, norm_pow, abs_of_pos hr, mul_one]
      gcongr
      exact hbd n hn _ (hc θ)
    · refine Eventually.of_forall fun θ _ => ?_
      exact ((GammaSeq_tendsto_Gamma _).const_smul _).const_smul _
  have h2 := key.const_smul ((2 * π * I : ℂ)⁻¹)
  have e : cderiv r Gamma z = deriv Gamma z := cderiv_eq_deriv hUo hGd hr hsub
  rw [← e]
  refine Tendsto.congr' ?_ h2
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact cderiv_eq_deriv hUo (hFd n hn) hr hsub

theorem tendsto_log_sub_sum_digamma : ∀ z : ℂ, 0 < z.re →
    Filter.Tendsto (fun n : ℕ => ((Real.log n : ℝ) : ℂ) -
      ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ))) Filter.atTop (nhds (Complex.digamma z)) := by
  intro z hz
  have h1 := (tendsto_deriv_GammaSeq hz).div (GammaSeq_tendsto_Gamma z)
    (Gamma_ne_zero_of_re_pos hz)
  rw [digamma_def, logDeriv_apply]
  refine Tendsto.congr' ?_ h1
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [← logDeriv_GammaSeq hz hn, logDeriv_apply]
  rfl

end GlobalTheory.CompanionTheory.DigammaLimit
end

section
section
namespace GlobalTheory.CompanionTheory.DigammaBound

open Finset

lemma add_half_le_norm (z : ℂ) (hz : 1 / 2 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    x + 1 / 2 ≤ ‖z + (x : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (z + (x : ℂ))
  have h2 : (z + (x : ℂ)).re = z.re + x := by simp
  rw [h2] at h
  have := le_abs_self (z.re + x)
  linarith

lemma term_eq (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ =
      ‖z‖ / (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) hk
  have h2 : z + (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hN
    linarith
  have h1 : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    rw [← hc]
    exact_mod_cast Nat.succ_ne_zero k
  rw [hc]
  have : 1 / (((k : ℝ) + 1 : ℝ) : ℂ) - 1 / (z + (((k : ℝ) + 1 : ℝ) : ℂ)) =
      z / ((((k : ℝ) + 1 : ℝ) : ℂ) * (z + (((k : ℝ) + 1 : ℝ) : ℂ))) := by
    field_simp
    ring
  rw [this, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]

lemma term_le_two (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ 2 * ((k : ℝ) + 1)⁻¹ := by
  rw [term_eq z hz k]
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) ha.le
  have hz' : ‖z‖ ≤ ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ + ((k : ℝ) + 1) := by
    have h := norm_sub_le (z + (((k : ℝ) + 1 : ℝ) : ℂ)) (((k : ℝ) + 1 : ℝ) : ℂ)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg ha.le] at h
    exact h
  have hNpos : 0 < ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ := by linarith
  rw [div_le_iff₀ (by positivity)]
  have : 2 * ((k : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) =
      2 * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ := by
    field_simp
  rw [this]
  linarith

lemma term_le_sq (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ ‖z‖ / ((k : ℝ) + 1) ^ 2 := by
  rw [term_eq z hz k]
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) ha.le
  apply div_le_div_of_nonneg_left (norm_nonneg z) (by positivity)
  nlinarith

lemma sum_terms_le (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (hn : M ≤ n) :
    ∑ i ∈ range n, ‖1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))‖ ≤
      2 * ∑ i ∈ range M, ((i : ℝ) + 1)⁻¹ + ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [sub_self, mul_zero, add_zero, mul_sum]
    exact sum_le_sum fun i _ => term_le_two z hz i
  | succ n hn ih =>
    rw [sum_range_succ]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    have ht := term_le_sq z hz n
    have htel : ‖z‖ / ((n : ℝ) + 1) ^ 2 ≤ ‖z‖ * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      have : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = ((n : ℝ) * ((n : ℝ) + 1))⁻¹ := by
        field_simp
        ring
      rw [this]
      apply inv_anti₀ (by positivity)
      nlinarith
    push_cast
    nlinarith [ih, ht, htel]

lemma harmonic_cast (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ := by
  simp [harmonic]

lemma partial_le (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (hzM : ‖z‖ ≤ M)
    (n : ℕ) (hn : M ≤ n) :
    ‖((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ))‖ ≤
      6 + 2 * Real.log M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hn1 : 1 ≤ n := hM.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set H : ℝ := ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ with hH
  have hlow : Real.log n ≤ H := by
    have h := log_add_one_le_harmonic n
    rw [harmonic_cast] at h
    have h2 : Real.log n ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log hn0 (by linarith)
    push_cast at h
    linarith
  have hup : H ≤ 1 + Real.log n := by
    have h := harmonic_le_one_add_log n
    rw [harmonic_cast] at h
    exact h
  have hHc : ((H : ℝ) : ℂ) = ∑ i ∈ range n, 1 / ((i : ℂ) + 1) := by
    rw [hH]
    push_cast
    simp
  have hdecomp : ((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ)) =
      ((Real.log n - H : ℝ) : ℂ) +
        ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))) - 1 / z := by
    rw [sum_range_succ', sum_sub_distrib, ← hHc]
    push_cast
    simp only [add_zero]
    ring
  have h1 : ‖((Real.log n - H : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h2 : ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ ≤
      2 * (1 + Real.log M) + 1 := by
    refine (norm_sum_le _ _).trans ((sum_terms_le z hz M hM n hn).trans ?_)
    have hHM := harmonic_le_one_add_log M
    rw [harmonic_cast] at hHM
    have h3 : ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) ≤ 1 := by
      have h4 : ‖z‖ * (1 / (M : ℝ)) ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_one hM0).2 hzM
      have h5 : 0 ≤ ‖z‖ * (1 / (n : ℝ)) := by positivity
      rw [mul_sub]
      linarith
    linarith
  have h3 : ‖1 / z‖ ≤ 2 := by
    have hzn : 1 / 2 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
    linarith
  rw [hdecomp]
  calc _ ≤ ‖((Real.log n - H : ℝ) : ℂ) +
        ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ + ‖1 / z‖ := norm_sub_le _ _
    _ ≤ ‖((Real.log n - H : ℝ) : ℂ)‖ +
        ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ + ‖1 / z‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 6 + 2 * Real.log M := by linarith

theorem digamma_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by
  refine ⟨11, by norm_num, fun z hz => ?_⟩
  have hzn : 1 / 2 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
  set M : ℕ := ⌈‖z‖⌉₊ + 1 with hMdef
  have hM : 1 ≤ M := by omega
  have hzM : ‖z‖ ≤ M := by
    rw [hMdef]
    push_cast
    linarith [Nat.le_ceil ‖z‖]
  have hMle : (M : ℝ) ≤ ‖z‖ + 2 := by
    rw [hMdef]
    push_cast
    linarith [Nat.ceil_lt_add_one (norm_nonneg z)]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hlogM : Real.log M ≤ Real.log (‖z‖ + 2) := Real.log_le_log hM0 hMle
  have hlim := (GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma z (by linarith)).norm
  have hbd : ‖Complex.digamma z‖ ≤ 6 + 2 * Real.log M :=
    le_of_tendsto hlim ((Filter.eventually_ge_atTop M).mono fun n hn =>
      partial_le z hz M hM hzM n hn)
  have hL : (2 : ℝ) / 3 ≤ Real.log (‖z‖ + 2) := by
    have h2 : Real.log 2 ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  linarith

end GlobalTheory.CompanionTheory.DigammaBound
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digamma_log_bound_right_half_plane : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DigammaBound.digamma_bound
end

section
section
namespace GlobalTheory.CompanionTheory.DigammaLeft

theorem digamma_sub_digamma_one_sub (w : ℂ) (hw : ∀ n : ℤ, w ≠ n) :
    Complex.digamma w - Complex.digamma (1 - w) =
      -((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)) := by
  have hw1 : ∀ m : ℕ, w ≠ -(m : ℂ) := fun m h => hw (-(m : ℤ)) (by rw [h]; push_cast; rfl)
  have hw2 : ∀ m : ℕ, 1 - w ≠ -(m : ℂ) := fun m h => hw ((m : ℤ) + 1) (by
    push_cast
    linear_combination -h)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : Complex.sin (Real.pi * w) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    apply hw k
    apply mul_left_cancel₀ hpi
    rw [hk]; ring
  have ha : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw1
  have hb : Complex.Gamma (1 - w) ≠ 0 := Complex.Gamma_ne_zero hw2
  have hG1 : HasDerivAt Complex.Gamma (deriv Complex.Gamma w) w :=
    (Complex.differentiableAt_Gamma w hw1).hasDerivAt
  have hG2' : HasDerivAt Complex.Gamma (deriv Complex.Gamma (1 - w)) (1 - w) :=
    (Complex.differentiableAt_Gamma (1 - w) hw2).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => 1 - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have hG2 : HasDerivAt (fun z : ℂ => Complex.Gamma (1 - z))
      (deriv Complex.Gamma (1 - w) * (-1)) w :=
    HasDerivAt.comp w hG2' hlin
  have hprod := hG1.mul hG2
  have hsin : HasDerivAt (fun z : ℂ => Complex.sin (Real.pi * z))
      (Complex.cos (Real.pi * w) * Real.pi) w := by
    have h1 : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) Real.pi w := by
      simpa using (hasDerivAt_id w).const_mul (Real.pi : ℂ)
    exact (Complex.hasDerivAt_sin _).comp w h1
  have hquot := (hasDerivAt_const w (Real.pi : ℂ)).div hsin hs
  have hfun : ((fun _ : ℂ => (Real.pi : ℂ)) / fun z : ℂ => Complex.sin (Real.pi * z)) =
      (Complex.Gamma * fun z : ℂ => Complex.Gamma (1 - z)) := by
    funext z
    simp only [Pi.mul_apply, Pi.div_apply]
    exact (Complex.Gamma_mul_Gamma_one_sub z).symm
  rw [hfun] at hquot
  have huniq := hprod.unique hquot
  have hab : Complex.Gamma w * Complex.Gamma (1 - w) = Real.pi / Complex.sin (Real.pi * w) :=
    Complex.Gamma_mul_Gamma_one_sub w
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply]
  have e1 : deriv Complex.Gamma w / Complex.Gamma w -
      deriv Complex.Gamma (1 - w) / Complex.Gamma (1 - w) =
      (deriv Complex.Gamma w * Complex.Gamma (1 - w) +
        Complex.Gamma w * (deriv Complex.Gamma (1 - w) * -1)) /
      (Complex.Gamma w * Complex.Gamma (1 - w)) := by
    field_simp
    ring
  rw [e1, huniq, hab]
  field_simp
  ring

theorem sq_norm_sin (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.sin_eq, Complex.normSq_apply]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re]
  have h1 := Real.sin_sq_add_cos_sq z.re
  have h2 := Real.cosh_sq z.im
  linear_combination Real.sin z.re ^ 2 * h2 + Real.sinh z.im ^ 2 * h1

theorem sq_norm_cos (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.cos_eq, Complex.normSq_apply]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re]
  have h1 := Real.sin_sq_add_cos_sq z.re
  have h2 := Real.cosh_sq z.im
  linear_combination Real.cos z.re ^ 2 * h2 + Real.sinh z.im ^ 2 * h1

theorem norm_cos_le_of_im (z : ℂ) (h : 1 ≤ |z.im|) : ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by
  have h1 : 1 ≤ |Real.sinh z.im| := by
    rw [Real.abs_sinh]
    exact h.trans (Real.self_le_sinh_iff.mpr (abs_nonneg _))
  have h2 : 1 ≤ Real.sinh z.im ^ 2 := by
    rw [← sq_abs]; nlinarith
  have hc := sq_norm_cos z
  have hs := sq_norm_sin z
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, hc, hs]
  nlinarith [Real.cos_sq_le_one z.re, sq_nonneg (Real.sin z.re)]

theorem norm_cos_le_of_re (z : ℂ) (k : ℤ) (h : z.re = Real.pi * ((k : ℝ) / 2 + 1 / 4)) :
    ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by
  have hc := sq_norm_cos z
  have hs := sq_norm_sin z
  have h2 : Real.cos (2 * z.re) = 0 := by
    have : 2 * z.re = (k : ℝ) * Real.pi + Real.pi / 2 := by rw [h]; ring
    rw [this, Real.cos_add_pi_div_two, Real.sin_int_mul_pi, neg_zero]
  have h3 : Real.cos z.re ^ 2 = Real.sin z.re ^ 2 := by
    have := Real.cos_sq' z.re
    rw [Real.cos_two_mul] at h2
    nlinarith
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, hc, hs, h3]
  nlinarith [sq_nonneg (Real.sin z.re), sq_nonneg (Real.sinh z.im)]

theorem norm_digamma_le_left :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re ≤ 1 / 4 →
      (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) →
      ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2) := by
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.digamma_log_bound_right_half_plane
  refine ⟨2 * C + 10, by positivity, fun w hre halt => ?_⟩
  have hint : ∀ n : ℤ, w ≠ n := by
    intro n hn
    rcases halt with h | ⟨k, hk⟩
    · rw [hn] at h
      norm_num at h
    · have h1 : (n : ℝ) = (k : ℝ) / 2 + 1 / 4 := by
        rw [← hk, hn]; simp
      have h4 : (4 * n : ℝ) = 2 * k + 1 := by linarith
      have h5 : 4 * n = 2 * k + 1 := by exact_mod_cast h4
      omega
  have hcot : ‖Complex.cos (Real.pi * w)‖ ≤ 2 * ‖Complex.sin (Real.pi * w)‖ := by
    rcases halt with h | ⟨k, hk⟩
    · apply norm_cos_le_of_im
      have him : ((Real.pi : ℂ) * w).im = Real.pi * w.im := by simp
      rw [him, abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    · apply norm_cos_le_of_re _ k
      simp [hk]
  have hcotn : ‖(Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)‖ ≤
      2 * Real.pi := by
    rcases eq_or_ne (Complex.sin (Real.pi * w)) 0 with h0 | h0
    · rw [h0]
      simp [Real.pi_pos.le]
    · have hpos : 0 < ‖Complex.sin (Real.pi * w)‖ := norm_pos_iff.mpr h0
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        div_le_iff₀ hpos]
      nlinarith [Real.pi_pos]
  have hrefl := digamma_sub_digamma_one_sub w hint
  have hdecomp : Complex.digamma w = Complex.digamma (1 - w) +
      -((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)) := by
    rw [← hrefl]; ring
  have hbd := hb (1 - w) (by simp; linarith)
  have hw0 := norm_nonneg w
  have hL : Real.log 2 ≤ Real.log (‖w‖ + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h1w : ‖1 - w‖ ≤ 1 + ‖w‖ := by simpa using norm_sub_le 1 w
  have hl2 : Real.log (‖1 - w‖ + 2) ≤ 2 * Real.log (‖w‖ + 2) := by
    have h2 : Real.log (‖1 - w‖ + 2) ≤ Real.log ((‖w‖ + 2) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rwa [Real.log_pow, Nat.cast_ofNat] at h2
  have hpi : 2 * Real.pi ≤ 10 * Real.log (‖w‖ + 2) := by
    linarith [Real.pi_lt_d2, Real.log_two_gt_d9]
  have hmul : C * Real.log (‖1 - w‖ + 2) ≤ C * (2 * Real.log (‖w‖ + 2)) :=
    mul_le_mul_of_nonneg_left hl2 hC.le
  calc ‖Complex.digamma w‖
      ≤ ‖Complex.digamma (1 - w)‖ +
          ‖(Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)‖ := by
        rw [hdecomp]
        simpa using norm_add_le (Complex.digamma (1 - w))
          (-((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)))
    _ ≤ (2 * C + 10) * Real.log (‖w‖ + 2) := by nlinarith

end GlobalTheory.CompanionTheory.DigammaLeft
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digamma_log_bound_left_region : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re ≤ 1 / 4 → (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) → ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left
end

section
open Complex DirichletCharacter ArithmeticFunction

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft

theorem bound_right : ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ), 3 / 2 ≤ s.re → ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ B := by
  have hsum : Summable fun n => ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) (3 / 2) n‖ :=
    (LSeriesSummable_vonMangoldt (s := 3 / 2) (by norm_num)).norm
  refine ⟨∑' n, ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) (3 / 2) n‖,
    tsum_nonneg fun _ => norm_nonneg _, ?_⟩
  intro N _ χ s hs2
  have hs : 1 < s.re := by linarith
  have h1 := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs, neg_div] at h1
  rw [← norm_neg]
  refine HasSum.norm_le_of_bounded h1 hsum.hasSum fun n => ?_
  refine (LSeries.norm_term_le s (g := fun n => (vonMangoldt n : ℂ)) ?_).trans
    (LSeries.norm_term_le_of_re_le_re _ (by simpa using hs2) n)
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem main : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N →
    χ.IsPrimitive → ∀ s : ℂ, s.re ≤ -(1/2 : ℝ) →
    (1 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -((k : ℝ) + 1/2)) →
    DirichletCharacter.LFunction χ s ≠ 0 ∧
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
      ≤ C * Real.log (N * (‖s‖ + 2)) := by
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.T.digamma_log_bound_right_half_plane
  obtain ⟨C₂, hC₂, H₂⟩ := GlobalTheory.T.digamma_log_bound_left_region
  obtain ⟨B, hB, HB⟩ := bound_right
  refine ⟨4 + C₁ + C₂ + B, by positivity, ?_⟩
  intro N _ χ hN hχ s hre hs

  have hint : ∀ m : ℤ, s ≠ (m : ℂ) := by
    rintro m rfl
    rcases hs with h | ⟨k, hk⟩
    · simp at h
      linarith
    · have hk' : (m : ℝ) = -((k : ℝ) + 1 / 2) := by simpa using hk
      have h2 : ((2 * m + 2 * k + 1 : ℤ) : ℝ) = 0 := by
        push_cast
        linarith
      have h3 : (2 * m + 2 * k + 1 : ℤ) = 0 := by exact_mod_cast h2
      omega
  have hL : LFunction χ s ≠ 0 := by
    intro h0
    obtain ⟨⟨n, hn⟩, -⟩ := GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ s (by linarith) h0
    exact hint (-(n : ℤ)) (by rw [hn]; push_cast; rfl)
  refine ⟨hL, ?_⟩
  have hre' : (3 / 2 : ℝ) ≤ (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  have hL' : LFunction χ⁻¹ (1 - s) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inr fun h => by rw [h] at hre'; norm_num at hre')
      (by linarith)
  obtain ⟨a, hpar, m, hm, rfl⟩ : ∃ a : ℂ, (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) ∧
      ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ a = (m : ℂ) := by
    rcases χ.even_or_odd with h | h
    · exact ⟨0, Or.inl ⟨h, rfl⟩, 0, Or.inl rfl, by simp⟩
    · exact ⟨1, Or.inr ⟨h, rfl⟩, 1, Or.inr rfl, by simp⟩
  have hm0 : (0 : ℝ) ≤ m := by rcases hm with rfl | rfl <;> simp
  have hm1 : (m : ℝ) ≤ 1 := by rcases hm with rfl | rfl <;> simp
  have hnorm : ‖(m : ℂ)‖ ≤ 1 := by rcases hm with rfl | rfl <;> simp
  have hz : (1 / 2 : ℝ) ≤ ((1 - s + (m : ℂ)) / 2).re := by
    have : ((1 - s + (m : ℂ)) / 2).re = (1 - s.re + m) / 2 := by simp
    rw [this]
    linarith
  have hwre : ((s + (m : ℂ)) / 2).re = (s.re + m) / 2 := by simp
  have hwim : ((s + (m : ℂ)) / 2).im = s.im / 2 := by simp
  have hc1 : ∀ n : ℕ, (s + (m : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n h
    refine hint (-2 * n - m) ?_
    push_cast
    linear_combination 2 * h
  have hc2 : ∀ n : ℕ, (1 - s + (m : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n h
    have h1 := congrArg Complex.re h
    rw [show ((1 - s + (m : ℂ)) / 2).re = (1 - s.re + m) / 2 by simp] at h1
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp at h1
    linarith
  rw [GlobalTheory.T.dirichlet_logDeriv_reflection_formula N χ hN hχ _ hpar s hc1 hc2 hL hL']

  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsn : 1 / 2 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    have h2 := neg_abs_le s.re
    linarith
  have hpos : 0 < (N : ℝ) * (‖s‖ + 2) := by positivity
  set X := Real.log (N * (‖s‖ + 2)) with hX
  have hX1 : 1 ≤ X := by
    rw [hX, Real.le_log_iff_exp_le hpos]
    have := Real.exp_one_lt_d9
    nlinarith
  have hlogN : Real.log N ≤ X := by
    refine Real.log_le_log (by linarith) ?_
    nlinarith [norm_nonneg s]
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hpi3 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  have t1 : ‖(((Real.log (N / Real.pi) : ℝ)) : ℂ)‖ ≤ 4 * X := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      Real.log_div (by linarith) Real.pi_ne_zero, abs_le]
    constructor <;> linarith
  have t2 : ‖digamma ((1 - s + (m : ℂ)) / 2)‖ ≤ C₁ * X := by
    refine (H₁ _ hz).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₁.le
    refine Real.log_le_log (by positivity) ?_
    have : ‖(1 - s + (m : ℂ)) / 2‖ ≤ (2 + ‖s‖) / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      have h1 := norm_add_le (1 - s) (m : ℂ)
      have h2 := norm_sub_le (1 : ℂ) s
      simp only [norm_one] at h2
      linarith
    nlinarith [norm_nonneg s]
  have t3 : ‖digamma ((s + (m : ℂ)) / 2)‖ ≤ C₂ * X := by
    have hcond : 1 / 2 ≤ |((s + (m : ℂ)) / 2).im| ∨
        ∃ k : ℤ, ((s + (m : ℂ)) / 2).re = (k : ℝ) / 2 + 1 / 4 := by
      rcases hs with h | ⟨k, hk⟩
      · left
        rw [hwim, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        linarith
      · right
        refine ⟨m - k - 1, ?_⟩
        rw [hwre, hk]
        push_cast
        ring
    refine (H₂ _ (by rw [hwre]; linarith) hcond).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₂.le
    refine Real.log_le_log (by positivity) ?_
    have : ‖(s + (m : ℂ)) / 2‖ ≤ (‖s‖ + 1) / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      have h1 := norm_add_le s (m : ℂ)
      linarith
    nlinarith [norm_nonneg s]
  have t4 := HB N χ⁻¹ (1 - s) hre'
  have hh : ∀ x y z u : ℂ, ‖-x - y / 2 - z / 2 - u‖ ≤ ‖x‖ + ‖y‖ / 2 + ‖z‖ / 2 + ‖u‖ := by
    intro x y z u
    have e : -x - y / 2 - z / 2 - u = -x + -(y / 2) + -(z / 2) + -u := by ring
    rw [e]
    refine (norm_add₄_le).trans ?_
    simp [norm_neg, norm_div]
  refine (hh _ _ _ _).trans ?_
  nlinarith

end GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft
end
