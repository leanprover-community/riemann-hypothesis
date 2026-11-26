module

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Meromorphic.Order
import TauCeti.Analysis.LaplaceTransform.Landau
public import Lib.Analytic.EntireLFunction

/-!
# Landau's lemma for polar transforms

This file applies Tau Ceti's Landau theorem for Laplace transforms
(`TauCeti.integrableOn_cexp_neg_mul_smul_ofReal_of_ae_nonneg`) to transforms satisfying
`New.IsPolar`. Assuming a one-sided bound on the error term `E` and that the residues `r x` at real
`x > β` have non-negative real part, `New.IsPolar.landau` concludes that there is no pole to the
right of `β`. Together with `Lib.Analytic.EntireLFunction`, this is the analytic tool for passing
from a one-sided bound on an error term to the absence of zeros of L-functions.

## Main results

* `New.IsPolar.landau`: let `β > 0`. If `E v ≤ A e^{(β-1)v}` for all large `v` and `re (r x) ≥ 0`
  for real `x > β`, then `r ρ = 0` for `re ρ > β`.

Notions from other files:
* `New.IsPolar` (from `Lib.Analytic.EntireLFunction`): `E` is measurable, `|E v| ≤ C e^v` for
  `v ≥ 0`, and `∫₀^∞ E(v) e^{(1-s)v} dv` continues meromorphically with at most simple poles of
  residue `r ρ` in `re ρ > 0`.

## Relation to the literature

Known result: Landau's lemma on Dirichlet integrals of one sign. It is applied to transforms with
simple poles whose residues at real points have non-negative real part: no pole lies to the right
of the abscissa given by the one-sided bound. Source: Montgomery and Vaughan, Multiplicative
Number Theory I, 2007, Lemma 15.1 (Widder, The Laplace Transform, 1941, II Thm 5b).
-/

@[expose] public section

open Complex Set Filter MeasureTheory Metric Topology ComplexOrder AnalyticOnNhd Real TauCeti

namespace New

variable {E : ℝ → ℝ}

/-- Let `E` satisfy `|E v| ≤ C e^v` for `v ≥ 0`, and let `β > 0`. If `E v ≤ A e^{(β-1)v}` for large
`v`, then `E(v) e^v ≤ K e^{βv}` for some `K` and all `v > 0`. -/
lemma exists_mul_exp_le {C A β : ℝ} (hE_growth : ∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) (hβ : 0 < β)
    (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ A * Real.exp ((β - 1) * v)) :
    ∃ K : ℝ, ∀ v : ℝ, 0 < v → E v * Real.exp v ≤ K * Real.exp (β * v) := by
  obtain ⟨Y, hY⟩ := hE_le.exists_forall_of_atTop
  -- `K ≥ A` serves for `v ≥ Y`, and `K ≥ |C| e^{2Y}` for `v ≤ Y`.
  refine ⟨max A (|C| * Y.exp ^ 2), fun v hv ↦ ?_⟩
  obtain hYv | hvY := le_total Y v
  · calc
      E v * v.exp ≤ (A * Real.exp ((β - 1) * v)) * v.exp := by grw [hY v hYv]
      _ = A * Real.exp (β * v) := by rw [mul_assoc, ← Real.exp_add, sub_one_mul, sub_add_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · calc
      E v * v.exp ≤ |C| * v.exp * v.exp := by
        grw [le_abs_self (E v), hE_growth v hv.le, le_abs_self C]
      _ ≤ max A (|C| * Y.exp ^ 2) := by grw [mul_assoc, ← sq, hvY, ← le_max_right]
      _ ≤ _ := le_mul_of_one_le_right
        ((show 0 ≤ |C| * Y.exp ^ 2 by positivity).trans (le_max_right _ _))
        (Real.one_le_exp (by positivity))

/-- Identity theorem: two functions meromorphic on `re z > a` that agree far to the right agree
on a punctured neighbourhood of every point of the half-plane. -/
lemma eventuallyEq_of_eq_far_right {f g : ℂ → ℂ} {a b : ℝ} (hf : MeromorphicOn f {z : ℂ | a < z.re})
    (hg : MeromorphicOn g {z : ℂ | a < z.re}) (hfg : ∀ z : ℂ, b < z.re → f z = g z) {ρ : ℂ}
    (hρ : a < ρ.re) :
    f =ᶠ[𝓝[≠] ρ] g := by
  -- `f - g` has infinite order at a point `s₀` to the right of `a` and `b`, hence at `ρ`.
  obtain ⟨s₀, has₀, hbs₀⟩ : ∃ s₀ : ℝ, a < s₀ ∧ b < s₀ := by simpa using exists_gt (max a b)
  have order_s₀ : meromorphicOrderAt (f - g) s₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr <| eventually_nhdsWithin_of_eventually_nhds <|
      mem_of_superset ((isOpen_re_gt b).mem_nhds hbs₀) fun z hz ↦ sub_eq_zero.mpr (hfg z hz)
  exact eventuallyEq_iff_sub.mpr <| meromorphicOrderAt_eq_top_iff.mp <|
    (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected
      (convex_halfSpace_re_gt a).isPreconnected has₀ hρ order_s₀

/-- **No pole to the right of `β`**, by Landau's lemma and the sign of the residues at real points.
Suppose `IsPolar E r`: `|E v| ≤ C e^v` for `v ≥ 0` and the transform
`∫₀^∞ E(v) e^{(1-s)v} dv` has a meromorphic continuation with at most simple poles of residue `r ρ`
in `re ρ > 0`. Let `β > 0`. If `E(v) ≤ A e^{(β-1)v}` for all large `v` and the residues at real points
right of `β` have real part `≥ 0`, then there is no pole in `re s > β`, that is, `r ρ = 0`. -/
lemma IsPolar.landau {r : ℂ → ℂ} (h : IsPolar E r) {A β : ℝ} (hβ : 0 < β)
    (hr : ∀ x : ℝ, β < x → 0 ≤ (r x).re)
    (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ A * Real.exp ((β - 1) * v))
    {ρ : ℂ} (hρ : β < ρ.re) :
    r ρ = 0 := by
  -- `Ψ(s) = K / (s - β) - Φ(s)` continues the Laplace transform `F` of `f v = K e^{βv} - E(v) e^v ≥ 0`.
  -- Let `a` be the larger of `β` and the abscissa of convergence of `F`. If `β < a`, the residue
  -- sign forces `Ψ` to be analytic at `a`, so Tau Ceti's Landau theorem extends convergence left of `a`.
  obtain ⟨hE, C, Φ, hΦ, hE_growth, Φ_eq, Φ_res⟩ := h
  obtain ⟨K, hK⟩ := exists_mul_exp_le hE_growth hβ hE_le
  let f (v : ℝ) : ℝ := K * Real.exp (β * v) - E v * Real.exp v
  have hf_nonneg : ∀ v : ℝ, 0 < v → 0 ≤ f v := fun v hv ↦ sub_nonneg.2 (hK v hv)
  let F (s : ℂ) : ℂ := ∫ v : ℝ in Ioi 0, cexp (-s * v) • (f v : ℂ)
  let Ψ (s : ℂ) : ℂ := K / (s - β) - Φ s
  -- For `re s > β + 2`, the Laplace transform of `f` converges and equals `Ψ s`.
  have h_far_laplace (s : ℂ) (hs : β + 2 < s.re) :
      HasLaplace (fun v ↦ (f v : ℂ)) s (Ψ s) := by
    have hsβ : (β - s).re < 0 := by simp; linarith
    have int_exp : Integrable (fun v : ℝ ↦ K * cexp ((β - s) * v)) (volume.restrict (Ioi 0)) :=
      (integrableOn_exp_mul_complex_Ioi hsβ 0).const_mul K
    have int_E := integrableOn_laplace_of_abs_le hE hE_growth (s := s) (by linarith)
    have h_integrand (v : ℝ) :
        cexp (-s * v) • (f v : ℂ) = K * cexp ((β - s) * v) - E v * cexp ((1 - s) * v) := by
      simp only [f, smul_eq_mul, ofReal_sub, ofReal_mul, ofReal_exp, mul_sub, sub_mul, one_mul,
        neg_mul, Complex.exp_sub, Complex.exp_neg]
      ring
    have h_int : Integrable (fun v : ℝ ↦ cexp (-s * v) • (f v : ℂ)) (volume.restrict (Ioi 0)) :=
      (int_exp.sub int_E).congr (.of_forall fun v ↦ (h_integrand v).symm)
    have h_eq : F s = Ψ s := by
      simp_rw [F, h_integrand, integral_sub int_exp int_E, integral_const_mul,
        integral_exp_mul_complex_Ioi hsβ, ← neg_sub s, neg_div_neg_eq, Ψ, Φ_eq s (by linarith)]
      simp [div_eq_mul_inv]
    exact h_eq ▸ h_int.hasLaplace
  -- `S` is the set of real points where the Laplace transform of `f` converges; let `a = sup (insert β Sᶜ)`.
  let S : Set ℝ := {x : ℝ | IntegrableOn (fun v : ℝ ↦ cexp (-(x : ℂ) * v) • (f v : ℂ)) (Ioi 0)}
  have bdd : BddAbove Sᶜ := ⟨β + 2, fun x hx ↦ le_of_not_gt fun hlt ↦
    hx (h_far_laplace x (by simpa)).integrable⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, IsLUB (insert β Sᶜ) a := Real.exists_isLUB (by simp) (bdd.insert β)
  have h_laplace {z : ℂ} (hz : a < z.re) : HasLaplace (fun v ↦ (f v : ℂ)) z (F z) := by
    obtain ⟨x, hax, hxz⟩ := exists_between hz
    have hxS : x ∈ S := of_not_not fun hx ↦ hax.not_ge (ha.1 (mem_insert_of_mem β hx))
    exact (hxS.hasLaplace.integrableOn_of_re_le (by simpa using hxz.le)).integrable.hasLaplace
  have F_analytic {z : ℂ} (hz : a < z.re) : AnalyticAt ℂ F z :=
    (differentiableOn_of_hasLaplace_re_gt (fun w hw ↦ h_laplace hw)).analyticAt
      ((isOpen_re_gt a).mem_nhds hz)
  have far_right (s : ℂ) (hs : β + 2 < s.re) : Ψ s = F s := (h_far_laplace s hs).integral_eq.symm
  have Ψ_eq {z : ℂ} (hz : a < z.re) : Ψ =ᶠ[𝓝[≠] z] F := eventuallyEq_of_eq_far_right
    (fun w _ ↦ by fun_prop) (fun w hw ↦ (F_analytic hw).meromorphicAt) far_right hz
  have Ψ_res (z : ℂ) (hz : β < z.re) : Tendsto (fun w ↦ (w - z) * Ψ w) (𝓝[≠] z) (𝓝 (-r z)) := by
    have hK_cont : ContinuousAt (fun s : ℂ ↦ K / (s - β)) z := by
      fun_prop (disch := exact sub_ne_zero.2 fun h_eq ↦ by simp [h_eq] at hz)
    simpa [Ψ, mul_sub] using (tendsto_sub_mul_of_continuousAt hK_cont).sub (Φ_res z (hβ.trans hz))
  obtain rfl | hβa : β = a ∨ β < a := (ha.1 (mem_insert β Sᶜ)).eq_or_lt
  · -- The residue `-r ρ` of `Ψ` is that of the analytic function `F`.
    simpa using tendsto_nhds_unique ((Ψ_res ρ hρ).congr' (Ψ_eq hρ).mul_left)
      (tendsto_sub_mul_of_continuousAt (F_analytic hρ).continuousAt)
  · -- If `β < a`, then `(x - a) Ψ x = (x - a) F x ≥ 0` for real `x > a`, forcing `-r a = 0`.
    have hΨ_mero : MeromorphicAt Ψ a := by fun_prop
    have tendsto_real : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] a) (𝓝[≠] a) :=
      ((hasDerivAt_id' a).ofReal_comp.tendsto_nhdsNE one_ne_zero).mono_left (nhdsGT_le_nhdsNE a)
    have eq_near : ∀ᶠ x : ℝ in 𝓝[>] a, Ψ =ᶠ[𝓝 (x : ℂ)] F := by
      filter_upwards [tendsto_real.eventually hΨ_mero.eventually_analyticAt, self_mem_nhdsWithin]
        with x hΨx (hx : a < x) using
          (hΨx.frequently_eq_iff_eventually_eq (F_analytic (by simpa using hx))).mp
            (Ψ_eq (by simpa using hx)).frequently
    have F_nonneg (x : ℝ) : 0 ≤ F x := by
      have h_int : F x = ((∫ v : ℝ in Ioi 0, Real.exp (-x * v) * f v : ℝ) : ℂ) := by
        calc F x = ∫ v : ℝ in Ioi 0, ((Real.exp (-x * v) * f v : ℝ) : ℂ) :=
              integral_congr_ae (.of_forall fun v ↦ by simp [smul_eq_mul, ofReal_exp])
          _ = _ := integral_ofReal
      rw [h_int, zero_le_real]
      exact setIntegral_nonneg measurableSet_Ioi fun v hv ↦
        mul_nonneg (Real.exp_nonneg _) (hf_nonneg v hv)
    have h_res_nonneg : 0 ≤ -r a := by
      refine ge_of_tendsto ((Ψ_res a hβa).comp tendsto_real) ?_
      filter_upwards [eq_near, self_mem_nhdsWithin] with x hΨx (hx : a < x)
      rw [Function.comp_apply, hΨx.self_of_nhds, ← ofReal_sub]
      exact mul_nonneg (zero_le_real.2 (sub_nonneg.2 hx.le)) (F_nonneg x)
    have h_res_zero : -r a = 0 :=
      Complex.ext (le_antisymm (by simpa using hr a hβa) h_res_nonneg.1) h_res_nonneg.2.symm
    -- Removable singularity at `a`: `g = dslope ((z - a) * Ψ z) a` is analytic on `ball a r₀`.
    let G (z : ℂ) : ℂ := (z - a) * Ψ z
    obtain ⟨p, hp⟩ : AnalyticAt ℂ G a :=
      MeromorphicAt.analyticAt (by fun_prop) (by
        rw [continuousAt_iff_punctured_nhds]
        simpa [G, h_res_zero] using Ψ_res a hβa)
    let g : ℂ → ℂ := dslope G a
    have hg_eq : ∀ z : ℂ, z ≠ a → g z = Ψ z := fun z hz ↦ eqOn_dslope_sub_smul Ψ a hz
    obtain ⟨r₀, hr₀, hg_ball⟩ := hp.dslope_fslope.analyticAt.exists_ball_analyticOnNhd
    have h_agree (z : ℂ) (hz : z ∈ ball (a : ℂ) r₀) (hza : a < z.re) :
        HasLaplace (fun v ↦ (f v : ℂ)) z (g z) := by
      have hz_ne : z ≠ a := fun h_eq ↦ by simp [h_eq] at hza
      have h_gF : g =ᶠ[𝓝[≠] z] F := by
        have h_open : ({(a : ℂ)}ᶜ : Set ℂ) ∈ 𝓝[≠] z :=
          mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds hz_ne)
        filter_upwards [h_open, Ψ_eq hza] with w hw hΨF
        exact (hg_eq w hw).trans hΨF
      have h_eq : g z = F z :=
        ((hg_ball z hz).frequently_eq_iff_eventually_eq (F_analytic hza)).1
          h_gF.frequently |>.self_of_nhds
      exact h_eq.symm ▸ h_laplace hza
    -- Tau Ceti's Landau theorem extends convergence to `a - r₀ < re s`, contradicting `IsLUB`.
    have h_ext (σ : ℝ) (hσ : a - r₀ < σ) : σ ∈ S :=
      integrableOn_cexp_neg_mul_smul_ofReal_of_ae_nonneg
        ((ae_restrict_mem measurableSet_Ioi).mono hf_nonneg) hr₀
        hg_ball.differentiableOn h_agree (by simpa)
    obtain ⟨σ, hσ, hσ_gt, -⟩ : ∃ σ ∈ insert β Sᶜ, max β (a - r₀) < σ ∧ σ ≤ a :=
      ha.exists_between (max_lt hβa (by linarith))
    obtain ⟨hβσ, hσr⟩ : β < σ ∧ a - r₀ < σ := max_lt_iff.mp hσ_gt
    exact absurd (h_ext σ hσr) (hσ.resolve_left hβσ.ne')

end New
