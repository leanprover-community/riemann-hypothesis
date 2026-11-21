import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPos
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TuranPowerSumBound
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyper
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrime
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnFinishTuran

section
open Finset Complex Classical Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhc_removable (Z : Finset ℂ) : ∀ (U : Set ℂ) (G : ℂ → ℂ) (C : ℝ), IsOpen U →
    DifferentiableOn ℂ G (U \ (Z : Set ℂ)) → (∀ z ∈ U \ (Z : Set ℂ), ‖G z‖ ≤ C) →
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧ (∀ z ∈ U \ (Z : Set ℂ), H z = G z) ∧
      ∀ z ∈ U, ‖H z‖ ≤ C := by
  induction Z using Finset.induction_on with
  | empty =>
    intro U G C _ hd hb
    exact ⟨G, by simpa using hd, fun _ _ => rfl, by simpa using hb⟩
  | insert a Z ha ih =>
    intro U G C hU hd hb
    have hset : U \ ((insert a Z : Finset ℂ) : Set ℂ) = (U \ {a}) \ (Z : Set ℂ) := by
      ext z
      simp [not_or, and_assoc]
    rw [hset] at hd hb
    obtain ⟨H₁, hH₁d, hH₁e, hH₁b⟩ := ih (U \ {a}) G C (hU.sdiff isClosed_singleton) hd hb
    rw [hset]
    by_cases haU : a ∈ U
    · have hUa : U ∈ 𝓝 a := hU.mem_nhds haU
      have hbd : BddAbove (norm ∘ H₁ '' (U \ {a})) :=
        ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact hH₁b z hz⟩
      have hD := differentiableOn_update_limUnder_of_bddAbove hUa hH₁d hbd
      have hne : ∀ z, z ≠ a → Function.update H₁ a (limUnder (𝓝[≠] a) H₁) z = H₁ z :=
        fun z hz => Function.update_of_ne hz _ _
      refine ⟨_, hD, ?_, ?_⟩
      · intro z hz
        rw [hne z hz.1.2]
        exact hH₁e z hz
      · intro z hz
        by_cases hza : z = a
        · rw [hza]
          have hc := (hD.differentiableAt hUa).continuousAt
          have ht := (hc.norm).tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
          refine le_of_tendsto ht ?_
          filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hUa] with w hw hwU
          rw [hne w hw]
          exact hH₁b w ⟨hwU, hw⟩
        · rw [hne z hza]
          exact hH₁b z ⟨hz, hza⟩
    · have hUe : U \ {a} = U := Set.sdiff_singleton_eq_self haU
      rw [hUe] at hH₁d hH₁b hH₁e ⊢
      exact ⟨H₁, hH₁d, hH₁e, hH₁b⟩

lemma dhc_iter (c ρ : ℂ) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun z => c / (z - ρ)) s =
      c * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ := by
  have h : (fun z : ℂ => c / (z - ρ)) = fun z => c * (fun z : ℂ => (1 * z - ρ)⁻¹) z := by
    ext z
    simp [div_eq_mul_inv]
  have hk : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
  simp only [one_pow, mul_one, one_mul]
  rw [hk, zpow_neg, zpow_natCast]
  ring

lemma dhc_cauchy (H : ℂ → ℂ) (z₀ s : ℂ) (ϱ C : ℝ) (hϱ : 0 < ϱ)
    (hHd : DifferentiableOn ℂ H (Metric.ball z₀ (2 * ϱ))) (hHb : ∀ z ∈ Metric.ball z₀ (2 * ϱ), ‖H z‖ ≤ C)
    (hs : s ∈ Metric.closedBall z₀ ϱ) (k : ℕ) :
    ‖iteratedDeriv k H s‖ ≤ k.factorial * C / ϱ ^ k := by
  have hcont : ContinuousAt (fun R : ℝ => (k.factorial : ℝ) * C / R ^ k) ϱ :=
    continuousAt_const.div (continuousAt_id.pow k) (pow_pos hϱ k).ne'
  have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio ϱ))
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hϱ] with R hR
  have hsub : Metric.closedBall s R ⊆ Metric.ball z₀ (2 * ϱ) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz hs
    rw [Metric.mem_ball]
    have := dist_triangle z s z₀
    linarith [hR.2]
  exact norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR.1 (hHd.diffContOnCl_ball hsub)
    (fun z hz => hHb z (hsub (Metric.sphere_subset_closedBall hz)))

theorem deuring_heilbronn_cauchy : DHCauchy := by
  intro f z₀ r B hr hB hfd hf0 hfb
  obtain ⟨Z, m, hZ, hm1, -, -, hsum, hbd⟩ := landau_local3 f z₀ r B hr hB hfd hf0 hfb
  refine ⟨Z, m, hZ, hm1, hsum, ?_⟩
  have hfan : ∀ z ∈ Metric.ball z₀ (r / 6), AnalyticAt ℂ f z := fun z hz =>
    (hfd.mono Metric.ball_subset_closedBall).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by linarith) hz))
  have hnz : ∀ z ∈ Metric.ball z₀ (r / 6) \ (Z : Set ℂ), f z ≠ 0 := fun z hz h0 =>
    hz.2 (Finset.mem_coe.2 ((hZ z).2
      ⟨Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz.1), h0⟩))
  have hGd : DifferentiableOn ℂ (fun z => deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ))
      (Metric.ball z₀ (r / 6) \ (Z : Set ℂ)) := by
    intro z hz
    have h1 := hfan z hz.1
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (h1.deriv.differentiableAt.div h1.differentiableAt (hnz z hz)).sub ?_
    refine DifferentiableAt.fun_sum (fun ρ hρ => ?_)
    exact (differentiableAt_const _).div (differentiableAt_id.sub_const ρ)
      (sub_ne_zero.2 (fun h => hz.2 (h ▸ Finset.mem_coe.2 hρ)))
  obtain ⟨H, hHd, hHe, hHb⟩ := dhc_removable Z _ _ (72 * Real.log B / r) Metric.isOpen_ball hGd
    (fun z hz => hbd z (Metric.ball_subset_closedBall hz.1) (hnz z hz))
  intro k s hs hfs
  have hsZ : s ∉ (Z : Set ℂ) := fun h => hfs ((hZ s).1 (Finset.mem_coe.1 h)).2
  have hsU : s ∈ Metric.ball z₀ (r / 6) := by
    rw [Metric.mem_closedBall] at hs
    rw [Metric.mem_ball]
    linarith
  have hev : (fun z => -(deriv f z / f z)) =ᶠ[𝓝 s]
      fun z => -(∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) - H z := by
    have hn : Metric.ball z₀ (r / 6) \ (Z : Set ℂ) ∈ 𝓝 s :=
      (Metric.isOpen_ball.sdiff Z.finite_toSet.isClosed).mem_nhds ⟨hsU, hsZ⟩
    filter_upwards [hn] with z hz
    rw [hHe z hz]
    ring
  have hHan : AnalyticAt ℂ H s := hHd.analyticAt (Metric.isOpen_ball.mem_nhds hsU)
  have hcd : ∀ ρ ∈ Z, ContDiffAt ℂ k (fun z => (m ρ : ℂ) / (z - ρ)) s := fun ρ hρ =>
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
      (sub_ne_zero.2 (fun h => hsZ (h ▸ Finset.mem_coe.2 hρ)))
  have hkey : ‖iteratedDeriv k H s‖ ≤ k.factorial * (72 * Real.log B / r) / (r / 12) ^ k := by
    have h2 : 2 * (r / 12) = r / 6 := by ring
    exact dhc_cauchy H z₀ s (r / 12) _ (by positivity) (h2 ▸ hHd) (h2 ▸ hHb) hs k
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpm : ((-1 : ℂ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; simp
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_fun_sub (ContDiffAt.neg (ContDiffAt.sum hcd)) hHan.contDiffAt,
    iteratedDeriv_fun_neg, iteratedDeriv_fun_sum hcd]
  simp_rw [dhc_iter]
  have he : (-1 : ℂ) ^ k / (k.factorial : ℂ) *
        (-∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ -
          iteratedDeriv k H s) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) =
      -((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k H s) := by
    have : ∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ =
        ((-1) ^ k * (k.factorial : ℂ)) * ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [div_eq_mul_inv]
      ring
    rw [this]
    generalize (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)) = S
    field_simp
    linear_combination (-(k.factorial : ℂ) * S) * hpm
  rw [he, norm_neg, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hfr : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  calc 1 / (k.factorial : ℝ) * ‖iteratedDeriv k H s‖
      ≤ 1 / (k.factorial : ℝ) * (k.factorial * (72 * Real.log B / r) / (r / 12) ^ k) := by gcongr
    _ = 72 * Real.log B / r * (12 / r) ^ k := by
      rw [div_pow, div_pow]
      field_simp

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhl_prod_le (M : ℕ) [NeZero M] (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ M := by
  rw [norm_prod]
  have h1 : ∀ p ∈ M.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
    have hn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp'.pos]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      simpa using hs
    calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ ≤ p := by rw [norm_one]; linarith
  calc ∏ p ∈ M.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ ∏ p ∈ M.primeFactors, (p : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) h1
    _ = ((∏ p ∈ M.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ M := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos M) (Nat.prod_primeFactors_dvd M)

lemma dhl_triv_growth (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunctionTrivChar₁ M s‖ ≤ 4 * M * (1 + ‖s‖) ^ 2 := by
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
  have hs0 := norm_nonneg s
  by_cases h1 : s = 1
  · subst h1
    have := dhl_prod_le M 1 (by simp)
    simp only [Function.update_self]
    have e : ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) = ∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) := by
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [cpow_neg_one]
    rw [e]
    refine this.trans ?_
    rw [norm_one]
    nlinarith
  · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne h1,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h1, norm_mul, norm_mul]
    have hP := dhl_prod_le M s (by linarith)
    have hz := Formalism.ZF.growthBound s (by linarith) h1
    have hpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
    have hle : ‖s - 1‖ ≤ 1 + ‖s‖ := by
      have := norm_sub_le s 1; rw [norm_one] at this; linarith
    have hb : 1 / s.re ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hz2 : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 4 * (1 + ‖s‖) ^ 2 := by
      calc ‖s - 1‖ * ‖riemannZeta s‖
          ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) := by gcongr
        _ = ‖s - 1‖ + 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by field_simp
        _ ≤ (1 + ‖s‖) + 1 + (1 + ‖s‖) * (‖s‖ * (1 + 2)) := by gcongr
        _ ≤ 4 * (1 + ‖s‖) ^ 2 := by nlinarith
    calc ‖s - 1‖ * (‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * ‖riemannZeta s‖)
        = ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * (‖s - 1‖ * ‖riemannZeta s‖) := by ring
      _ ≤ M * (4 * (1 + ‖s‖) ^ 2) := by gcongr
      _ = 4 * M * (1 + ‖s‖) ^ 2 := by ring

lemma dhl_pole (k : ℕ) (s : ℂ) (hs : s ≠ 1) :
    (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z : ℂ => 1 / (z - 1)) s
      = 1 / (s - 1) ^ (k + 1) := by
  have h := congrFun (iter_deriv_inv_linear_sub k (1 : ℂ) 1) s
  have e : (fun z : ℂ => 1 / (z - 1)) = fun x : ℂ => (1 * x - 1)⁻¹ := by
    funext z; simp
  rw [iteratedDeriv_eq_iterate, e, h]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have e2 : (1 * s - 1) ^ (-1 - (k : ℤ)) = ((s - 1) ^ (k + 1))⁻¹ := by
    rw [one_mul, show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [e2, one_pow]
  have h1 : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]; simp
  field_simp
  linear_combination h1

lemma dhl_log (K X : ℝ) (hK : 1 ≤ K) (hX : 3 ≤ X) :
    Real.log (K * X ^ 2) ≤ (Real.log K + 2) * Real.log X := by
  have hl : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hk : 0 ≤ Real.log K := Real.log_nonneg hK
  rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
  push_cast
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhl_geom (t : ℝ) (z : ℂ) (hz : ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25) :
    1 / 2 ≤ z.re ∧ 1 + ‖z‖ ≤ 2 * (|t| + 2) := by
  have hre : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
    simp
  have h1 := abs_re_le_norm (z - ((26 / 25 : ℂ) + t * I))
  rw [sub_re, hre] at h1
  have hn : ‖((26 / 25 : ℂ) + t * I)‖ ≤ 26 / 25 + |t| := by
    calc ‖((26 / 25 : ℂ) + t * I)‖ ≤ ‖(26 / 25 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 26 / 25 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  refine ⟨?_, ?_⟩
  · have := (abs_le.mp (h1.trans hz)).1; linarith
  · have := norm_sub_norm_le z ((26 / 25 : ℂ) + t * I)
    linarith [abs_nonneg t]

lemma dhl_core (hCau : DHCauchy) (f : ℂ → ℂ) (t K X : ℝ) (hK : 1 ≤ K) (hX : 3 ≤ X)
    (hf : Differentiable ℂ f) (hf0 : f ((26 / 25 : ℂ) + t * I) ≠ 0)
    (hB : ∀ z, ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25 →
      ‖f z‖ ≤ K * X ^ 2 * ‖f ((26 / 25 : ℂ) + t * I)‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ 150 * (Real.log K + 2) * Real.log X ∧
      ∀ (k : ℕ) (s : ℂ), ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤
          150 * (Real.log K + 2) * Real.log X * 25 ^ k := by
  have hB1 : 1 ≤ K * X ^ 2 := by nlinarith
  obtain ⟨Z, m, hZ, hm, hsum, hexp⟩ := hCau f ((26 / 25 : ℂ) + t * I) (12 / 25) (K * X ^ 2)
    (by norm_num) hB1 hf.differentiableOn hf0
    (fun z hz => hB z (by rwa [Metric.mem_closedBall, dist_eq] at hz))
  have hlog := dhl_log K X hK hX
  have hlog0 : 0 ≤ Real.log (K * X ^ 2) := Real.log_nonneg hB1
  refine ⟨Z, m, ?_, hm, ?_, ?_⟩
  · intro ρ
    rw [hZ ρ, Metric.mem_closedBall, dist_eq]
    norm_num
  · refine hsum.trans ?_
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · intro k s hs hfs
    have := hexp k s (by rw [Metric.mem_closedBall, dist_eq]; norm_num; linarith) hfs
    refine this.trans ?_
    have e : (72 * Real.log (K * X ^ 2) / (12 / 25) * (12 / (12 / 25)) ^ k : ℝ)
        = 150 * Real.log (K * X ^ 2) * 25 ^ k := by
      norm_num; ring
    rw [e]
    have : (0 : ℝ) < 25 ^ k := by positivity
    nlinarith

lemma dhl_z0re (t : ℝ) : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
  simp

lemma dhl_inv (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) :
    1 ≤ 26 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
  have h := inverseBound M ψ ((26 / 25 : ℂ) + t * I) (by rw [dhl_z0re]; norm_num)
  rw [dhl_z0re] at h
  have hne : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ
      (Or.inr (by intro h; have := congrArg Complex.re h; rw [dhl_z0re] at this; norm_num at this))
      (by rw [dhl_z0re]; norm_num)
  have hpos : 0 < ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := norm_pos_iff.mpr hne
  rw [inv_le_comm₀ hpos (by norm_num)] at h
  norm_num at h
  linarith

def DHLocalAt (C : ℝ) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) : Prop :=
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ IsLZero ψ ρ)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, ρ.re < 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ (k : ℕ) (s : ℂ), 1 < s.re → ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD ψ) s
            - (if ψ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) * 25 ^ k

lemma dhl_X (M : ℕ) (t : ℝ) (hM : 3 ≤ M) : 3 ≤ (M : ℝ) * (|t| + 2) := by
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [abs_nonneg t]

lemma dhl_nontriv (hCau : DHCauchy) (C0 K : ℝ)
    (hC0 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C0 * q * (1 + ‖s‖))
    (hK1 : 1 ≤ K) (hK : 52 * C0 ≤ K) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ ≠ 1)
    (t : ℝ) (hM : 3 ≤ M) : DHLocalAt (150 * (Real.log K + 2)) M ψ t := by
  have hX := dhl_X M t hM
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hinv := dhl_inv M ψ t
  have hf0 : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hinv; norm_num at hinv
  obtain ⟨Z, m, hZ, hm, hsum, hexp⟩ := dhl_core hCau (DirichletCharacter.LFunction ψ) t K
    ((M : ℝ) * (|t| + 2)) hK1 hX (DirichletCharacter.differentiable_LFunction hψ) hf0 (by
      intro z hz
      obtain ⟨hre, hn⟩ := dhl_geom t z hz
      have h1 := hC0 M ψ hψ z hre
      have hz0 := norm_nonneg z
      have ht := abs_nonneg t
      calc ‖DirichletCharacter.LFunction ψ z‖ ≤ C0 * M * (1 + ‖z‖) := h1
        _ ≤ (K / 52) * M * (1 + ‖z‖) := by
            have : C0 ≤ K / 52 := by linarith
            gcongr
        _ ≤ (K / 52) * M * (2 * (|t| + 2)) := by gcongr
        _ = K * ((M : ℝ) * (|t| + 2)) * (1 / 26) := by ring
        _ ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
            have hXX : (M : ℝ) * (|t| + 2) ≤ ((M : ℝ) * (|t| + 2)) ^ 2 := by nlinarith
            have : (1 / 26 : ℝ) ≤ ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by linarith
            gcongr)
  refine ⟨Z, m, ?_, hm, ?_, hsum, ?_⟩
  · intro ρ
    rw [hZ ρ]
    exact and_congr_right (fun _ => ⟨fun h => ⟨Or.inl hψ, h⟩, fun h => h.2⟩)
  · intro ρ hρ
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (not_lt.mp hcon)
      ((hZ ρ).mp hρ).2
  · intro k s hs1 hs
    have h := hexp k s hs (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) hs1.le)
    rw [if_neg hψ, sub_zero]
    exact h

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhl_ne_one {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  intro h
  rw [h, Complex.one_re] at hs
  exact lt_irrefl _ hs

lemma dhl_triv_ld (M : ℕ) [NeZero M] (z : ℂ) (hz : 1 < z.re) :
    -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z / DirichletCharacter.LFunctionTrivChar₁ M z)
      = negLD (1 : DirichletCharacter ℂ M) z - 1 / (z - 1) := by
  have hz1 : z ≠ 1 := dhl_ne_one hz
  have hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w =
      (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    intro w hw
    simp [DirichletCharacter.LFunctionTrivChar₁, hw]
  have hev : DirichletCharacter.LFunctionTrivChar₁ M =ᶠ[nhds z]
      fun w => (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    filter_upwards [eventually_ne_nhds hz1] with w hw
    exact hf w hw
  have hd := DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ M) z (Or.inl hz1)
  have hL0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ M)
    (Or.inr hz1) hz.le
  have hlin : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := differentiableAt_id.sub_const 1
  have hder : deriv (DirichletCharacter.LFunctionTrivChar₁ M) z =
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) z +
        (z - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) z := by
    rw [hev.deriv_eq, deriv_fun_mul hlin hd]
    simp
  rw [hder, hf z hz1]
  unfold negLD
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp
  ring

lemma dhl_negLD_contDiffAt (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 < s.re) (k : ℕ) :
    ContDiffAt ℂ k (negLD (1 : DirichletCharacter ℂ M)) s := by
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLd : DifferentiableOn ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M))
      {w : ℂ | 1 < w.re} := by
    intro w hw
    exact (DirichletCharacter.differentiableAt_LFunction _ w
      (Or.inl (dhl_ne_one hw))).differentiableWithinAt
  have hD : DifferentiableOn ℂ (negLD (1 : DirichletCharacter ℂ M)) {w : ℂ | 1 < w.re} := by
    unfold negLD
    refine ((hLd.deriv hU).div hLd ?_).neg
    intro w hw
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr (dhl_ne_one hw)) (le_of_lt hw)
  exact (hD.contDiffOn hU).contDiffAt (hU.mem_nhds hs)

lemma dhl_pole_contDiffAt (s : ℂ) (hs : s ≠ 1) (k : ℕ) :
    ContDiffAt ℂ k (fun z : ℂ => 1 / (z - 1)) s := by
  exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hs)

lemma dhl_triv_iter (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 < s.re) (k : ℕ) :
    (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z =>
      -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z / DirichletCharacter.LFunctionTrivChar₁ M z)) s
      = (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) s
        - 1 / (s - 1) ^ (k + 1) := by
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun z => -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z /
      DirichletCharacter.LFunctionTrivChar₁ M z)) =ᶠ[nhds s]
      (negLD (1 : DirichletCharacter ℂ M) - fun z : ℂ => 1 / (z - 1)) := by
    filter_upwards [hU.mem_nhds hs] with z hz
    rw [Pi.sub_apply]
    exact dhl_triv_ld M z hz
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_sub (dhl_negLD_contDiffAt M s hs k)
    (dhl_pole_contDiffAt s (dhl_ne_one hs) k), mul_sub, dhl_pole k s (dhl_ne_one hs)]

lemma dhl_triv (hCau : DHCauchy) (K : ℝ) (hK : 10400 ≤ K) (M : ℕ) [NeZero M]
    (t : ℝ) (hM : 3 ≤ M) : DHLocalAt (150 * (Real.log K + 2)) M (1 : DirichletCharacter ℂ M) t := by
  have hX3 : 3 ≤ (M : ℝ) * (|t| + 2) := dhl_X M t hM
  have hK1 : 1 ≤ K := by linarith
  have hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w =
      (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    intro w hw
    simp [DirichletCharacter.LFunctionTrivChar₁, hw]
  have hf1 : DirichletCharacter.LFunctionTrivChar₁ M 1 ≠ 0 := by
    simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_self]
    rw [Finset.prod_ne_zero_iff]
    intro p hp h
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : (p : ℂ)⁻¹ = 1 := (sub_eq_zero.mp h).symm
    have h2 : (p : ℂ) = 1 := inv_eq_one.mp h1
    have h3 : p = 1 := by exact_mod_cast h2
    omega
  have hz0re : ((26 / 25 : ℂ) + ↑t * I).re = 26 / 25 := dhl_z0re t
  have hz0ne : (26 / 25 : ℂ) + ↑t * I ≠ 1 := dhl_ne_one (by rw [hz0re]; norm_num)
  have hLz0 := dhl_inv M (1 : DirichletCharacter ℂ M) t
  have hnz0 : 1 / 650 ≤ ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
    rw [hf _ hz0ne, norm_mul]
    have ha : 1 / 25 ≤ ‖(26 / 25 : ℂ) + ↑t * I - 1‖ := by
      have := Complex.re_le_norm ((26 / 25 : ℂ) + ↑t * I - 1)
      rw [Complex.sub_re, hz0re, Complex.one_re] at this
      linarith
    nlinarith [norm_nonneg (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) ((26 / 25 : ℂ) + ↑t * I))]
  have hfz0 : DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnz0
    norm_num at hnz0
  have hgrowth : ∀ z : ℂ, ‖z - ((26 / 25 : ℂ) + ↑t * I)‖ ≤ 12 / 25 →
      ‖DirichletCharacter.LFunctionTrivChar₁ M z‖ ≤
        K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
    intro z hz
    obtain ⟨hre, hn⟩ := dhl_geom t z hz
    have h1 := dhl_triv_growth M z hre
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have h2 : ‖DirichletCharacter.LFunctionTrivChar₁ M z‖ ≤ 16 * M * (|t| + 2) ^ 2 := by
      have hsq : (1 + ‖z‖) ^ 2 ≤ (2 * (|t| + 2)) ^ 2 := by
        have : 0 ≤ 1 + ‖z‖ := by positivity
        gcongr
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 4 * M)
      nlinarith
    have h3 : 16 * M * (|t| + 2) ^ 2 ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) := by
      have hKM : 10400 ≤ K * M := by nlinarith
      have hT : 0 ≤ (M : ℝ) * (|t| + 2) ^ 2 := by positivity
      have e : K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) = (K * M) * (M * (|t| + 2) ^ 2) / 650 := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hKM hT
      linarith
    have h4 : K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) ≤
        K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
      apply mul_le_mul_of_nonneg_left hnz0
      positivity
    linarith
  obtain ⟨Z, m, hZ, hm, hcount, hbd⟩ := dhl_core hCau (DirichletCharacter.LFunctionTrivChar₁ M) t K
    ((M : ℝ) * (|t| + 2)) hK1 hX3 (DirichletCharacter.differentiable_LFunctionTrivChar₁ M) hfz0 hgrowth
  have hzero : ∀ ρ : ℂ, DirichletCharacter.LFunctionTrivChar₁ M ρ = 0 ↔
      IsLZero (1 : DirichletCharacter ℂ M) ρ := by
    intro ρ
    constructor
    · intro h
      have hρ : ρ ≠ 1 := fun e => hf1 (e ▸ h)
      refine ⟨Or.inr hρ, ?_⟩
      rw [hf ρ hρ] at h
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hρ)
    · rintro ⟨h1, h2⟩
      have hρ : ρ ≠ 1 := h1.resolve_left (fun h => h rfl)
      rw [hf ρ hρ, h2, mul_zero]
  unfold DHLocalAt
  refine ⟨Z, m, ?_, hm, ?_, hcount, ?_⟩
  · intro ρ
    rw [hZ ρ, hzero ρ]
  · intro ρ hρ
    obtain ⟨_, hfρ⟩ := (hZ ρ).mp hρ
    obtain ⟨h1, h2⟩ := (hzero ρ).mp hfρ
    by_contra hge
    push_neg at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ h1 hge h2
  · intro k s hs hsd
    have hs1 : s ≠ 1 := dhl_ne_one hs
    have hfs : DirichletCharacter.LFunctionTrivChar₁ M s ≠ 0 := by
      rw [hf s hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr hs1) hs.le)
    have hb := hbd k s hsd hfs
    rw [if_pos rfl, ← dhl_triv_iter M s hs k]
    exact hb

theorem deuring_heilbronn_local : DHLocalOf := by
  unfold DHLocalOf DHLocal
  intro hCau
  obtain ⟨C0, hC0⟩ := lfunction_polynomial_growth
  have hlog : 0 ≤ Real.log (max 10400 (52 * C0)) :=
    Real.log_nonneg (by linarith [le_max_left (10400 : ℝ) (52 * C0)])
  refine ⟨150 * (Real.log (max 10400 (52 * C0)) + 2), by linarith, ?_⟩
  intro M inst ψ t hM
  by_cases hψ : ψ = 1
  · subst hψ
    exact dhl_triv hCau _ (le_max_left _ _) M t hM
  · exact dhl_nontriv hCau C0 _ hC0 (by linarith [le_max_left (10400 : ℝ) (52 * C0)])
      (le_max_right _ _) M ψ hψ t hM

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

lemma dhDom_hasSum {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n ↦ term (logMul^[k] (↗ψ * ↗Λ)) s n)
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s) := by
  have habs : abscissaOfAbsConv (↗ψ * ↗Λ) < s.re := by
    refine lt_of_le_of_lt (abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) ?_) ?_
    · intro y hy
      exact LSeriesSummable_twist_vonMangoldt ψ hy
    · exact_mod_cast hs
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hU : LFunction ψ =ᶠ[nhds z] LSeries (↗ψ) := by
      filter_upwards [hopen.mem_nhds hz'] with w hw
      exact DirichletCharacter.LFunction_eq_LSeries ψ hw
    simp only [negLD]
    rw [Filter.EventuallyEq.deriv_eq hU, DirichletCharacter.LFunction_eq_LSeries ψ hz',
      LSeries_twist_vonMangoldt_eq ψ hz', neg_div]
  have hit : iteratedDeriv k (negLD ψ) s = iteratedDeriv k (LSeries (↗ψ * ↗Λ)) s := by
    simp only [← iteratedDerivWithin_univ]
    refine Filter.EventuallyEq.iteratedDerivWithin_eq ?_ hev.eq_of_nhds
    simpa [nhdsWithin_univ] using hev
  rw [hit, LSeries_iteratedDeriv k habs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (by simpa using habs)).LSeriesHasSum

private theorem logMul_iterate_apply_eq_log_pow_mul (f : ℕ → ℂ) (k n : ℕ) :
    logMul^[k] f n = Complex.log n ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', logMul, ih]
    ring

lemma dhDom_term_le {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h1 : χ₁ ^ 2 = 1)
    (k : ℕ) (σ γ : ℝ) (n : ℕ) :
    ‖term (logMul^[k] (↗χ * ↗Λ)) ((σ : ℂ) + γ * I) n
      + term (logMul^[k] (↗(χ * χ₁) * ↗Λ)) ((σ : ℂ) + γ * I) n‖ ≤
    (term (logMul^[k] (↗(1 : DirichletCharacter ℂ q) * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ₁ * ↗Λ)) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set A : ℝ := Real.log n ^ k * Λ n with hA
  have hA0 : 0 ≤ A :=
    mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k) ArithmeticFunction.vonMangoldt_nonneg
  have e1 : ∀ c : ℂ, Complex.log n ^ k * (c * ((Λ n : ℝ) : ℂ)) = (A : ℂ) * c := by
    intro c
    rw [hA, ← Complex.natCast_log]
    push_cast
    ring
  have hN : ‖(n : ℂ) ^ ((σ : ℂ) + γ * I)‖ = (n : ℝ) ^ σ := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hR : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnpos.le]
  have hp : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
  have hre : ∀ c : ℝ, ((A : ℂ) * (c : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)).re = A * c / (n : ℝ) ^ σ := by
    intro c
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [term_of_ne_zero hn, logMul_iterate_apply_eq_log_pow_mul, Pi.mul_apply, MulChar.coeToFun_mul, e1, hR]
  by_cases hu : IsUnit (n : ZMod q)
  · obtain ⟨u, hu'⟩ := hu
    rw [← hu', MulChar.one_apply_coe]
    have hχ : ‖χ u‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
    have h1u : χ₁ u * χ₁ u = 1 := by
      rw [← pow_two, ← MulChar.pow_apply_coe, h1, MulChar.one_apply_coe]
    rcases mul_self_eq_one_iff.mp h1u with h | h
    · rw [h]
      have := hre 1
      push_cast at this
      rw [this]
      have e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * 1) /
          (n : ℂ) ^ ((σ : ℂ) + γ * I) = ((2 * A : ℝ) : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) := by
        push_cast
        ring
      rw [e2, norm_div, norm_mul, hχ, hN, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      apply le_of_eq
      ring
    · rw [h]
      have := hre 1
      have h' := hre (-1)
      push_cast at this h'
      rw [this, h']
      have e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * -1) /
          (n : ℂ) ^ ((σ : ℂ) + γ * I) = 0 := by
        ring
      rw [e2, norm_zero]
      apply le_of_eq
      ring
  · simp [MulChar.map_nonunit _ hu]

theorem deuring_heilbronn_dominant : DHDom := by
  intro M _ χ₁ χ γ σ k h1 hσ
  have hs : 1 < ((σ : ℂ) + γ * I).re := by simpa using hσ
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hA := dhDom_hasSum χ k hs
  have hB := dhDom_hasSum (χ * χ₁) k hs
  have hC := dhDom_hasSum (1 : DirichletCharacter ℂ M) k hs0
  have hD := dhDom_hasSum χ₁ k hs0
  have hbound := HasSum.norm_le_of_bounded (hA.add hB) (Complex.hasSum_re (hC.add hD))
    (fun n ↦ by
      rw [Complex.add_re]
      exact dhDom_term_le χ₁ χ h1 k σ γ n)
  have e1 : ‖iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
      + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ =
      ‖(-1 : ℂ) ^ k * iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
        + (-1 : ℂ) ^ k * iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ := by
    rw [← mul_add, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [e1, mul_add]
  exact hbound

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

def dhFam (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) : Multiset ℂ :=
  Z.val.bind (fun ρ => Multiset.replicate (m ρ) (s - ρ))

theorem dhFam_mem (Z : Finset ℂ) (m : ℂ → ℕ) (s ρ : ℂ) (h : ρ ∈ Z) (hm : 1 ≤ m ρ) :
    s - ρ ∈ dhFam Z m s := by
  unfold dhFam
  rw [Multiset.mem_bind]
  exact ⟨ρ, h, Multiset.mem_replicate.2 ⟨by omega, rfl⟩⟩

theorem dhFlat (S : Multiset ℂ) : ∃ (N : ℕ) (w : Fin N → ℂ), Finset.univ.val.map w = S := by
  refine ⟨S.toList.length, S.toList.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]

theorem dhFlat_sum {β : Type*} [AddCommMonoid β] {N : ℕ} (w : Fin N → ℂ) (S : Multiset ℂ)
    (h : Finset.univ.val.map w = S) (g : ℂ → β) : ∑ i, g (w i) = (S.map g).sum := by
  rw [← h, Multiset.map_map]
  rfl

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem dhReBound (A P S : ℂ) (E : ℝ) (h : ‖A - P + S‖ ≤ E) : S.re ≤ P.re - A.re + E := by
  have h1 : (A - P + S).re ≤ ‖A - P + S‖ := by
    first
      | exact Complex.re_le_norm _
      | exact Complex.re_le_abs _
  simp only [Complex.add_re, Complex.sub_re] at h1
  linarith

theorem logMulAbsAddTwoLeTwoMulLog (M : ℕ) (T t : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) (ht : |t| ≤ T) :
    Real.log ((M : ℝ) * (|t| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hta := abs_nonneg t
  have hpos : 0 < (M : ℝ) * (|t| + 2) := by positivity
  have h1 : (M : ℝ) * (|t| + 2) ≤ (M : ℝ) * (T + 2) := by nlinarith
  have h2 : (M : ℝ) * (T + 2) ≤ ((M : ℝ) * T) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (M : ℝ) - 3) (by linarith : (0 : ℝ) ≤ T - 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (M : ℝ)) (by linarith : (0 : ℝ) ≤ T - 2)]
  calc Real.log ((M : ℝ) * (|t| + 2)) ≤ Real.log (((M : ℝ) * T) ^ 2) :=
        Real.log_le_log hpos (h1.trans h2)
    _ = 2 * Real.log ((M : ℝ) * T) := by rw [Real.log_pow]; norm_num

theorem dhLogOne (M : ℕ) (T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : (6 : ℝ) ≤ M * T := by nlinarith
  have he := Real.exp_one_lt_d9
  have h1 : Real.exp 1 ≤ (M : ℝ) * T := by linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) h1

theorem dhPair (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : β₁ < 1) (k : ℕ) (s : ℂ)
    (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) :
    (1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)).re ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
  have hδ : 0 < 1 - β₁ := by linarith
  have hare : (s - 1).re = η := by rw [hs]; simp
  have hbre : (s - β₁).re = η + (1 - β₁) := by rw [hs]; simp; ring
  have hna : η ≤ ‖s - 1‖ := hare ▸ Complex.re_le_norm (s - 1)
  have hnb : η ≤ ‖s - β₁‖ := le_trans (by linarith) (hbre ▸ Complex.re_le_norm (s - β₁))
  have ha0 : s - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hna; linarith
  have hb0 : s - β₁ ≠ 0 := fun h => by rw [h, norm_zero] at hnb; linarith
  have hba : (s - β₁) - (s - 1) = ((1 - β₁ : ℝ) : ℂ) := by push_cast; ring
  have hid : 1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1) =
      ((s - β₁) - (s - 1)) * (∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)) /
        ((s - 1) ^ (k + 1) * (s - β₁) ^ (k + 1)) := by
    rw [mul_comm ((s - β₁) - (s - 1)), geom_sum₂_mul]
    field_simp
  have hsum : ‖∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ ≤
      ((k + 1 : ℕ) : ℝ) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2)) := by
    calc _ ≤ ∑ i ∈ Finset.range (k + 1), ‖(s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (k + 1), ‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [norm_mul, norm_pow, norm_pow, le_div_iff₀ (by positivity)]
          have e1 : η ^ (k + 2) = η ^ (i + 1) * η ^ (k + 1 - i) := by rw [← pow_add]; congr 1; omega
          have e2 : ‖s - 1‖ ^ (k + 1) = ‖s - 1‖ ^ (k + 1 - 1 - i) * ‖s - 1‖ ^ (i + 1) := by
            rw [← pow_add]; congr 1; omega
          have e3 : ‖s - β₁‖ ^ (k + 1) = ‖s - β₁‖ ^ i * ‖s - β₁‖ ^ (k + 1 - i) := by
            rw [← pow_add]; congr 1; omega
          rw [e1, e2, e3]
          have p1 : η ^ (i + 1) ≤ ‖s - 1‖ ^ (i + 1) := pow_le_pow_left₀ hη.le hna _
          have p2 : η ^ (k + 1 - i) ≤ ‖s - β₁‖ ^ (k + 1 - i) := pow_le_pow_left₀ hη.le hnb _
          have p12 := mul_le_mul p1 p2 (by positivity) (by positivity)
          calc ‖s - β₁‖ ^ i * ‖s - 1‖ ^ (k + 1 - 1 - i) * (η ^ (i + 1) * η ^ (k + 1 - i))
              ≤ ‖s - β₁‖ ^ i * ‖s - 1‖ ^ (k + 1 - 1 - i) * (‖s - 1‖ ^ (i + 1) * ‖s - β₁‖ ^ (k + 1 - i)) :=
                mul_le_mul_of_nonneg_left p12 (by positivity)
            _ = _ := by ring
      _ = ((k + 1 : ℕ) : ℝ) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfinal : ‖1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)‖ ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
    rw [hid, norm_div, norm_mul, hba, Complex.norm_real, Real.norm_of_nonneg hδ.le, norm_mul, norm_pow, norm_pow]
    have hpos : 0 < ‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) := by
      have := norm_pos_iff.mpr ha0
      have := norm_pos_iff.mpr hb0
      positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    have h3 := mul_le_mul_of_nonneg_left hsum hδ.le
    push_cast at h3
    calc (1 - β₁) * ‖∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ * η ^ (k + 2)
        ≤ (1 - β₁) * (((k : ℝ) + 1) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2))) * η ^ (k + 2) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ((k : ℝ) + 1) * (1 - β₁) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1)) := by
          field_simp
  have hre : (1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)).re ≤
      ‖1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)‖ := Complex.re_le_norm _
  exact hre.trans hfinal

theorem dhAssemble {β : Type*} [AddCommGroup β] (F1 F2 F3 F4 : Multiset ℂ) (b2 b3 b4 : ℂ)
    (c3 c4 : Prop) [Decidable c3] [Decidable c4] (h2 : b2 ∈ F2) (h3 : c3 → b3 ∈ F3) (h4 : c4 → b4 ∈ F4)
    (g : ℂ → β) :
    ((F1 + F2.erase b2 + (if c3 then F3.erase b3 else F3) + (if c4 then F4.erase b4 else F4)).map g).sum
      = (F1.map g).sum + (F2.map g).sum + (F3.map g).sum + (F4.map g).sum - g b2
        - (if c3 then g b3 else 0) - (if c4 then g b4 else 0) := by
  classical
  have e : ∀ (F : Multiset ℂ) (b : ℂ), b ∈ F → ((F.erase b).map g).sum = (F.map g).sum - g b := by
    intro F b hb
    rw [← Multiset.sum_map_erase hb]
    abel
  simp only [Multiset.map_add, Multiset.sum_add, e _ _ h2]
  by_cases hc3 : c3 <;> by_cases hc4 : c4
  · simp only [if_pos hc3, if_pos hc4, e _ _ (h3 hc3), e _ _ (h4 hc4)]
    abel
  · simp only [if_pos hc3, if_neg hc4, e _ _ (h3 hc3)]
    abel
  · simp only [if_neg hc3, if_pos hc4, e _ _ (h4 hc4)]
    abel
  · simp only [if_neg hc3, if_neg hc4]
    abel

theorem dhFam_re (Z : Finset ℂ) (m : ℂ → ℕ) (s x : ℂ) (η : ℝ) (hZ : ∀ ρ ∈ Z, ρ.re < 1)
    (hs : s.re = 1 + η) (hx : x ∈ dhFam Z m s) : η ≤ x.re := by
  unfold dhFam at hx
  rw [Multiset.mem_bind] at hx
  obtain ⟨ρ, hρ, hx⟩ := hx
  rw [Multiset.eq_of_mem_replicate hx, Complex.sub_re, hs]
  linarith [hZ ρ hρ]

theorem dhMemIte (F : Multiset ℂ) (c : Prop) [Decidable c] (b x : ℂ) (h : x ∈ (if c then F.erase b else F)) :
    x ∈ F := by
  split_ifs at h
  · exact Multiset.mem_of_mem_erase h
  · exact h

theorem dhFamPow (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (k : ℕ) :
    ((dhFam Z m s).map (fun x => 1 / x ^ (k + 1))).sum = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
  unfold dhFam
  rw [Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun ρ _ => ?_
  simp [Multiset.map_replicate, Multiset.sum_replicate, div_eq_mul_inv]

theorem dhFinalArith (S1 S2 S3 S4 P1 P3 P4 A1 A2 A3 A4 E0 Eγ g2 I3 I4 X F G Hc H e8 : ℝ)
    (t1 : S1 + S2 + S3 + S4 ≤ P1 - A1 + E0 + (0 - A2 + E0) + (P3 - A3 + Eγ) + (P4 - A4 + Eγ))
    (hA : 0 ≤ A1 + A2 + A3 + A4) (hp : P1 - g2 ≤ X) (hs : P3 + P4 - I3 - I4 ≤ X + e8)
    (h0 : E0 ≤ F) (hγ : Eγ ≤ F) (t3 : F ≤ 2 * G) (t2 : e8 ≤ H) (nn : 0 ≤ Hc) :
    S1 + S2 + S3 + S4 - g2 - I3 - I4 ≤ 2 * X + (8 * G + 8 * Hc + H) := by
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

private theorem norm_inv_pow_sub_inv_pow_le (a b : ℂ) (η δ : ℝ) (hη : 0 < η) (ha : η ≤ ‖a‖) (hb : η ≤ ‖b‖)
    (hab : ‖b - a‖ ≤ δ) (n : ℕ) : ‖1 / a ^ n - 1 / b ^ n‖ ≤ n * δ / η ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, norm_zero] at ha
      linarith
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, norm_zero] at hb
      linarith
    have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hab
    have key : 1 / a ^ (n + 1) - 1 / b ^ (n + 1) =
        (1 / a) * (1 / a ^ n - 1 / b ^ n) + (1 / b ^ n) * ((b - a) / (a * b)) := by
      field_simp
      ring
    rw [key]
    have h1 : ‖1 / a‖ ≤ 1 / η := by
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hη ha
    have h2 : ‖1 / b ^ n‖ ≤ 1 / η ^ n := by
      rw [norm_div, norm_one, norm_pow]
      exact one_div_le_one_div_of_le (pow_pos hη n) (pow_le_pow_left₀ hη.le hb n)
    have h3 : ‖(b - a) / (a * b)‖ ≤ δ / (η * η) := by
      rw [norm_div, norm_mul]
      exact div_le_div₀ hδ hab (mul_pos hη hη) (mul_le_mul ha hb hη.le (norm_nonneg _))
    calc _ ≤ ‖1 / a‖ * ‖1 / a ^ n - 1 / b ^ n‖ + ‖1 / b ^ n‖ * ‖(b - a) / (a * b)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 / η * (n * δ / η ^ (n + 1)) + 1 / η ^ n * (δ / (η * η)) := by gcongr
      _ = _ := by
        push_cast
        field_simp
        ring

theorem dhfShiftPoleN (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : β₁ < 1) (k : ℕ) (c : Prop) [Decidable c]
    (hc : ¬ c → 1 / 8 ≤ |γ|) (s : ℂ) (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) :
    ‖1 / (s - 1) ^ (k + 1) - (if c then 1 / (s - β₁) ^ (k + 1) else 0)‖ ≤
      ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
  have hre1 : (s - 1).re = η := by
    rw [hs]
    simp
  have hre2 : (s - (β₁ : ℂ)).re = 1 + η - β₁ := by
    rw [hs]
    simp
  have him : (s - 1).im = γ := by
    rw [hs]
    simp
  have hsa : η ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [hre1, abs_of_pos hη] at this
    exact this
  have hsb : η ≤ ‖s - (β₁ : ℂ)‖ := by
    have := Complex.re_le_norm (s - (β₁ : ℂ))
    rw [hre2] at this
    linarith
  have hd : ‖(s - (β₁ : ℂ)) - (s - 1)‖ ≤ 1 - β₁ := by
    have e : (s - (β₁ : ℂ)) - (s - 1) = ((1 - β₁ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h8 : (0 : ℝ) ≤ 8 ^ (k + 1) := by positivity
  have hpos : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
    apply div_nonneg
    · apply mul_nonneg
      · positivity
      · linarith
    · positivity
  split_ifs with h
  · have := norm_inv_pow_sub_inv_pow_le (s - 1) (s - β₁) η (1 - β₁) hη hsa hsb hd (k + 1)
    push_cast at this
    linarith
  · have hγ : 1 / 8 ≤ |γ| := hc h
    have hs1 : 1 / 8 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [him] at this
      linarith
    rw [sub_zero, norm_div, norm_one, norm_pow]
    have hb : 1 / ‖s - 1‖ ^ (k + 1) ≤ 8 ^ (k + 1) := by
      rw [div_le_iff₀ (by positivity)]
      calc (1 : ℝ) = 8 ^ (k + 1) * (1 / 8) ^ (k + 1) := by
            rw [← mul_pow]
            norm_num
        _ ≤ 8 ^ (k + 1) * ‖s - 1‖ ^ (k + 1) := by gcongr
    linarith

private theorem one_eighth_le_abs_of_not_mem_pole_disc (γ β₁ : ℝ) (hβ1 : 19 / 20 ≤ β₁) (hβ2 : β₁ < 1)
    (h : ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25) : 1 / 8 ≤ |γ| := by
  by_contra hlt
  push_neg at hlt
  apply h
  have hg : γ ^ 2 < 1 / 64 := by
    have := abs_lt.mp hlt
    nlinarith
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith

theorem dhfPoles {M : ℕ} (χ₁ χ : DirichletCharacter ℂ M) (hχ₁2 : χ₁ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1)
    (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : 19 / 20 ≤ β₁) (hβ2 : β₁ < 1) (k : ℕ) (s : ℂ)
    (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) [Decidable (χ = 1)] [Decidable (χ * χ₁ = 1)]
    (c3 c4 : Prop) [Decidable c3] [Decidable c4]
    (h3 : χ = χ₁ → ¬ c3 → ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25)
    (h4 : χ = 1 → ¬ c4 → ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25)
    (h3' : c3 → χ = χ₁) (h4' : c4 → χ = 1) :
    ‖(if χ = 1 then 1 / (s - 1) ^ (k + 1) else 0) + (if χ * χ₁ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
      - (if c3 then 1 / (s - β₁) ^ (k + 1) else 0) - (if c4 then 1 / (s - β₁) ^ (k + 1) else 0)‖
      ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
  have hpos : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
    have : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
      apply div_nonneg
      · apply mul_nonneg
        · positivity
        · linarith
      · positivity
    exact add_nonneg this (by positivity)
  by_cases h1 : χ = 1
  · have h2 : ¬ (χ * χ₁ = 1) := by
      rw [h1, one_mul]
      exact hχ₁1
    have h3n : ¬ c3 := fun h => hχ₁1 ((h3' h).symm.trans h1)
    simp only [if_pos h1, if_neg h2, if_neg h3n, add_zero, sub_zero]
    exact dhfShiftPoleN η γ β₁ hη hβ2 k c4 (fun h => one_eighth_le_abs_of_not_mem_pole_disc γ β₁ hβ1 hβ2 (h4 h1 h)) s hs
  · by_cases h2 : χ * χ₁ = 1
    · have hχ : χ = χ₁ := by
        have e : χ = χ * χ₁ * χ₁ := by rw [mul_assoc, ← sq, hχ₁2, mul_one]
        rw [e, h2, one_mul]
      have h4n : ¬ c4 := fun h => h1 (h4' h)
      simp only [if_neg h1, if_pos h2, if_neg h4n, zero_add, sub_zero]
      exact dhfShiftPoleN η γ β₁ hη hβ2 k c3 (fun h => one_eighth_le_abs_of_not_mem_pole_disc γ β₁ hβ1 hβ2 (h3 hχ h)) s hs
    · have h3n : ¬ c3 := fun h => h2 (by rw [h3' h, ← sq, hχ₁2])
      have h4n : ¬ c4 := fun h => h1 (h4' h)
      simp only [if_neg h1, if_neg h2, if_neg h3n, if_neg h4n, add_zero, sub_zero, norm_zero]
      exact hpos

theorem dhfReNonneg (S : Multiset ℂ) (h : ∀ x ∈ S, 0 < x.re) :
    0 ≤ ((S.map (fun x : ℂ => 1 / x)).sum).re := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_re]
    have ha := h a (Multiset.mem_cons_self a S)
    have h1 : 0 ≤ (1 / a).re := by
      rw [one_div, Complex.inv_re]
      exact div_nonneg ha.le (Complex.normSq_nonneg a)
    exact add_nonneg h1 (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

theorem dhfEraseSum (Z : Finset ℂ) (m : ℂ → ℕ) (s b : ℂ) (c : Prop) [Decidable c]
    (hb : c → b ∈ dhFam Z m s) (k : ℕ) :
    ((if c then (dhFam Z m s).erase b else dhFam Z m s).map (fun x : ℂ => 1 / x ^ (k + 1))).sum =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) - (if c then 1 / b ^ (k + 1) else 0) := by
  have key : ((dhFam Z m s).map (fun x : ℂ => 1 / x ^ (k + 1))).sum =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
    unfold dhFam
    rw [Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
    congr 1
    apply Multiset.map_congr rfl
    intro ρ _
    rw [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    ring
  split_ifs with h
  · rw [← key, ← Multiset.sum_map_erase (hb h)]
    ring
  · rw [key, sub_zero]

theorem dhfNormArith (D3 D4 P3 P4 S3 S4 I3 I4 A B : ℂ) (k : ℕ) (e3 e4 Dom X : ℝ)
    (h3 : ‖D3 - P3 + S3‖ ≤ e3) (h4 : ‖D4 - P4 + S4‖ ≤ e4)
    (hD3 : D3 = (-1 : ℂ) ^ k / (k.factorial : ℂ) * A) (hD4 : D4 = (-1 : ℂ) ^ k / (k.factorial : ℂ) * B)
    (hdom : ‖A + B‖ ≤ Dom) (hP : ‖P3 + P4 - I3 - I4‖ ≤ X) :
    ‖(S3 - I3) + (S4 - I4)‖ ≤ Dom / (k.factorial : ℝ) + X + e3 + e4 := by
  have hnf : ‖(-1 : ℂ) ^ k / (k.factorial : ℂ)‖ = 1 / (k.factorial : ℝ) := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hD : ‖D3 + D4‖ ≤ Dom / (k.factorial : ℝ) := by
    rw [hD3, hD4, ← mul_add, norm_mul, hnf, div_mul_eq_mul_div, one_mul]
    gcongr
  have e : (S3 - I3) + (S4 - I4) =
      ((D3 - P3 + S3) + (D4 - P4 + S4) - (D3 + D4)) + (P3 + P4 - I3 - I4) := by ring
  rw [e]
  have n1 := norm_add_le ((D3 - P3 + S3) + (D4 - P4 + S4) - (D3 + D4)) (P3 + P4 - I3 - I4)
  have n2 := norm_sub_le ((D3 - P3 + S3) + (D4 - P4 + S4)) (D3 + D4)
  have n3 := norm_add_le (D3 - P3 + S3) (D4 - P4 + S4)
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem deuring_heilbronn_inequality : DHIneqFOf := by
  intro hPos hLoc hDom
  obtain ⟨CL, hCL, hL⟩ := hLoc
  refine ⟨8 * CL + 1, by positivity, ?_⟩
  intro M _ χ₁ χ β₁ T η ρ hM hT hχ₁2 hχ₁1 hβ hβ1 hβ2 hρ hρre hρim hne hη hη2
  have hlog0 : Real.log ((M : ℝ) * (|(0 : ℝ)| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) :=
    logMulAbsAddTwoLeTwoMulLog M T 0 hM hT (by rw [abs_zero]; linarith)
  have hlogγ := logMulAbsAddTwoLeTwoMulLog M T ρ.im hM hT hρim
  have hlog1 := dhLogOne M T hM hT
  obtain ⟨Z1, m1, hZ1, hm1, hr1, hN1, hE1⟩ := hL M 1 0 hM
  obtain ⟨Z2, m2, hZ2, hm2, hr2, hN2, hE2⟩ := hL M χ₁ 0 hM
  obtain ⟨Z3, m3, hZ3, hm3, hr3, hN3, hE3⟩ := hL M χ ρ.im hM
  obtain ⟨Z4, m4, hZ4, hm4, hr4, hN4, hE4⟩ := hL M (χ * χ₁) ρ.im hM
  obtain ⟨s₀, hs₀⟩ : ∃ s : ℂ, s = ((1 + η : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s : ℂ, s = ((1 + η : ℝ) : ℂ) + ρ.im * I := ⟨_, rfl⟩
  have hs₀' : s₀ = ((1 + η : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by rw [hs₀]; simp
  have hs₀re : s₀.re = 1 + η := by rw [hs₀]; simp
  have hs₁re : s₁.re = 1 + η := by rw [hs₁]; simp
  have hd₀ : ‖s₀ - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ≤ 1 / 25 := by
    rw [hs₀, show ((1 + η : ℝ) : ℂ) - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((η - 1 / 25 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hd₁ : ‖s₁ - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I)‖ ≤ 1 / 25 := by
    rw [hs₁, show ((1 + η : ℝ) : ℂ) + ρ.im * I - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I) = ((η - 1 / 25 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h1s₀ : 1 < s₀.re := by rw [hs₀re]; linarith
  have h1s₁ : 1 < s₁.re := by rw [hs₁re]; linarith
  have hβZ : (β₁ : ℂ) ∈ Z2 := by
    refine (hZ2 β₁).2 ⟨?_, Or.inl hχ₁1, hβ⟩
    rw [show (β₁ : ℂ) - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((β₁ - 26 / 25 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hρZ : ρ ∈ Z3 := by
    refine (hZ3 ρ).2 ⟨?_, hρ⟩
    rw [show ρ - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I) = ((ρ.re - 26 / 25 : ℝ) : ℂ) by
        apply Complex.ext <;> simp,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hρ1 : ρ.re < 1 := by
      by_contra h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hρ.1 (le_of_not_gt h) hρ.2
    constructor <;> linarith
  have hb2 : s₀ - β₁ ∈ dhFam Z2 m2 s₀ := dhFam_mem _ _ _ _ hβZ (hm2 _ hβZ)
  have hb3 : χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 → s₁ - β₁ ∈ dhFam Z3 m3 s₁ :=
    fun h => dhFam_mem _ _ _ _ h.2 (hm3 _ h.2)
  have hb4 : χ = 1 ∧ (β₁ : ℂ) ∈ Z4 → s₁ - β₁ ∈ dhFam Z4 m4 s₁ :=
    fun h => dhFam_mem _ _ _ _ h.2 (hm4 _ h.2)
  have hl0 : 0 ≤ Real.log ((M : ℝ) * T) := by linarith

  have big : ∀ k : ℕ, (((dhFam Z1 m1 s₀ + (dhFam Z2 m2 s₀).erase (s₀ - β₁)
      + (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁) else dhFam Z3 m3 s₁)
      + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁) else dhFam Z4 m4 s₁)).map
        (fun x : ℂ => 1 / x ^ (k + 1))).sum).re ≤
      2 * (((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2)) + (8 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1))
        + 8 * 0 + Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) := by
    intro k
    have key := dhAssemble (dhFam Z1 m1 s₀) (dhFam Z2 m2 s₀) (dhFam Z3 m3 s₁) (dhFam Z4 m4 s₁)
      (s₀ - β₁) (s₁ - β₁) (s₁ - β₁) _ _ hb2 hb3 hb4 (fun x : ℂ => 1 / x ^ (k + 1))
    rw [dhFamPow, dhFamPow, dhFamPow, dhFamPow] at key
    rw [key]
    have l1 := dhReBound _ _ _ _ (hE1 k s₀ h1s₀ hd₀)
    have l2 := dhReBound _ _ _ _ (hE2 k s₀ h1s₀ hd₀)
    have l3 := dhReBound _ _ _ _ (hE3 k s₁ h1s₁ hd₁)
    have l4 := dhReBound _ _ _ _ (hE4 k s₁ h1s₁ hd₁)
    rw [if_pos rfl] at l1
    rw [if_neg hχ₁1, Complex.zero_re] at l2
    have hp := hPos M χ₁ χ ρ.im (1 + η) k hχ₁2 (by linarith)
    rw [← hs₁, ← hs₀] at hp
    have hA : 0 ≤ ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) s₀).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD χ₁) s₀).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD χ) s₁).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (χ * χ₁)) s₁).re := by
      have e : ∀ a b c d : ℂ, ((-1 : ℂ) ^ k / (k.factorial : ℂ) * a).re
          + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * b).re
          + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * c).re + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * d).re
          = ((k.factorial : ℝ))⁻¹ * ((-1 : ℂ) ^ k * (a + b + c + d)).re := by
        intro a b c d
        rw [← Complex.re_ofReal_mul]
        simp only [← Complex.add_re]
        congr 1
        push_cast
        ring
      rw [e]
      exact mul_nonneg (by positivity) hp
    have hpair := dhPair η 0 β₁ hη hβ2 k s₀ hs₀'
    have hshift : ((if χ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        + (if χ * χ₁ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        - (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then 1 / (s₁ - β₁) ^ (k + 1) else 0)
        - (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then 1 / (s₁ - β₁) ^ (k + 1) else 0)).re
        ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
      refine le_trans (Complex.re_le_norm _) ?_
      refine dhfPoles χ₁ χ hχ₁2 hχ₁1 η ρ.im β₁ hη hβ1 hβ2 k s₁ hs₁ (χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3) (χ = 1 ∧ (β₁ : ℂ) ∈ Z4) ?_ ?_
        (fun h => h.1) (fun h => h.1)
      · intro h2 hc hd
        apply hc
        refine ⟨h2, (hZ3 β₁).2 ⟨hd, ?_⟩⟩
        rw [h2]
        exact ⟨Or.inl hχ₁1, hβ⟩
      · intro h1 hc hd
        apply hc
        refine ⟨h1, (hZ4 β₁).2 ⟨hd, ?_⟩⟩
        rw [h1, one_mul]
        exact ⟨Or.inl hχ₁1, hβ⟩
    simp only [Complex.add_re, Complex.sub_re] at hpair hshift ⊢
    have ee0 : CL * Real.log ((M : ℝ) * (|(0 : ℝ)| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog0 hCL.le) (by positivity)
    have eeγ : CL * Real.log ((M : ℝ) * (|ρ.im| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogγ hCL.le) (by positivity)
    have h25k : (25 : ℝ) ^ k ≤ 25 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have eek := mul_le_mul_of_nonneg_left h25k (mul_nonneg hCL.le hl0)
    have h8 : (8 : ℝ) ^ (k + 1) ≤ 25 ^ (k + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h25 : (25 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) :=
      le_mul_of_one_le_left (by positivity) hlog1
    have t1 := add_le_add (add_le_add (add_le_add l1 l2) l3) l4
    have t2 : (8 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) := le_trans h8 h25
    have t3 : CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k ≤ 2 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) := by
      linarith
    exact dhFinalArith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t1 hA hpair hshift ee0 eeγ t3 t2 le_rfl

  obtain ⟨N, w, hw⟩ := dhFlat
    ((if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁) else dhFam Z3 m3 s₁)
    + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁) else dhFam Z4 m4 s₁))
  refine ⟨N, w, ?_, ?_, ?_, ?_⟩
  ·
    intro i
    have hx : w i ∈ Finset.univ.val.map w := Multiset.mem_map_of_mem w (Finset.mem_univ i)
    rw [hw] at hx
    rcases Multiset.mem_add.1 hx with h | h
    · exact dhFam_re _ _ _ _ _ hr3 hs₁re (dhMemIte _ _ _ _ h)
    · exact dhFam_re _ _ _ _ _ hr4 hs₁re (dhMemIte _ _ _ _ h)
  ·
    have hx₀ : s₁ - ρ = ((η + (1 - ρ.re) : ℝ) : ℂ) := by
      rw [hs₁]; apply Complex.ext <;> simp; ring
    have hm : s₁ - ρ ∈ dhFam Z3 m3 s₁ := dhFam_mem _ _ _ _ hρZ (hm3 _ hρZ)
    have hm' : s₁ - ρ ∈ (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁)
        else dhFam Z3 m3 s₁) := by
      split_ifs with hc
      · rw [Multiset.mem_erase_of_ne]
        · exact hm
        · intro h'
          apply hne
          rw [hc.1, sub_right_inj.1 h']
      · exact hm
    have hS : s₁ - ρ ∈ Finset.univ.val.map w := by
      rw [hw]
      exact Multiset.mem_add.2 (Or.inl hm')
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hS
    exact ⟨i, hi.trans hx₀⟩
  ·
    have e1 : ∑ i, 1 / w i = (((if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁)
        else dhFam Z3 m3 s₁) + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁)
        else dhFam Z4 m4 s₁)).map (fun x : ℂ => 1 / x)).sum := dhFlat_sum w _ hw (fun x : ℂ => 1 / x)
    rw [e1]
    have hb := big 0
    simp only [zero_add, pow_one, Nat.cast_zero] at hb
    rw [Multiset.map_add, Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add,
      Multiset.sum_add, Complex.add_re, Complex.add_re, Complex.add_re] at hb
    rw [Multiset.map_add, Multiset.sum_add, Complex.add_re]
    have n1 := dhfReNonneg (dhFam Z1 m1 s₀) (fun x hx => by
      have := dhFam_re _ _ _ _ _ hr1 hs₀re hx; linarith)
    have n2 := dhfReNonneg ((dhFam Z2 m2 s₀).erase (s₀ - β₁)) (fun x hx => by
      have := dhFam_re _ _ _ _ _ hr2 hs₀re (Multiset.mem_of_mem_erase hx); linarith)
    have hl := mul_nonneg hCL.le hl0
    have q1 : 2 * (1 * (1 - β₁) / η ^ 2) = 2 * (1 - β₁) / η ^ 2 := by ring
    have q2 : (8 * CL + 1) * Real.log ((M : ℝ) * T) * 25 =
        8 * (CL * Real.log ((M : ℝ) * T) * 25) + 8 * 0 + Real.log ((M : ℝ) * T) * 25 := by ring
    rw [q2, ← q1]
    linarith
  ·
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have e1 : ∑ i, 1 / (w i) ^ (k + 1) = (((if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁)
        else dhFam Z3 m3 s₁) + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁)
        else dhFam Z4 m4 s₁)).map (fun x : ℂ => 1 / x ^ (k + 1))).sum :=
      dhFlat_sum w _ hw (fun x : ℂ => 1 / x ^ (k + 1))
    rw [e1, Multiset.map_add, Multiset.sum_add, dhfEraseSum Z3 m3 s₁ (s₁ - β₁) _ hb3 k,
      dhfEraseSum Z4 m4 s₁ (s₁ - β₁) _ hb4 k]
    have hdom := hDom M χ₁ χ ρ.im (1 + η) k hχ₁2 (by linarith)
    rw [← hs₁] at hdom
    have hP : ‖(if χ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        + (if χ * χ₁ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        - (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then 1 / (s₁ - β₁) ^ (k + 1) else 0)
        - (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then 1 / (s₁ - β₁) ^ (k + 1) else 0)‖
        ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
      refine dhfPoles χ₁ χ hχ₁2 hχ₁1 η ρ.im β₁ hη hβ1 hβ2 k s₁ hs₁ (χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3) (χ = 1 ∧ (β₁ : ℂ) ∈ Z4) ?_ ?_
        (fun h => h.1) (fun h => h.1)
      · intro h2 hc hd
        apply hc
        refine ⟨h2, (hZ3 β₁).2 ⟨hd, ?_⟩⟩
        rw [h2]
        exact ⟨Or.inl hχ₁1, hβ⟩
      · intro h1 hc hd
        apply hc
        refine ⟨h1, (hZ4 β₁).2 ⟨hd, ?_⟩⟩
        rw [h1, one_mul]
        exact ⟨Or.inl hχ₁1, hβ⟩
    have hm := dhfNormArith _ _ _ _ _ _ _ _ _ _ k _ _ _ _ (hE3 k s₁ h1s₁ hd₁) (hE4 k s₁ h1s₁ hd₁)
      rfl rfl hdom hP
    have eeγ : CL * Real.log ((M : ℝ) * (|ρ.im| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogγ hCL.le) (by positivity)
    have h25k : (25 : ℝ) ^ k ≤ 25 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have eek := mul_le_mul_of_nonneg_left h25k (mul_nonneg hCL.le hl0)
    have h8 : (8 : ℝ) ^ (k + 1) ≤ 25 ^ (k + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h25 : (25 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) :=
      le_mul_of_one_le_left (by positivity) hlog1
    have hX0 : (0 : ℝ) ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
      apply div_nonneg _ (by positivity); apply mul_nonneg (by positivity); linarith
    have eG : 2 * ((k + 1 : ℕ) : ℝ) * (1 - β₁) / η ^ (k + 1 + 1) =
        2 * (((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2)) := by push_cast; ring
    have t4 : (8 * CL + 1) * Real.log ((M : ℝ) * T) * 25 ^ (k + 1) =
        8 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) + Real.log ((M : ℝ) * T) * 25 ^ (k + 1) := by ring
    rw [eG, t4]
    have hCL0 : 0 ≤ CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1) := by positivity
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem deuring_heilbronn_lossy : DeuringHeilbronnMB :=
  deuring_heilbronn_finish_turan turan_power_sum_bound (deuring_heilbronn_inequality deuring_heilbronn_positivity (deuring_heilbronn_local deuring_heilbronn_cauchy) deuring_heilbronn_dominant)
    (deuring_heilbronn_prime_sum deuring_heilbronn_hypergeometric)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
