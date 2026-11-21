import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PRestPBound
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.TauSumRearrangement
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PShOfPower
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTotOfPower
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDegPolyEvalX
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PCFlPos
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PShTotIndependent
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PLimitsExist
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AntisymmetrizeBlockVandermondeOf
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTotFormula
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.SingleDecompIsHomDecomp
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PCBounds
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeHomogeneous
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PPrimesLogSum
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsHomDecomp
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.LineFIsHomogeneous
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.ExistsDominantSubSmul

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem KaPSplit.proof : KaPSplit.Statement := by
  intro d p φ hp _ hs τ
  have h2 : ∀ n : ℕ, ((φ ^ (n + 1)) (τ, false)).2 = false := by
    intro n
    induction n with
    | zero => simpa using hs τ
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have e : (φ ^ (n + 1)) (τ, false) = (((φ ^ (n + 1)) (τ, false)).1, false) :=
        Prod.ext rfl ih
      rw [e]
      exact hs _
  have hterm : ∀ n : ℕ, ((p : ℝ) ^ (n + 1))⁻¹ * (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ) =
      (d.j : ℝ) * ((p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n) := by
    intro n
    simp only [rankLie, h2 n, Bool.false_eq_true, if_false]
    rw [pow_succ, mul_inv, inv_pow]
    ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  unfold kaP
  rw [tsum_congr hterm, tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have e1 : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  rw [e1]
  field_simp

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

theorem inertFrob_snd {d : IndexData} {φ : Equiv.Perm (Emb d)} (hφ : IsFrobLike d φ)
    (hi : IsInertFrob d φ) (e : Emb d) : (φ e).2 = !e.2 := by
  obtain ⟨σ, b⟩ := e
  cases b with
  | false => simpa using hi σ
  | true =>
    have h := hφ.1 (σ, false)
    have hc : conjEmb d (σ, false) = (σ, true) := rfl
    rw [hc] at h
    rw [h]
    simp [conjEmb, hi σ]

theorem inertFrob_pow_snd {d : IndexData} {φ : Equiv.Perm (Emb d)} (hφ : IsFrobLike d φ)
    (hi : IsInertFrob d φ) (e : Emb d) (n : ℕ) : ((φ ^ n) e).2 = (e.2 ^^ decide (Odd n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, inertFrob_snd hφ hi, ih]
    cases e.2 <;> by_cases h : Odd n <;> simp [h, Nat.odd_add_one]

theorem rankLie_inert_pow {d : IndexData} {φ : Equiv.Perm (Emb d)} (hφ : IsFrobLike d φ)
    (hi : IsInertFrob d φ) (τ : Fin d.f) (n : ℕ) :
    rankLie d ((φ ^ (n + 1)) (τ, false)) = if Odd n then d.j else d.N - d.j := by
  unfold rankLie
  rw [inertFrob_pow_snd hφ hi]
  by_cases h : Odd n <;> simp [h, Nat.odd_add_one]

theorem KaPInert.proof : KaPInert.Statement := by
  intro d p φ hp hφ hi τ
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set r : ℝ := ((p : ℝ) ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  set a : ℝ := ((d.N - d.j : ℕ) : ℝ)
  set t : ℕ → ℝ := fun n => ((p : ℝ) ^ (n + 1))⁻¹ * (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ)
  have heven : ∀ k, t (2 * k) = (a / p) * r ^ k := by
    intro k
    simp only [t, rankLie_inert_pow hφ hi, hr, a]
    have : ¬ Odd (2 * k) := by simp
    rw [if_neg this, inv_pow, ← pow_mul, pow_succ]
    field_simp
  have hodd : ∀ k, t (2 * k + 1) = ((d.j : ℝ) / p ^ 2) * r ^ k := by
    intro k
    simp only [t, rankLie_inert_pow hφ hi, hr]
    have : Odd (2 * k + 1) := odd_two_mul_add_one k
    rw [if_pos this, inv_pow, ← pow_mul, show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add]
    field_simp
  have hg : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hse : Summable (fun k => t (2 * k)) := by
    simp_rw [heven]; exact hg.mul_left _
  have hso : Summable (fun k => t (2 * k + 1)) := by
    simp_rw [hodd]; exact hg.mul_left _
  have hsum : kaP d p φ τ = ∑' k, t (2 * k) + ∑' k, t (2 * k + 1) :=
    (tsum_even_add_odd hse hso).symm
  rw [hsum]
  simp_rw [heven, hodd]
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, hr]
  have hp2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hp2' : (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹ = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 := by
    field_simp
  rw [hp2']
  field_simp

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem rankLie_bounds (d : IndexData) (e : Emb d) :
    1 ≤ (rankLie d e : ℝ) ∧ (rankLie d e : ℝ) ≤ d.N := by
  have h1 := d.one_le_j
  have h2 := d.j_lt_N
  unfold rankLie
  split_ifs
  · constructor
    · exact_mod_cast (by omega : 1 ≤ d.N - d.j)
    · exact_mod_cast (by omega : d.N - d.j ≤ d.N)
  · constructor
    · exact_mod_cast h1
    · exact_mod_cast h2.le

theorem geom_succ_inv (p : ℕ) (hp : 2 ≤ p) :
    HasSum (fun n : ℕ => ((p : ℝ) ^ (n + 1))⁻¹) (1 / ((p : ℝ) - 1)) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (p : ℝ)⁻¹
  have hfun : (fun n : ℕ => (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ n) = fun n : ℕ => ((p : ℝ) ^ (n + 1))⁻¹ := by
    funext n
    rw [← inv_pow, pow_succ, mul_comm]
  rw [hfun] at h
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hsub : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  have hv : (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ = 1 / ((p : ℝ) - 1) := by
    rw [hsub, inv_div, ← mul_div_assoc, inv_mul_cancel₀ hp0]
  rw [hv] at h
  exact h

theorem KaPBound.proof : KaPBound.Statement := by
  intro d p φ hp _ τ
  have hp2 := hp.two_le
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hg := geom_succ_inv p hp2
  set a : ℕ → ℝ := fun n => ((p : ℝ) ^ (n + 1))⁻¹ with ha
  set r : ℕ → ℝ := fun n => (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ) with hr
  have ha0 : ∀ n, 0 < a n := fun n => inv_pos.mpr (pow_pos (by linarith) _)
  have hterm0 : ∀ n, 0 ≤ a n * r n := fun n =>
    mul_nonneg (ha0 n).le (by linarith [(rankLie_bounds d ((φ ^ (n + 1)) (τ, false))).1])
  have htermle : ∀ n, a n * r n ≤ (d.N : ℝ) * a n := fun n => by
    rw [mul_comm (d.N : ℝ)]
    exact mul_le_mul_of_nonneg_left (rankLie_bounds d ((φ ^ (n + 1)) (τ, false))).2 (ha0 n).le
  have hNs : HasSum (fun n => (d.N : ℝ) * a n) ((d.N : ℝ) * (1 / ((p : ℝ) - 1))) := hg.mul_left _
  have hsum : Summable (fun n => a n * r n) :=
    Summable.of_nonneg_of_le hterm0 htermle hNs.summable
  have hk : kaP d p φ τ = ∑' n, a n * r n := rfl
  rw [hk]
  constructor
  · have h0 : 0 < a 0 * r 0 :=
      mul_pos (ha0 0) (by linarith [(rankLie_bounds d ((φ ^ (0 + 1)) (τ, false))).1])
    exact hsum.tsum_pos hterm0 0 h0
  · calc ∑' n, a n * r n ≤ ∑' n, (d.N : ℝ) * a n := hsum.tsum_le_tsum htermle hNs.summable
      _ = (d.N : ℝ) * (1 / ((p : ℝ) - 1)) := hNs.tsum_eq
      _ = (d.N : ℝ) / ((p : ℝ) - 1) := by ring

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem liePowerSum_isHomogeneous (d : IndexData) (m : ℕ) (e : Emb d) :
    (liePowerSum d m e).IsHomogeneous m := by
  unfold liePowerSum lowerPowerSum
  split_ifs
  · refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℚ (e.1, i)).neg.pow m
  · refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℚ (e.1, i)).pow m

theorem RestPWellDefined.proof : RestPWellDefined.Statement := by
  intro d vol p φ F Q Q' hQ hQ'
  unfold rest₂
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp hk
  congr 1
  funext n
  unfold restSeries
  have hG := liePowerSum_isHomogeneous d (k - 1) ((φ ^ (n + 1)) (τ, false))
  have h := RestTerms.RestTermWellDefined.full d.f d.N F Q Q' hQ hQ' k (by omega) hkN τ _ hG
  unfold RestTerms.restTerm at h
  have e : ∀ R : ℕ → Fin d.f → XPoly d,
      (k : ℚ) * intFl d (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * R k τ) =
        flagNormalisation d.f d.N *
          ((k : ℚ) * RestTerms.flagIntegral d.f d.N (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * R k τ)) := by
    intro R
    simp only [intFl, LinearMap.smul_apply, flagIntegralLin, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [e Q, e Q', h]

theorem RestPWellDefined.full : RestPWellDefined.Statement := RestPWellDefined.proof

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

theorem summable_log_div_sq : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _))
    (fun n => ?_) ((Real.summable_nat_rpow.2 (by norm_num : (-(3 / 2) : ℝ) < -1)).mul_left 2)
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.log_le_rpow_div hx.le one_half_pos
  have key : (n : ℝ) ^ (-(3 / 2) : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hx]
    norm_num
  rw [key]
  calc Real.log n / (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2) := by ring

theorem RestSummable.proof (hB : RestPBound.Statement) : RestSummable.Statement := by
  intro d S B0 F Q hQ
  obtain ⟨c, hc⟩ := hB d S.vol F Q hQ
  have hg : Summable (fun p : primesAbove S B0 =>
      |c| * (Real.log (p : ℕ) / (((p : ℕ) : ℝ)) ^ 2)) :=
    (summable_log_div_sq.subtype (primesAbove S B0)).mul_left |c|
  refine Summable.of_nonneg_of_le (fun p => abs_nonneg _) (fun p => ?_) hg
  have h := (hc p.1 (S.frob p.1) p.2.1).2
  calc |rest₂ d S.vol p (S.frob p) Q| ≤ c * Real.log (p : ℕ) / (((p : ℕ) : ℝ)) ^ 2 := h
    _ ≤ |c| * (Real.log (p : ℕ) / (((p : ℕ) : ℝ)) ^ 2) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self c)
          (div_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _))

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem ShTotInvertiblePair.proof (h : ShTotIndependent.Statement) :
    ShTotInvertiblePair.Statement := by
  intro d hf
  have hli := LinearIndependent.pair_iff.mp (h d hf).2
  set S : topSpace d →ₗ[ℚ] ℚ := ∑ τ : Fin d.f, shOn d τ with hS
  set T : topSpace d →ₗ[ℚ] ℚ := ∑ τ : Fin d.f, totOn d τ with hT
  have hSapp : ∀ x : topSpace d, S x = shSum d x.1 := by
    intro x
    simp [hS, LinearMap.sum_apply, shOn, shLin, shSum]
  have hTapp : ∀ x : topSpace d, T x = totSum d x.1 := by
    intro x
    simp [hT, LinearMap.sum_apply, totOn, totLin, totSum]
  by_contra hne
  push Not at hne
  have key : ∀ x y : topSpace d, S x * T y - T x * S y = 0 := by
    intro x y
    rw [hSapp, hSapp, hTapp, hTapp]
    exact hne x.1 y.1 ((mem_homogeneousSubmodule _ _).mp x.2)
      ((mem_homogeneousSubmodule _ _).mp y.2)
  obtain ⟨x, hx⟩ : ∃ x : topSpace d, S x ≠ 0 := by
    by_contra h0
    push Not at h0
    have h1 := hli 1 0 (by
      ext y
      simp [h0 y])
    exact one_ne_zero h1.1
  have h2 := hli (T x) (-(S x)) (by
    ext y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
    linear_combination -(key x y))
  exact hx (neg_eq_zero.mp h2.2)

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset Filter Topology

theorem tendsto_sum_primesIn_restP {d : IndexData} (S : EndSystem d) (B0 : ℕ)
    (Q : ℕ → Fin d.f → XPoly d)
    (h : Summable (fun p : primesAbove S B0 => |rest₂ d S.vol p (S.frob p) Q|)) :
    Tendsto (fun B : ℕ => ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q) atTop
      (𝓝 (restTot S B0 Q)) := by
  set g : ℕ → ℝ := fun p => rest₂ d S.vol p (S.frob p) Q with hg
  have hs : Summable (fun p : primesAbove S B0 => g p) := summable_abs_iff.1 h
  have hi : Summable ((primesAbove S B0).indicator g) := summable_subtype_iff_indicator.1 hs
  have ht : restTot S B0 Q = ∑' p, (primesAbove S B0).indicator g p := by
    rw [restTot]
    exact _root_.tsum_subtype (primesAbove S B0) g
  rw [ht]
  refine (hi.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr ?_
  intro B
  classical
  have hset : primesIn S B0 B = (range (B + 1)).filter (fun p => p ∈ primesAbove S B0) := by
    ext p
    rw [primesIn, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    have hm : p ∈ primesAbove S B0 ↔ p.Prime ∧ ¬ p ∣ S.level ∧ B0 < p := Iff.rfl
    rw [hm]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨by omega, h3, h4, h1⟩
    · rintro ⟨h1, h3, h4, h5⟩
      exact ⟨⟨h5, by omega⟩, h3, h4⟩
  rw [Function.comp_apply, hset, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Set.indicator_apply]

theorem HeightTauIdentity.proof (h82 : HeightSumIdentity.Statement) (hsum : RestSummable.Statement) :
    HeightTauIdentity.Statement := by
  intro d S hin B0 A0 b0 hA hb F Q hQ
  obtain ⟨B1, hB1⟩ := h82 d S hin B0
  obtain ⟨C, hC⟩ := hB1 F Q hQ
  have hrest := tendsto_sum_primesIn_restP S B0 Q (hsum d S B0 F Q hQ.2.2)
  set L : ℕ → ℝ := fun B => S.vol * (S.hh F - aB S B0 B * (shSum d F : ℝ) -
      bB S B0 B * (totSum d F : ℝ)) + ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q with hLdef
  have hL : Tendsto L atTop (𝓝 (S.vol * (S.hh F - A0 * (shSum d F : ℝ) - b0 * (totSum d F : ℝ)) +
      restTot S B0 Q)) :=
    ((((tendsto_const_nhds (x := S.hh F)).sub (hA.mul_const _)).sub
      (hb.mul_const _)).const_mul S.vol).add hrest
  have hlog : Tendsto (fun B : ℕ => C * Real.log B / B) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).const_mul C
    simpa [Function.comp_def, mul_div_assoc] using h
  have hdiff : Tendsto (fun B => S.PP B0 F - L B) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlog
    filter_upwards [eventually_gt_atTop B0, eventually_ge_atTop B1] with B hB0 hB1'
    rw [Real.norm_eq_abs]
    exact hC B hB0 hB1'
  have hsum' := hL.add hdiff
  rw [add_zero] at hsum'
  have hconst : Tendsto (fun _ : ℕ => S.PP B0 F) atTop
      (𝓝 (S.vol * (S.hh F - A0 * (shSum d F : ℝ) - b0 * (totSum d F : ℝ)) + restTot S B0 Q)) :=
    hsum'.congr (fun B => by ring)
  exact tendsto_nhds_unique tendsto_const_nhds hconst

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

theorem HeightEvaluation.shSum_lineF (d : IndexData) (u : Idx d → ℚ) :
    (shSum d (lineF d u) : ℝ) = -((d.D : ℝ) + 1) * (degAt d u : ℝ) *
      ∑ τ : Fin d.f, ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) := by
  unfold shSum lineF
  simp only [ShOfPower.proof d]
  push_cast
  rw [Finset.mul_sum]

theorem HeightEvaluation.totSum_lineF (d : IndexData) (u : Idx d → ℚ) :
    (totSum d (lineF d u) : ℝ) = -((d.D : ℝ) + 1) * (degAt d u : ℝ) *
      ∑ τ : Fin d.f, ∑ i : Fin d.N, (u (τ, i) : ℝ) := by
  unfold totSum lineF
  simp only [TotOfPower.proof d]
  push_cast
  rw [Finset.mul_sum]

theorem HeightEvaluation.N_mul_ubar (d : IndexData) (u : Idx d → ℚ) (τ : Fin d.f) :
    (d.N : ℝ) * ubar d (uR d u) τ = ∑ i : Fin d.N, (u (τ, i) : ℝ) := by
  have hN : (d.N : ℝ) ≠ 0 := by
    have := d.two_le_N
    exact_mod_cast (show d.N ≠ 0 by omega)
  unfold ubar uR
  field_simp

theorem HeightEvaluation.proof (h83 : HeightTauIdentity.Statement) : HeightEvaluation.Statement := by
  intro d S hS B0 A0 b0 hA hb u Q hQ
  have key := h83 d S hS B0 A0 b0 hA hb (lineF d u) Q hQ
  have hNu := HeightEvaluation.N_mul_ubar d u
  have first : bigP S B0 u = S.vol * S.hh (lineF d u) + ((d.D : ℝ) + 1) * (S.vol * (degAt d u : ℝ)) *
      ∑ τ : Fin d.f, (A0 * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
        (d.N : ℝ) * b0 * ubar d (uR d u) τ) + restTot S B0 Q := by
    have hsum : ∑ τ : Fin d.f, (A0 * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
        (d.N : ℝ) * b0 * ubar d (uR d u) τ) =
        A0 * ∑ τ : Fin d.f, ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
          b0 * ∑ τ : Fin d.f, ∑ i : Fin d.N, (u (τ, i) : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [← hNu τ]
      ring
    rw [hsum]
    show S.PP B0 (lineF d u) = _
    rw [key, HeightEvaluation.shSum_lineF, HeightEvaluation.totSum_lineF]
    ring
  refine ⟨first, ?_⟩
  have hsum2 : ∑ τ : Fin d.f, (A0 * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
        (d.N : ℝ) * b0 * ubar d (uR d u) τ) =
      ∑ τ : Fin d.f, (A0 * cTau d (uR d u) τ + ((d.j : ℝ) * A0 + (d.N : ℝ) * b0) * ubar d (uR d u) τ) := by
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    unfold cTau uR
    ring
  rw [first, hsum2]

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem pderiv_blockPowerSum_apply (d : IndexData) (k : ℕ) (σ τ : Fin d.f) (i : Fin d.N) :
    pderiv (τ, i) (RestTerms.blockPowerSum d.f d.N k σ : XPoly d) =
      if σ = τ then (k : XPoly d) * X (τ, i) ^ (k - 1) else 0 := by
  classical
  rw [RestTerms.blockPowerSum, map_sum]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro l _ hl
      rw [pderiv_pow, pderiv_X_of_ne (show (σ, l) ≠ (σ, i) by simp [hl]), mul_zero]
    · simp
  · refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [pderiv_pow, pderiv_X_of_ne (show (σ, l) ≠ (τ, i) by simp [h]), mul_zero]

theorem intFl_blockPowerSum_mul (d : IndexData) (k : ℕ) (σ : Fin d.f) (G : XPoly d)
    (hk1 : 1 ≤ k) (hkN : k ≤ d.N) :
    intFl d (RestTerms.blockPowerSum d.f d.N k σ * G) = 0 := by
  simp only [intFl, LinearMap.smul_apply, flagIntegralLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [RestTerms.FlagIntegralKillsPowerSums.intersectionNumber_baseChange d.f d.N k σ G hk1 hkN, smul_zero]

theorem intFl_natCast_mul (d : IndexData) (n : ℕ) (G : XPoly d) :
    intFl d ((n : XPoly d) * G) = n * intFl d G := by
  rw [show (n : XPoly d) = C (n : ℚ) from (map_natCast C n).symm, C_mul', map_smul, smul_eq_mul]

theorem ShFormula.proof : ShFormula.Statement := by
  classical
  intro d τ F Q _ _ hQ
  have hinner : ∀ k : ℕ,
      ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j),
          ∑ σ : Fin d.f, pderiv (τ, i) (RestTerms.blockPowerSum d.f d.N k σ * Q k σ) =
        ∑ σ : Fin d.f, RestTerms.blockPowerSum d.f d.N k σ *
            ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), pderiv (τ, i) (Q k σ) +
          (k : XPoly d) * lowerPowerSum d (k - 1) τ * Q k τ := by
    intro k
    simp_rw [pderiv_mul, pderiv_blockPowerSum_apply, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq' univ τ, if_pos (Finset.mem_univ τ)]
    rw [add_comm, Finset.sum_comm]
    congr 1
    · simp_rw [Finset.mul_sum]
    · rw [lowerPowerSum, Finset.mul_sum, Finset.sum_mul]
  have hexp : ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), pderiv (τ, i) F =
      ∑ k ∈ Icc 1 d.N, (∑ σ : Fin d.f, RestTerms.blockPowerSum d.f d.N k σ *
            ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), pderiv (τ, i) (Q k σ) +
          (k : XPoly d) * lowerPowerSum d (k - 1) τ * Q k τ) := by
    rw [hQ]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hinner k)
  unfold shiftFl
  rw [hexp, map_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Icc] at hk
  rw [map_add, map_sum,
    Finset.sum_eq_zero (fun σ _ => intFl_blockPowerSum_mul d k σ _ hk.1 hk.2), zero_add, mul_assoc,
    intFl_natCast_mul]

theorem ShFormula.full : ShFormula.Statement := ShFormula.proof

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

theorem NormUbar.proof : NormUbar.Statement := by
  intro d u τ
  have hN : (d.N : ℝ) ≠ 0 := by
    have := d.two_le_N
    exact_mod_cast (by omega : d.N ≠ 0)
  have hNpos : (0 : ℝ) ≤ d.N := Nat.cast_nonneg _
  have key : (d.N : ℝ) * |ubar d u τ| = |∑ i : Fin d.N, u (τ, i)| := by
    unfold ubar
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (d.N : ℝ)), ← mul_assoc,
      mul_one_div_cancel hN, one_mul]
  rw [key]
  exact abs_sum_le_sum_abs _ _

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem TermA.proof : TermA.Statement := by
  intro d S hI9 u hu
  exact mul_nonneg S.vol_pos.le (hI9 u hu).1

end GroundTheory.Heights₂.Heights.TheoremB
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem TermB.proof : TermB.Statement := by
  intro d S u g B0 _hyp _hB0 hM5 Q hQ
  obtain ⟨hsum, hle⟩ := hM5 Q hQ
  have hsum' : Summable (fun p : primesAbove S B0 =>
      ‖rest₂ d S.vol (p : ℕ) (S.frob p) Q‖) := by
    simpa [Real.norm_eq_abs] using hsum
  have h1 : ‖restTot S B0 Q‖ ≤ ∑' p : primesAbove S B0, ‖rest₂ d S.vol (p : ℕ) (S.frob p) Q‖ :=
    norm_tsum_le_tsum_norm hsum'
  have h2 : |restTot S B0 Q| ≤ ∑' p : primesAbove S B0, |rest₂ d S.vol (p : ℕ) (S.frob p) Q| := by
    simpa [Real.norm_eq_abs] using h1
  exact h2.trans hle

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

theorem flagNormalisation_ne_zero (f N : ℕ) : flagNormalisation f N ≠ 0 := by
  unfold flagNormalisation
  refine div_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ?_)
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

theorem flagIntegral_blockVandermonde_pos (f N : ℕ) :
    0 < RestTerms.flagIntegral f N (RestTerms.blockVandermonde f N) := by
  unfold RestTerms.flagIntegral
  have hne : (RestTerms.blockVandermonde f N).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact RestTerms.Flag.blockVandermonde_ne_zero f N
  refine Finset.sum_pos (fun α hα => ?_) hne
  have hc : coeff α (RestTerms.blockVandermonde f N) ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  refine mul_pos (mul_self_pos.mpr hc) ?_
  exact Finset.prod_pos fun i _ => by dsimp only; exact_mod_cast Nat.factorial_pos _

theorem exists_intFl_eq_one (d : IndexData) :
    ∃ Q : XPoly d, Q.IsHomogeneous d.D ∧ intFl d Q = 1 := by
  set Δ : XPoly d := RestTerms.blockVandermonde d.f d.N
  have hΔ : Δ.IsHomogeneous d.D := RestTerms.FlagVandermondeHomogeneous.proof d.f d.N
  have hval : intFl d Δ = flagNormalisation d.f d.N * RestTerms.flagIntegral d.f d.N Δ := rfl
  have hc : intFl d Δ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (flagNormalisation_ne_zero _ _)
      (flagIntegral_blockVandermonde_pos d.f d.N).ne'
  refine ⟨(intFl d Δ)⁻¹ • Δ, ?_, ?_⟩
  · have hm : Δ ∈ homogeneousSubmodule (Idx d) ℚ d.D := (mem_homogeneousSubmodule _ _).mpr hΔ
    exact (mem_homogeneousSubmodule _ _).mp (Submodule.smul_mem _ _ hm)
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hc]

theorem TermC.proof (h₁ : HeightLimitIdentity.Statement) : TermC.Statement := by
  intro d S h82 hfl B0 A0 b0 hA hb hF
  obtain ⟨Q, hQ, hQ1⟩ := exists_intFl_eq_one d
  have e := h₁ d S h82 hfl B0 A0 b0 hA hb (tau0 S) Q hQ hQ1
  have hv : S.vol ≠ 0 := S.vol_pos.ne'
  have hval : (d.j : ℝ) * A0 + (d.N : ℝ) * b0 = -S.hB B0 := by
    rw [e, hF.1 (tau0 S) Q hQ, hQ1]
    field_simp
    push_cast
    ring
  rw [hval, abs_neg]
  exact hF.2

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset Filter Topology

theorem termD_term_le {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤ 2 * (Real.log p / p) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp0 : (0 : ℝ) < p := by linarith
  rw [mul_div_assoc', div_le_div_iff₀ hden hp0]
  nlinarith [mul_nonneg hlog (by nlinarith : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 2)]

theorem TermD.proof : TermD.Statement := by
  intro C7 hC7
  refine ⟨2 + C7 / Real.log 2, ?_⟩
  intro d S B0 A0 hB0 h7 hA
  obtain ⟨hlow, -⟩ := h7 A0 hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB0r : (2 : ℝ) ≤ B0 := by exact_mod_cast hB0
  have hlogB : Real.log 2 ≤ Real.log B0 := Real.log_le_log (by norm_num) hB0r
  have hC7le : C7 ≤ C7 / Real.log 2 * Real.log B0 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlogB hC7
  have hsum : ∑ p ∈ S.level.primeFactors.filter (fun p => B0 < p),
        (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤
      2 * ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ p ∈ S.level.primeFactors.filter (fun p => B0 < p), 2 * (Real.log p / p) :=
          Finset.sum_le_sum fun p hp =>
            termD_term_le (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).two_le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => mul_nonneg zero_le_two
            (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)))
  have hS0 : 0 ≤ ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hlogB0 : 0 ≤ Real.log B0 := le_trans hl2.le hlogB
  have hCpos : 0 ≤ C7 / Real.log 2 := div_nonneg hC7 hl2.le
  nlinarith [mul_nonneg hCpos hS0]

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem HomDecompExists.proof : HomDecompExists.Statement := by
  intro d F hF
  obtain ⟨Q, hQ, hsum⟩ := RestTerms.CoinvAboveTop.full ℚ d.f d.N (d.D + 1) F hF
    (by simp [RestTerms.Coinv.coinvTop, IndexData.D, RestTerms.topDegree])
  refine ⟨Q, hF, fun k _ τ => hQ k τ, ?_⟩
  rw [RestTerms.IsPowerSumDecomposition, hsum]
  rfl

end GroundTheory.Heights₂.Heights.TheoremB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Filter Topology

theorem KaPSplit.full : KaPSplit.Statement := KaPSplit.proof

theorem KaPInert.full : KaPInert.Statement := KaPInert.proof

theorem KaPBound.full : KaPBound.Statement := KaPBound.proof

theorem RestPBound.full : RestPBound.Statement := RestPBound.proof

theorem RestSummable.full : RestSummable.Statement := RestSummable.proof RestPBound.full

theorem HeightSumIdentity.full : HeightSumIdentity.Statement := HeightSumIdentity.proof

theorem ShTotIndependent.full : ShTotIndependent.Statement :=
  ShTotIndependent.proof ShOfPower.proof TotOfPower.proof DegPolyEval.proof CFlPos.proof

theorem ShTotInvertiblePair.full : ShTotInvertiblePair.Statement :=
  ShTotInvertiblePair.proof ShTotIndependent.full

theorem LimitsExist.full : LimitsExist.Statement :=
  LimitsExist.proof HeightSumIdentity.full ShTotInvertiblePair.full RestSummable.full

theorem HeightTauIdentity.full : HeightTauIdentity.Statement :=
  HeightTauIdentity.proof HeightSumIdentity.full RestSummable.full

theorem HeightEvaluation.full : HeightEvaluation.Statement := HeightEvaluation.proof HeightTauIdentity.full

theorem HeightLimitIdentity.full : HeightLimitIdentity.Statement :=
  HeightLimitIdentity.proof HeightTauIdentity.full ShFormula.full TotFormula.full

theorem CBounds.full : CBounds.Statement := CBounds.proof

theorem NormUbar.full : NormUbar.Statement := NormUbar.proof

theorem TermA.full : TermA.Statement := TermA.proof

theorem TermB.full : TermB.Statement := TermB.proof

theorem TermC.full : TermC.Statement := TermC.proof HeightLimitIdentity.full

theorem TermD.full : TermD.Statement := TermD.proof

theorem TheoremTUpper.full : TheoremTUpper.Statement :=
  TheoremTUpper.proof LimitsExist.full HeightEvaluation.full CBounds.full NormUbar.full TermA.full
    TermB.full TermC.full TermD.full PrimesLogSum.fullNat HomDecompExists.proof

theorem LimitTheorem.full : LimitTheorem.Statement := LimitTheorem.proof

theorem TheoremTLower.full : TheoremTLower.Statement := TheoremTLower.proof LimitTheorem.full

namespace EndSample

end EndSample

end GroundTheory.Heights₂.Heights.TheoremB
end
end
