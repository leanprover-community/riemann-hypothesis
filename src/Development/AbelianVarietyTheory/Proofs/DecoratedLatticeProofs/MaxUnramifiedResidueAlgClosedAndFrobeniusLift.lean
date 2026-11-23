module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubPowLe
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.IsLawOfLog
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnramifiedNearIntegralComplexPadicStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda.KurUnr

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_pow_sub_pow_le {y z : K} (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) (i : ℕ) :
    ‖y ^ i - z ^ i‖ ≤ ‖y - z‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : y ^ (i + 1) - z ^ (i + 1) = y * (y ^ i - z ^ i) + (y - z) * z ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖y‖ * ‖y ^ i - z ^ i‖ ≤ 1 * ‖y - z‖ :=
            mul_le_mul hy ih (norm_nonneg _) zero_le_one
        _ = ‖y - z‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖y - z‖ * ‖z‖ ^ i ≤ ‖y - z‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hz) (norm_nonneg _)
        _ = ‖y - z‖ := mul_one _

theorem norm_eval_sub_eval_le (f : Polynomial K) (hf : ∀ n, ‖f.coeff n‖ ≤ 1) {y z : K}
    (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) : ‖f.eval y - f.eval z‖ ≤ ‖y - z‖ := by
  rw [Polynomial.eval_eq_sum_range y, Polynomial.eval_eq_sum_range z, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖f.coeff i‖ * ‖y ^ i - z ^ i‖ ≤ 1 * ‖y - z‖ :=
        mul_le_mul (hf i) (norm_pow_sub_pow_le hy hz i) (norm_nonneg _) zero_le_one
    _ = ‖y - z‖ := one_mul _

theorem norm_root_le_one (f : Polynomial K) (hm : f.Monic) (hf : ∀ n, ‖f.coeff n‖ ≤ 1) {z : K}
    (hz : f.eval z = 0) : ‖z‖ ≤ 1 := by
  apply GlobalTheory.NormEvalSubBound.norm_le_one_of_root <;> assumption

theorem unr_of_unrOK (l : ℕ) (σ : K →+* K) (h : Formalism.InvariantFactorPaths.G7.UnrOK K l σ) : Unr K l σ := by
  obtain ⟨hp, hl2, hnl, hval, hfr⟩ := h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlK : (l : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnl
    exact (inv_pos.mpr hl0).ne' hnl.symm

  have hiso : ∀ a : K, ‖σ a‖ = ‖a‖ := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    obtain ⟨k, hk⟩ := hval a ha
    set u := a * (l : K) ^ k with hu
    have hc : ‖((l : K) ^ k)‖ = (l : ℝ)⁻¹ ^ k := by rw [norm_zpow, hnl]
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_mul, hc, hk, inv_zpow', ← zpow_add₀ hl0.ne', add_neg_cancel, zpow_zero]
    have hsu : ‖σ u‖ = 1 := by
      have h1 := hfr u hun.le
      have hup : ‖u ^ l‖ = 1 := by rw [norm_pow, hun, one_pow]
      have hne : ‖σ u - u ^ l‖ ≠ ‖u ^ l‖ := by rw [hup]; linarith
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [sub_add_cancel, hup, max_eq_right (by linarith)] at this
      exact this
    have hσu : σ u = σ a * (l : K) ^ k := by rw [hu, map_mul, map_zpow₀, map_natCast]
    have hcne : ‖((l : K) ^ k)‖ ≠ 0 := by rw [norm_ne_zero_iff]; exact zpow_ne_zero _ hlK
    have e1 : ‖σ a‖ * ‖((l : K) ^ k)‖ = ‖a‖ * ‖((l : K) ^ k)‖ := by
      rw [← norm_mul, ← norm_mul, ← hσu, ← hu, hsu, hun]
    exact mul_right_cancel₀ hcne e1
  refine ⟨hp, hl2, by rw [hnl]; exact hlinv, ?_, hiso, ?_⟩
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    obtain ⟨k, hk⟩ := hval x hx0
    rw [hnl, hk]
    have hkneg : k ≤ -1 := by
      by_contra hk1
      push_neg at hk1
      have : (1 : ℝ) ≤ (l : ℝ) ^ k := one_le_zpow₀ hl1.le (by omega)
      rw [← hk] at this
      linarith
    calc (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hl1.le hkneg
      _ = (l : ℝ)⁻¹ := zpow_neg_one _
  · intro x hx
    exact (hfr x hx).trans_lt hlinv

end GlobalTheory.Honda.KurUnr


open GlobalTheory.Honda.KurUnr in
theorem GlobalTheory.Honda.kur_resAlg_unr : ∀ (l : ℕ) [Fact l.Prime], 2 < l →
    ResAlg (MaximalUnramifiedExtension l) ∧ ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension l) l σ → Unr (MaximalUnramifiedExtension l) l σ := by
  intro l _ _
  refine ⟨?_, fun σ hσ => unr_of_unrOK l σ hσ⟩
  intro f hm hdeg hf
  set g : Polynomial ℂ_[l] := f.map (MaximalUnramifiedExtension l).subtype with hg
  have hgm : g.Monic := hm.map _
  have hgdeg : g.natDegree = f.natDegree := Polynomial.natDegree_map _
  have hgc : ∀ n, ‖g.coeff n‖ ≤ 1 := fun n => by
    rw [hg, Polynomial.coeff_map]
    exact hf n
  have hdg : g.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero, hgdeg]
    exact_mod_cast hdeg.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root g hdg
  have hz1 : ‖z‖ ≤ 1 := norm_root_le_one g hgm hgc hz
  obtain ⟨y, hyK, hy1, hzy⟩ := GlobalTheory.T.exists_unramified_near_integral_complexPadic l z hz1
  refine ⟨⟨y, hyK⟩, hy1, ?_⟩
  have hev : ((f.eval ⟨y, hyK⟩ : MaximalUnramifiedExtension l) : ℂ_[l]) = g.eval y := by
    rw [hg, Polynomial.eval_map]
    exact (Polynomial.eval₂_hom (MaximalUnramifiedExtension l).subtype ⟨y, hyK⟩).symm
  change ‖((f.eval ⟨y, hyK⟩ : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1
  rw [hev, ← sub_zero (g.eval y), ← hz]
  calc ‖g.eval y - g.eval z‖ ≤ ‖y - z‖ := norm_eval_sub_eval_le g hgc hy1 hz1
    _ = ‖z - y‖ := norm_sub_rev _ _
    _ < 1 := hzy
