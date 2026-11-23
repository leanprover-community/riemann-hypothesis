module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim

theorem tendsto_fouInf_div_integral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∀ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets → ∀ t : Ainf F, Filter.Tendsto (fun k => fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) Filter.atTop (nhds 1) := by
  intro F _ _ ψ hψ laminf _ ρ hρ hsupp t
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hg_cont : Continuous fun x : Ainf F => psiInf F ψ (x * t) := by
    have h1 : Continuous fun x : Ainf F => pairA F (x * t) 0 :=
      (continuous_mul_const t).prodMk continuous_const
    exact hψ.1.comp h1
  have hg0 : psiInf F ψ (0 * t) = 1 := by
    have h0 : pairA F (0 * t) 0 = 0 := by
      rw [zero_mul]
      rfl
    show ψ (pairA F (0 * t) 0) = 1
    rw [h0, AddChar.map_zero_eq_one]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hU : (fun x : Ainf F => psiInf F ψ (x * t)) ⁻¹' Metric.ball 1 (ε / 2) ∈ nhds (0 : Ainf F) := by
    apply hg_cont.continuousAt.preimage_mem_nhds
    rw [hg0]
    exact Metric.ball_mem_nhds _ (half_pos hε)
  filter_upwards [Filter.tendsto_smallSets_iff.1 hsupp _ hU] with k hk
  obtain ⟨hc, hcs, hnn, hI⟩ := hρ k
  have hint : Integrable (ρ k) laminf := hc.integrable_of_hasCompactSupport hcs
  have hc1 : Continuous fun x => (ρ k x : ℂ) := Complex.continuous_ofReal.comp hc
  have hcs1 : HasCompactSupport fun x => (ρ k x : ℂ) := hcs.comp_left Complex.ofReal_zero
  have hi1 : Integrable (fun x => (ρ k x : ℂ)) laminf := hc1.integrable_of_hasCompactSupport hcs1
  have hi2 : Integrable (fun x => (ρ k x : ℂ) * psiInf F ψ (x * t)) laminf :=
    (hc1.mul hg_cont).integrable_of_hasCompactSupport
      (hcs1.mul_right (f' := fun x => psiInf F ψ (x * t)))
  have key : fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)
      = ∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf := by
    unfold fouInf
    rw [← integral_complex_ofReal, ← integral_sub hi2 hi1]
    congr 1
    ext x
    ring
  have hIc : ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hI.ne'
  have hsplit : fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) - 1
      = (fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) := by
    rw [sub_div, div_self hIc]
  have hbound : ‖∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf‖ ≤ ∫ x, ρ k x * (ε / 2) ∂laminf := by
    apply norm_integral_le_of_norm_le (hint.mul_const _)
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn x)]
    by_cases hx : x ∈ tsupport (ρ k)
    · have h := hk hx
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
      exact mul_le_mul_of_nonneg_left h.le (hnn x)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [integral_mul_const] at hbound
  rw [dist_eq_norm, hsplit, key, norm_div, Complex.norm_real, Real.norm_of_nonneg hI.le, div_lt_iff₀ hI]
  nlinarith

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim
