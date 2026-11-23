module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.CuspGeneric MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgSwap

private theorem integral_intervalIntegral_comm_of_continuous_norm_le {G : Type} [TopologicalSpace G]
    {mG : MeasurableSpace G} [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]
    (F : G × ℝ → ℂ) (hF : Continuous F) (t C : ℝ)
    (hC : ∀ x, ∀ s ∈ Set.uIcc (0 : ℝ) t, ‖F (x, s)‖ ≤ C) :
    ∫ x, (∫ s in (0 : ℝ)..t, F (x, s)) ∂μ = ∫ s in (0 : ℝ)..t, ∫ x, F (x, s) ∂μ := by
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hint : Integrable (Function.uncurry fun x s => F (x, s))
      (μ.prod (volume.restrict (Set.uIoc (0 : ℝ) t))) := by
    refine Integrable.mono' (integrable_const C) hF.aestronglyMeasurable ?_
    have hs : ∀ᵐ p ∂(μ.prod (volume.restrict (Set.uIoc (0 : ℝ) t))), p.2 ∈ Set.uIoc (0 : ℝ) t :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_uIoc)
    filter_upwards [hs] with p hp
    exact hC p.1 p.2 (Set.uIoc_subset_uIcc hp)
  simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [integral_smul]
  congr 1
  exact integral_integral_swap hint

theorem avg_intervalIntegral_swap {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G) (hΓ : IsCoLat Γ)
    (F : G × ℝ → ℂ) (hF : Continuous F) (hper : ∀ γ ∈ Γ, ∀ x s, F (γ + x, s) = F (x, s)) (t : ℝ) :
    avg Γ (fun x => ∫ s in (0 : ℝ)..t, F (x, s)) = ∫ s in (0 : ℝ)..t, avg Γ (fun x => F (x, s)) := by
  unfold GlobalTheory.CuspGeneric.IsCoLat at hΓ
  obtain ⟨-, K, hK, hKcov⟩ := hΓ
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_uIcc (a := (0 : ℝ)) (b := t))).exists_bound_of_continuousOn
    hF.continuousOn
  have hbound : ∀ x, ∀ s ∈ Set.uIcc (0 : ℝ) t, ‖F (x, s)‖ ≤ C := by
    intro x s hs
    obtain ⟨γ, hγ, hγK⟩ := hKcov x
    rw [← hper γ hγ x s]
    exact hC (γ + x, s) ⟨hγK, hs⟩
  borelize G
  unfold GlobalTheory.CuspGeneric.avg
  split_ifs with h
  · try simp only [dif_pos h]
    haveI : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      ⟨by rw [Measure.restrict_apply_univ, h.choose_spec.2.2]; exact ENNReal.one_lt_top⟩
    exact integral_intervalIntegral_comm_of_continuous_norm_le _ F hF t C hbound
  · simp only [dif_neg h, intervalIntegral.integral_zero]

end GlobalTheory.CompanionTheory.AvgSwap
