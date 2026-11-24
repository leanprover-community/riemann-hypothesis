module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory
open scoped Pointwise

theorem UpperTheory.V.Af.Nf.avgZero :
    UpperTheory.V.Af.Nf.AvgZero := by
  intro G _ _ _ _ _ _ _ Γ _ μ 𝓕 hμ h𝓕 ψ hψ hinv e he N hN havg
  by_cases hint : IntegrableOn ψ 𝓕 μ
  swap
  · exact integral_undef hint
  have hΓ : ∀ (g : Γ) (x : G), ψ (g +ᵥ x) = ψ x := fun g x => hinv g g.2 x
  have hF : ∀ a : G, IsAddFundamentalDomain Γ ((fun x => a + x) '' 𝓕) μ := fun a => h𝓕.vadd_of_comm a
  have hmp : ∀ a : G, MeasurePreserving (fun x => a + x) μ μ := fun a => measurePreserving_add_left μ a
  have hem : ∀ a : G, MeasurableEmbedding (fun x : G => a + x) := fun a => measurableEmbedding_addLeft a
  have h1 : ∀ a : G, ∫ x in 𝓕, ψ (a + x) ∂μ = ∫ x in 𝓕, ψ x ∂μ := fun a => by
    rw [← (hmp a).setIntegral_image_emb (hem a) ψ 𝓕]
    exact (hF a).setIntegral_eq h𝓕 hΓ
  have h2 : ∀ a : G, ∫ x in 𝓕, ‖ψ (a + x)‖ ∂μ = ∫ x in 𝓕, ‖ψ x‖ ∂μ := fun a => by
    rw [← (hmp a).setIntegral_image_emb (hem a) (fun x => ‖ψ x‖) 𝓕]
    exact (hF a).setIntegral_eq h𝓕 fun g x => by rw [hΓ]
  have h3 : ∀ a : G, IntegrableOn (fun x => ψ (a + x)) 𝓕 μ := fun a =>
    ((hmp a).integrableOn_image (hem a)).1 (((hF a).integrableOn_iff h𝓕 hΓ).2 hint)
  have hc : Continuous (Function.uncurry fun (t : ℝ) (x : G) => ψ (e t + x)) :=
    hψ.comp ((he.comp continuous_fst).add continuous_snd)
  have hI : Integrable (Function.uncurry fun (t : ℝ) (x : G) => ψ (e t + x))
      ((volume.restrict (Set.Ioc (0 : ℝ) N)).prod (μ.restrict 𝓕)) := by
    rw [integrable_prod_iff hc.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun t => h3 (e t), ?_⟩
    simp only [Function.uncurry_apply_pair, h2]
    exact integrable_const _
  have hs := integral_integral_swap hI
  simp only [h1, ← intervalIntegral.integral_of_le hN.le, havg, integral_zero, intervalIntegral.integral_const,
    sub_zero, smul_eq_zero, hN.ne', false_or] at hs
  exact hs
