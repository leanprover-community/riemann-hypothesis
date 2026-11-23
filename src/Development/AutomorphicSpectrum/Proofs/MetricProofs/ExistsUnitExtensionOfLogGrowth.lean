module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDomainUnitaryTriangularStatement
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_unit_extension_of_log_growth :
    ∀ (n : ℕ) (S : Finset (Fin n)) (φ : (Fin n → ℂ) → ℂ) (ρ C : ℝ) (N : ℕ), 0 < ρ →
      DifferentiableOn ℂ φ {z ∈ ball (0 : Fin n → ℂ) ρ | ∀ i ∈ S, z i ≠ 0} →
      (∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → φ z ≠ 0 ∧
        ‖φ z‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N ∧
        ‖(φ z)⁻¹‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N) →
      ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ (ball 0 ρ) ∧
        (∀ z ∈ ball (0 : Fin n → ℂ) ρ, ψ z ≠ 0) ∧
        ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ψ z = φ z := by
  intro n S φ ρ C N hρ hφ hb
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.T.removable_log_growth_singularity n S φ ρ C N hρ hφ (fun z hz hS => (hb z hz hS).2.1)
  obtain ⟨χ, hχ, hχe⟩ := GlobalTheory.T.removable_log_growth_singularity n S (fun z => (φ z)⁻¹) ρ C N hρ
    (hφ.inv fun z hz => (hb z hz.1 hz.2).1) (fun z hz hS => (hb z hz hS).2.2)
  refine ⟨ψ, hψ, fun z hz => ?_, hψe⟩
  have hF : ContinuousAt (fun w => ψ w * χ w) z :=
    ((hψ.mul hχ).differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ → (Fin n → ℂ),
      w = fun (ε : ℝ) i => if z i = 0 then (ε : ℂ) else z i := ⟨_, rfl⟩
  have hwc : Continuous w := by
    rw [hw_def]
    refine continuous_pi fun i => ?_
    by_cases h : z i = 0
    · simp only [h, if_true]
      exact continuous_ofReal
    · simp only [h, if_false]
      exact continuous_const
  have hw0 : w 0 = z := funext fun i => by by_cases h : z i = 0 <;> simp [hw_def, h]
  have hlim : Filter.Tendsto w (nhdsWithin 0 {0}ᶜ) (nhds z) := by
    rw [← hw0]
    exact hwc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) {0}ᶜ, ψ (w ε) * χ (w ε) = 1 := by
    have h1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) {0}ᶜ, w ε ∈ ball (0 : Fin n → ℂ) ρ :=
      hlim (isOpen_ball.mem_nhds hz)
    filter_upwards [h1, self_mem_nhdsWithin] with ε hε hε0
    have hS : ∀ i ∈ S, w ε i ≠ 0 := by
      intro i _
      by_cases h : z i = 0
      · simp only [hw_def, h, if_true]
        exact Complex.ofReal_ne_zero.2 hε0
      · simp only [hw_def, h, if_false]
        exact h
    rw [hψe _ hε hS, hχe _ hε hS]
    exact mul_inv_cancel₀ (hb _ hε hS).1
  have h2 : Filter.Tendsto (fun ε => ψ (w ε) * χ (w ε)) (nhdsWithin 0 {0}ᶜ) (nhds (ψ z * χ z)) :=
    hF.tendsto.comp hlim
  have h3 : ψ z * χ z = 1 :=
    tendsto_nhds_unique h2 (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
  exact left_ne_zero_of_mul_eq_one h3

end GlobalTheory.CompanionTheory.Ar.Flat
