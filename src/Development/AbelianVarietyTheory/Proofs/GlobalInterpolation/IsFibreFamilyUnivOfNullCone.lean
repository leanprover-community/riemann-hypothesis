module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Tactic.Linter.Style
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

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem isFibreFamily_univ_of_null_cone (K V : Type) [NormedField K] [IsUltrametricDist K]
    [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (ν : Measure K) (q : V → K) (hq : Continuous q) (h0 : μ {x | q x = 0} = 0)
    (U : Set V) (B : Set K) (fib : K → Measure V) (hU : {x | q x ≠ 0} ⊆ U) (hB : {t | t ≠ 0} ⊆ B)
    (h : IsFibreFamily μ q id U ν B fib) :
    IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib := by
  classical
  obtain ⟨h1, h2, h3⟩ := h
  have hae : ∀ b, ∀ᵐ x ∂(fib b), q x = b := by
    intro b
    refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx hx'.1
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs _ => ?_⟩
  · refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx ⟨hx'.1, trivial⟩
  · have hμ : μ.restrict U = μ := by
      apply Measure.restrict_eq_self_of_ae_mem
      refine measure_mono_null ?_ h0
      intro x hx
      by_contra hx'
      exact hx (hU hx')
    rw [← h2 φ hφ, hμ, Measure.restrict_univ]
  · have key : ∀ b0 : K, b0 ≠ 0 → ∃ D : Set K, D ∈ nhds b0 ∧ b0 ∈ D ∧ D ⊆ B ∧
        (∀ b ∈ D, Integrable φ (fib b)) ∧ ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) D := by
      intro b0 hb0
      have hr : 0 < ‖b0‖ := norm_pos_iff.mpr hb0
      have hD : IsClopen (Metric.ball b0 ‖b0‖) := IsUltrametricDist.isClopen_ball b0 _
      set D := Metric.ball b0 ‖b0‖ with hDdef
      have hD0 : ∀ t ∈ D, t ≠ 0 := by
        rintro t ht rfl
        simp [hDdef] at ht
      have hE : IsClopen (q ⁻¹' D) := hD.preimage hq
      let ψ : V → ℝ := (q ⁻¹' D).indicator φ
      have hψc : Continuous ψ := hE.continuous_indicator hc
      have hψs : HasCompactSupport ψ := by
        refine hcs.mono ?_
        intro x hx hx'
        apply hx
        simp [ψ, Set.indicator, hx']
      have hψt : tsupport ψ ⊆ U := by
        have : tsupport ψ ⊆ q ⁻¹' D :=
          closure_minimal Set.support_indicator_subset hE.isClosed
        intro x hx
        exact hU (hD0 _ (this hx))
      obtain ⟨hi, hco⟩ := h3 ψ hψc hψs hψt
      have hDB : D ⊆ B := fun t ht => hB (hD0 t ht)
      have heq : ∀ b ∈ D, ψ =ᵐ[fib b] φ := by
        intro b hb
        filter_upwards [hae b] with x hx
        have : x ∈ q ⁻¹' D := by
          show q x ∈ D
          rw [hx]; exact hb
        simp [ψ, Set.indicator_of_mem this]
      refine ⟨D, Metric.ball_mem_nhds _ hr, Metric.mem_ball_self hr, hDB, fun b hb => ?_, ?_⟩
      · exact (integrable_congr (heq b hb)).mp (hi b (hDB hb))
      · refine (hco.mono hDB).congr fun b hb => ?_
        exact (integral_congr_ae (heq b hb)).symm
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨D, -, hbD, -, hi, -⟩ := key b hb
      exact hi b hbD
    · obtain ⟨D, hD, -, -, -, hco⟩ := key b hb
      exact (hco.continuousAt hD).continuousWithinAt

end GlobalTheory
