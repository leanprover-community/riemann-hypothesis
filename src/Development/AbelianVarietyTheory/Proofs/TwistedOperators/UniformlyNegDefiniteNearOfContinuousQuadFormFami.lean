module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem quadForm_eventually_unif_negDef {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hc : Continuous (fun p : ℝ × V => M p.1 p.2 p.2))
    (hneg : ∀ t v, v ≠ 0 → (M t v v).re < 0) (t₀ : ℝ) :
    ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
  have hF : Continuous (fun p : ℝ × V => (M p.1 p.2 p.2).re) := Complex.continuous_re.comp hc
  have hscale : ∀ t (c : ℝ) (u : V), (M t (c • u) (c • u)).re = c ^ 2 * (M t u u).re := by
    intro t c u
    simp only [map_smul, LinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
    ring
  have key : ∀ (ε : ℝ) (t : ℝ), (∀ u ∈ Metric.sphere (0:V) 1, (M t u u).re < -ε) →
      ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
    intro ε t ht x
    by_cases hx : x = 0
    · subst hx; simp
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0:V) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have h1 := ht _ hu
      have hx' : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      have h2 : (M t x x).re = ‖x‖ ^ 2 * (M t (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re := by
        conv_lhs => rw [hx']
        exact hscale t _ _
      rw [h2]
      have hp : 0 ≤ ‖x‖ ^ 2 := by positivity
      nlinarith
  have hS : IsCompact (Metric.sphere (0:V) 1) := isCompact_sphere 0 1
  rcases (Metric.sphere (0:V) 1).eq_empty_or_nonempty with hE | hNE
  · refine ⟨1, one_pos, Filter.Eventually.of_forall fun t => key 1 t ?_⟩
    intro u hu
    rw [hE] at hu
    exact absurd hu (Set.notMem_empty _)
  · have hcont0 : ContinuousOn (fun u : V => (M t₀ u u).re) (Metric.sphere 0 1) :=
      (hF.comp (Continuous.prodMk_right t₀)).continuousOn
    obtain ⟨u₀, hu₀, hmax⟩ := hS.exists_isMaxOn hNE hcont0
    have hu₀0 : u₀ ≠ 0 := by
      rintro rfl
      simp at hu₀
    have hm : (M t₀ u₀ u₀).re < 0 := hneg t₀ u₀ hu₀0
    refine ⟨-(M t₀ u₀ u₀).re / 2, by linarith, ?_⟩
    have hev : ∀ᶠ t in nhds t₀, ∀ u ∈ Metric.sphere (0:V) 1,
        (M t u u).re < -(-(M t₀ u₀ u₀).re / 2) := by
      apply hS.eventually_forall_of_forall_eventually
      intro u hu
      have hlt : (M t₀ u u).re < -(-(M t₀ u₀ u₀).re / 2) := by
        have := hmax hu
        simp only [Set.mem_setOf_eq] at this
        linarith
      exact hF.continuousAt.eventually_lt continuousAt_const hlt
    exact hev.mono fun t ht => key _ t ht

theorem quadForm_unif_target : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    Continuous (fun p : ℝ × V => M p.1 p.2 p.2) → (∀ t v, v ≠ 0 → (M t v v).re < 0) →
    ∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) :=
  fun M hc hneg t₀ => quadForm_eventually_unif_negDef M hc hneg t₀

end GlobalTheory
