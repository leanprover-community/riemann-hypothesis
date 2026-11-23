module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.Casselman

theorem le_one_of_forall_sqrt_mul_rpow_lt :
    ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r →
      (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by
  intro δ r hδ hδ1 hr h
  by_contra hlt
  rw [not_le] at hlt
  have hx : 0 < Real.sqrt δ * r := mul_pos (Real.sqrt_pos.mpr hδ) (by linarith)
  have hcont : ContinuousAt (fun ε : ℝ => δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε)) 0 := by
    apply ContinuousAt.mul continuousAt_const
    exact (Real.continuousAt_const_rpow hx.ne').comp
      (continuous_const.add continuous_id).continuousAt
  have h0 : δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) = r ^ 2 := by
    rw [add_zero, Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le, inv_mul_cancel_left₀ hδ.ne']
  have h1 : (1 : ℝ) < δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) := by
    rw [h0]
    nlinarith
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 1 < δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) :=
    hcont.eventually (lt_mem_nhds h1)
  obtain ⟨ε, hε1, hε0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[Set.Ioi (0 : ℝ)] 0, x ∈ Set.Ioi (0 : ℝ))).exists
  exact lt_asymm (h ε hε0) hε1

end GlobalTheory.CompanionTheory.Casselman
