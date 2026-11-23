module

public import Formalism.GrowthSums.StatementA
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

theorem oddPowerInvSumIdentity : GammaIdentity := by
  intro p hp
  have hp0 : p ≠ 0 := by positivity
  have hp2 : 1 < p ^ 2 := by nlinarith
  have hq : p ^ 2 - 1 ≠ 0 := by linarith
  have hq' : p - 1 ≠ 0 := by linarith
  have hr0 : (0 : ℝ) ≤ (p ^ 2)⁻¹ := by positivity
  have hr1 : (p ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp2
  have hs := (hasSum_geometric_of_lt_one hr0 hr1).mul_left p⁻¹
  have hf : (fun n : ℕ => (p ^ (2 * n + 1))⁻¹) = fun i : ℕ => p⁻¹ * (p ^ 2)⁻¹ ^ i := by
    funext n
    rw [inv_pow, ← mul_inv]
    congr 1
    ring
  have hv : gamP p = p⁻¹ * (1 - (p ^ 2)⁻¹)⁻¹ := by
    unfold gamP rhoP
    have e : 1 - (p ^ 2)⁻¹ = (p ^ 2 - 1) / p ^ 2 := by field_simp
    rw [e, inv_div]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hf, hv]
    exact hs
  · unfold gamP rhoP
    field_simp
    ring

end Formalism.GrowthSums
