module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ep_split : ∀ (p j : ℕ), 2 ≤ p →
    HasSum (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) ((j : ℝ) / ((p : ℝ) - 1)) := by
  intro p j hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by positivity
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hr : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left ((j : ℝ) / p)
  have hf : (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) =
      fun n : ℕ => (j : ℝ) / p * (1 / (p : ℝ)) ^ n := by
    funext n
    rw [one_div_pow, pow_succ]
    field_simp
  have hv : (j : ℝ) / ((p : ℝ) - 1) = (j : ℝ) / p * (1 - 1 / (p : ℝ))⁻¹ := by
    rw [one_sub_div h0, inv_div]
    field_simp
  rw [hf, hv]
  exact hs

end GlobalTheory.CompanionTheory.Ar.Flat
