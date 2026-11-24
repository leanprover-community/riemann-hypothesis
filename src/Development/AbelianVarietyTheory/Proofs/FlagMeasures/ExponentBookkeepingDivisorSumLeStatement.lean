module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExponentDivisorSumLe
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped BigOperators

theorem _root_.GlobalTheory.T.exponent_divisor_sum_le : ∀ (k f r : ℕ) (G N H a Q C : ℝ), 1 ≤ k → 1 ≤ r → 1 ≤ f → Real.log f ≤ Real.sqrt r → 1 ≤ G → 1 ≤ N → G ≤ H → N ≤ H → 0 ≤ a → 0 ≤ Q → Q * 9 ^ f ≤ H → 60 ≤ C → ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, ((de : ℝ) / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * Real.logb 2 f)) * ((G / de) ^ ((k : ℝ) + Real.logb 2 (2 * f) + 1) * (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  first | exact @GlobalTheory.exponent_sum_le | exact GlobalTheory.exponent_sum_le | (intros; apply GlobalTheory.exponent_sum_le <;> assumption)
