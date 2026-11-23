module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne

@[expose] public section

open ReciprocityTheory.PGsh

theorem _root_.GlobalTheory.T.legendre_bounds_factorial_multiIndex_capelli : (∀ (l : ℕ), l.Prime → (∀ N : ℕ, 1 ≤ N → (N : ℝ) / (l - 1) - (Real.logb l N + 1) ≤ padicValNat l N.factorial ∧ (padicValNat l N.factorial : ℝ) ≤ (N - 1) / (l - 1)) ∧
    (∀ (κ : Type) [Fintype κ] (A : κ → ℕ), 1 ≤ ∑ j, A j → ((∑ j, A j : ℕ) : ℝ) / (l - 1) - Fintype.card κ * (Real.logb l ((∑ j, A j : ℕ) : ℝ) + 1) ≤ padicValNat l (∏ j, (A j).factorial)) ∧
    ∀ n₀ x : ℕ, (padicValNat l (∏ c ∈ Finset.range n₀, (x + c).factorial) : ℝ) - padicValNat l (∏ c ∈ Finset.range n₀, c.factorial) ≤
      n₀ * x / (l - 1) + n₀ * (Real.logb l n₀ + 1)) := by
  first | exact @GlobalTheory.LegendreBounds.legendre_bounds | exact GlobalTheory.LegendreBounds.legendre_bounds | (intros; apply GlobalTheory.LegendreBounds.legendre_bounds <;> assumption)
