module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.explicitRanks_basic_bounds_large_scale : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.f : ℝ) ≤ s.x ^ (3 : ℝ) ∧ (R.m : ℝ) ≤ s.x ∧ (R.r : ℝ) ≤ s.x ^ (5 : ℝ) ∧ R.k ≤ R.r ∧ R.r ≤ 2 * R.k ∧ s.L ≤ s.x ∧ 1 ≤ s.L ∧ s.x ^ ((13 : ℝ) / 2) ≤ (R.f : ℝ) * R.r * s.L ∧ (R.f : ℝ) * R.r * s.L ≤ s.x ^ ((687 : ℝ) / 100) ∧ ((R.f * R.r.choose 2 : ℕ) : ℝ) ≤ s.x ^ (12 : ℝ) ∧ (R.k : ℝ) * R.f / R.m ≤ s.x ^ (7 : ℝ) ∧ ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) ∧ s.x ^ (377 : ℝ) ≤ (R.t : ℝ) ∧ (R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ (R.N R.m : ℝ) ≤ s.x ^ (402 : ℝ) ∧ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
  first | exact @GlobalTheory.EX.rank_basic_bounds | exact GlobalTheory.EX.rank_basic_bounds | (intros; apply GlobalTheory.EX.rank_basic_bounds <;> assumption)
