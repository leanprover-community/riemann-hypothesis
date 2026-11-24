module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLargeVonMangoldtLogPowerSeriesNearZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.exists_large_vonMangoldtLogPowerSeries_near_zero : ∃ A C r₀ : ℝ, 1 ≤ A ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (τ r L : ℝ) (K : ℕ) (ρ : ℂ), (χ ≠ 1 ∨ 2 ≤ |τ|) → Real.log (q * (|τ| + 2)) ≤ L → 1 / L ≤ r → r ≤ r₀ → C * r * L ≤ K → LFunction χ ρ = 0 → ‖ρ - (1 + τ * I)‖ ≤ r → ∃ k : ℕ, K ≤ k ∧ k ≤ 2 * K ∧ 1 / (A * r) ^ (k + 1) ≤ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k ((1 + r : ℝ) + τ * I)‖ := by
  first | exact @GlobalTheory.NearZeroDeriv.exists_large_derSeries | exact GlobalTheory.NearZeroDeriv.exists_large_derSeries | (intros; apply GlobalTheory.NearZeroDeriv.exists_large_derSeries <;> assumption)
