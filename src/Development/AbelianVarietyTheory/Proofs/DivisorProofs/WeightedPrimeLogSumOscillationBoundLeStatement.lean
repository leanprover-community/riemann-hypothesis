module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedPrimeLogSumOscillationBoundLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.weightedPrimeLogSum_oscillationBound_le : ∀ (F N k m M : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (large₂ ll : ℝ) (S₀ R : Finset ℕ), 0 ≤ Mb → 0 ≤ Sm → (∀ q, 0 ≤ vd q) → N + 1 = k + m → m ≤ k → 1 ≤ m → 1 ≤ large₂ → 1 ≤ ll → Real.log M ≤ large₂ → Real.log N ≤ large₂ → ∑ q ∈ S₀, (1 + vd q / 2) * Real.log q ≤ 3 / 2 * large₂ → Real.log (Real.log k) ≤ ll → R.card ≤ 2 → (∀ q ∈ R, N * Real.log q / ((q : ℝ) - 1) ≤ m * large₂) → PrimeSum ((Finset.range (M + 1)).filter Nat.Prime) (fun p => if p.Prime then eOf F N k m Mb Sm vd M S₀ R p else 0) (40 * ((F * m * Mb + Sm) * large₂ * ll + F * (N : ℝ) ^ 3 * large₂ + M)) := by
  first | exact @GlobalTheory.SumBound.primeSum_eOf | exact GlobalTheory.SumBound.primeSum_eOf | (intros; apply GlobalTheory.SumBound.primeSum_eOf <;> assumption)
