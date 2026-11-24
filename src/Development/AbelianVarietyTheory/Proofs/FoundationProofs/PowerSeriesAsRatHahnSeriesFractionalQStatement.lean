module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesAsRatHahnSeriesFractionalQ
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.powerSeries_as_rat_hahnSeries_fractional_q : ∀ (Ω : Type) [Field Ω] (N : ℕ), 0 < N → ∃ Φ : PowerSeries Ω →+* HahnSeries ℚ Ω, (∀ (p : PowerSeries Ω) (k : ℕ), (Φ p).coeff ((k : ℚ) / N) = PowerSeries.coeff k p) ∧ ∀ (p : PowerSeries Ω) (r : ℚ), (∀ k : ℕ, r ≠ (k : ℚ) / N) → (Φ p).coeff r = 0 := by
  first | exact @GlobalTheory.powerSeries_to_hahnSeries_rat | exact GlobalTheory.powerSeries_to_hahnSeries_rat | (intros; apply GlobalTheory.powerSeries_to_hahnSeries_rat <;> assumption)
