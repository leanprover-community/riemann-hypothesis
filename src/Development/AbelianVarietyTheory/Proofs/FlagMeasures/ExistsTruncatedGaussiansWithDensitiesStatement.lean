module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTruncatedGaussiansWithDensities
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.exists_truncated_gaussians_with_densities : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (φ : ℕ → (Fin n → ℂ) → ℝ) (D : ℕ → ℝ → ℝ), (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ k) ∧ HasCompactSupport (φ k) ∧ (∀ y, 0 ≤ φ k y) ∧ IsDens ε (φ k) (D k)) ∧ (∀ y, Monotone (fun k => φ k y) ∧ Filter.Tendsto (fun k => φ k y) Filter.atTop (nhds (gauss y))) ∧ ∀ β : ℝ, β ≠ 0 → Filter.Tendsto (fun k => D k β) Filter.atTop (nhds (gaussDens ε β)) := by
  first | exact @GlobalTheory.GaussMean.Trunc.exists_truncated | exact GlobalTheory.GaussMean.Trunc.exists_truncated | (intros; apply GlobalTheory.GaussMean.Trunc.exists_truncated <;> assumption)
