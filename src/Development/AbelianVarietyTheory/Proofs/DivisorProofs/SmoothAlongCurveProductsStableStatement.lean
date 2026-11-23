module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlongCurveProductsStable
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

@[expose] public section

open MeasureTheory
open scoped ContDiff

theorem _root_.GlobalTheory.T.smooth_along_curve_products_stable_alt : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by
  first | exact @GlobalTheory.smooth_along_curve_products_stable | exact GlobalTheory.smooth_along_curve_products_stable | (intros; apply GlobalTheory.smooth_along_curve_products_stable <;> assumption)
