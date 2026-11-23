module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitRootAnalytic
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


theorem _root_.GlobalTheory.T.implicit_root_analytic : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ) (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ), (∀ j, AnalyticAt ℂ (c j) w₀) → ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0 → ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0 → ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧ AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W, ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  first | exact @GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root | exact GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root | (intros; apply GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root <;> assumption)
