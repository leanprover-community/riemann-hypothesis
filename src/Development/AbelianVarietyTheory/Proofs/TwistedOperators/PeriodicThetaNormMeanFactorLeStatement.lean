module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodicThetaNormMeanFactorLe
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

theorem _root_.GlobalTheory.T.periodic_theta_norm_mean_factor_le : ∀ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (p n : ℕ) (v : Fin n → (Fin g → ℂ)) (T : ℝ), Countable Λ → Countable Λ' → MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume → 0 < p → (∀ a ∈ Λ, h a ∈ Λ') → (∀ z, 0 ≤ u z) → (∀ z, 0 ≤ u' z) → (∀ a ∈ Λ, ∀ z, u (z + a) = u z) → (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) → (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 → (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 → (∀ z, T * u' (h z) ≤ ∑ m, u ((p : ℂ) • z + v m)) → T ≤ n := by
  first | exact @GlobalTheory.PeriodicMean.mean_factor_le | exact GlobalTheory.PeriodicMean.mean_factor_le | (intros; apply GlobalTheory.PeriodicMean.mean_factor_le <;> assumption)
