module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AffineChangeFundamentalDomainMeanPeriodic
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

theorem _root_.GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic : ∀ (g : ℕ) (Λ' Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd' : Set (Fin g → ℂ)) (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (c : Fin g → ℂ) (f : (Fin g → ℂ) → ℝ), Countable Λ' → (∀ z, L z ∈ Λ' ↔ z ∈ Λ₁) → IsAddFundamentalDomain Λ' Fd' volume → (∀ a ∈ Λ', ∀ z, f (z + a) = f z) → (∫ z in Fd', f z) / (volume Fd').toReal = 1 → IsAddFundamentalDomain Λ₁ ((fun z => L z + c) ⁻¹' Fd') volume ∧ (∫ z in (fun z => L z + c) ⁻¹' Fd', f (L z + c)) / (volume ((fun z => L z + c) ⁻¹' Fd')).toReal = 1 := by
  first | exact @GlobalTheory.AffineMean.affine_fundamentalDomain_mean | exact GlobalTheory.AffineMean.affine_fundamentalDomain_mean | (intros; apply GlobalTheory.AffineMean.affine_fundamentalDomain_mean <;> assumption)
