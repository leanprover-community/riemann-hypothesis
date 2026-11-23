module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjMulExpEqConjQExpansionCoeff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.integral_conj_mul_exp_eq_conj_qExpansion_coeff : ∀ (h : ℍ → ℂ) (T : ℝ) (n : ℕ) (y : ℝ), 0 < T → 0 < y → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → Function.Periodic (h ∘ ofComplex) T → IsBoundedAtImInfty h → (∫ x in (0 : ℝ)..T, (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) = T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral | exact GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral | (intros; apply GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral <;> assumption)
