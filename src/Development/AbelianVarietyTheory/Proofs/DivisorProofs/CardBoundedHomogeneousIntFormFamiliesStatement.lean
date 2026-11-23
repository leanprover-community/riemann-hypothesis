module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBoundedHomogeneousIntFormFamilies
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

@[expose] public section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.card_bounded_homogeneous_int_form_families : ∀ (D q δ : ℕ) (R : ℝ), 0 ≤ R → {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}.Finite ∧ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}.ncard = (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ∧ Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D ∧ Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) = (q + D).choose D ∧ Module.Finite ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) := by
  first | exact @GlobalTheory.HSAmp.card_bounded_forms | exact GlobalTheory.HSAmp.card_bounded_forms | (intros; apply GlobalTheory.HSAmp.card_bounded_forms <;> assumption)
