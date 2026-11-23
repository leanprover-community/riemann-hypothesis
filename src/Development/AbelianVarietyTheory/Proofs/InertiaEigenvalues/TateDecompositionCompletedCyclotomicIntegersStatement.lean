module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, 1 ≤ j → (∀ z ∈ Ohat K, ∃ y ∈ intC (Ks K j), ∃ x ∈ Xj K j, z = y + x) ∧ (∀ y ∈ inC (Ks K j), ∀ x ∈ Xj K j, ∀ n : ℕ, (l : PadicComplex l) ^ n * y = x → y = 0) ∧ (∀ x ∈ Xj K j, x ∈ Ohat K) ∧ (∀ y ∈ intC (Ks K j), ∀ x ∈ Xj K j, y * x ∈ Xj K j) ∧ (∀ g ∈ (K0 K).fixingSubgroup, ∀ x ∈ Xj K j, act g x ∈ Xj K j) ∧ (∀ x ∈ Ohat K, ∀ y ∈ intC (Ks K j), y ≠ 0 → y * x ∈ Xj K j → x ∈ Xj K j) := by
  first | exact @GlobalTheory.TateDecomp.tate_decomposition | exact GlobalTheory.TateDecomp.tate_decomposition | (intros; apply GlobalTheory.TateDecomp.tate_decomposition <;> assumption)
