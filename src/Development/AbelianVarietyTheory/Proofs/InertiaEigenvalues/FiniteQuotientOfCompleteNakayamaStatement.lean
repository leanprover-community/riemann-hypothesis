module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientOfCompleteNakayama
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

@[expose] public section


theorem _root_.GlobalTheory.T.module_finite_quotient_of_complete_of_span_mod_range : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → ∀ {T Z : Type} [AddCommGroup T] [Module R T] [AddCommGroup Z] [Module R Z], (∀ x : ℕ → T, ∃ y : T, ∀ n : ℕ, ∃ z : T, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) → (∀ c : Z, (∀ n : ℕ, ∃ z : Z, c = ϖ ^ n • z) → c = 0) → ∀ (d : T →ₗ[R] Z) (N : Submodule R Z), LinearMap.range d ≤ N → ∀ s : Finset Z, (∀ c : Z, ∃ (a : Z → R) (c' : Z) (x : T), c = ∑ i ∈ s, a i • i + ϖ • c' + d x) → Module.Finite R (Z ⧸ N) := by
  first | exact @GlobalTheory.finite_quotient_of_complete_nakayama | exact GlobalTheory.finite_quotient_of_complete_nakayama | (intros; apply GlobalTheory.finite_quotient_of_complete_nakayama <;> assumption)
