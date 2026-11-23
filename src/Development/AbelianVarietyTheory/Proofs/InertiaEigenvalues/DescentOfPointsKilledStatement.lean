module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescentOfPointsKilled
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

open scoped NNReal

theorem _root_.GlobalTheory.T.descent_of_points_killed_alt : ∀ (l : ℕ) [Fact l.Prime] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : A) (pr : B →ₗ[A] A), ((l : ℕ) : B) = 0 → algebraMap A B u ∈ nonZeroDivisors B → IsHausdorff (Ideal.span {algebraMap A B u}) B → ∀ (κ : Type) [Fintype κ] (x : κ → B), (∀ (T : Type) [CommRing T] (i₁ i₂ : B →+* T), (∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a)) → IsUnit (i₁ (algebraMap A B u)) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ ψ' : B →+* O), ψ (algebraMap A B u) ≠ 0 → ¬ IsUnit (ψ (algebraMap A B u)) → IsAdicComplete (Ideal.span {ψ (algebraMap A B u)}) O → (∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a)) → ∀ j, ψ (x j) = ψ' (x j)) → pr 1 = 1 → ∀ j, x j = algebraMap A B (pr (x j)) := by
  first | exact @GlobalTheory.descent_of_points_killed | exact GlobalTheory.descent_of_points_killed | (intros; apply GlobalTheory.descent_of_points_killed <;> assumption)
