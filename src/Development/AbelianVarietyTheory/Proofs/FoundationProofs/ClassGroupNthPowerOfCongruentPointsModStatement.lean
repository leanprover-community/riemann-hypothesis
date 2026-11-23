module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupNthPowerOfCongruentPointsMod
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

open Polynomial

theorem _root_.GlobalTheory.T.classGroup_nthPower_of_congruent_points_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  first | exact @GlobalTheory.classGroup_nthPower_of_codim_one_mod | exact GlobalTheory.classGroup_nthPower_of_codim_one_mod | (intros; apply GlobalTheory.classGroup_nthPower_of_codim_one_mod <;> assumption)
