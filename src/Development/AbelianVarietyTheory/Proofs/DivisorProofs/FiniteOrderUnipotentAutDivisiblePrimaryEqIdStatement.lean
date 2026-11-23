module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderUnipotentAutDivisiblePrimaryEqId
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


theorem _root_.GlobalTheory.T.finiteOrder_unipotent_aut_divisible_primary_eq_id : ∀ (A : Type) [AddCommGroup A] (β : A →+ A) (n g r m : ℕ), 0 < n → (∀ x : A, β^[n] x = x) → g.Prime → r + 2 ≤ g → (∀ x : A, ∃ y : A, g • y = x) → (∀ x : A, ∃ j : ℕ, g ^ j • x = 0) → (∃ T : Finset A, T.card ≤ g ^ r ∧ ∀ x : A, g • x = 0 → x ∈ T) → (∀ x : A, g • x = 0 → (fun z => β z - z)^[m] x = 0) → ∀ x : A, β x = x := by
  first | exact @GlobalTheory.finite_order_unipotent_eq_id | exact GlobalTheory.finite_order_unipotent_eq_id | (intros; apply GlobalTheory.finite_order_unipotent_eq_id <;> assumption)
