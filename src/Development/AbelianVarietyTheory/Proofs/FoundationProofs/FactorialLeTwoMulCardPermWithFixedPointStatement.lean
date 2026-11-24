module

public import Mathlib.Data.Fintype.Perm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FactorialLeTwoMulCardPermWithFixedPoint
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

@[expose] public section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint : ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α → (Fintype.card α).factorial ≤ 2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by
  first | exact @GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed | exact GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed | (intros; apply GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed <;> assumption)
