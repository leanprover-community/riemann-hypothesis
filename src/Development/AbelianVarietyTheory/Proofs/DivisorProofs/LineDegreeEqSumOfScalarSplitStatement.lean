module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDegreeEqSumOfScalarSplit
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

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

theorem _root_.GlobalTheory.T.lineDegree_eq_sum_of_scalar_split : ∀ (k E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field E] [Algebra k E], IsFF k E → ∀ (m n : ℕ) (G : Place k E → Matrix (Fin 2) (Fin 2) E), admitted G → ∀ (S : Place k E → Matrix (Fin n) (Fin n) E) (q : Fin n → E) (c : E) (w : Fin m → Fin 2 → E), c ≠ 0 → (∀ j, w j ≠ 0) → (∀ P, ordVec P ((S P).mulVec q) = ord P c + ∑ j, ordVec P ((G P).mulVec (w j))) → degLine S q = ∑ j, degLine G (w j) := by
  first | exact @GlobalTheory.Nef.degLine_eq_sum_of_split | exact GlobalTheory.Nef.degLine_eq_sum_of_split | (intros; apply GlobalTheory.Nef.degLine_eq_sum_of_split <;> assumption)
