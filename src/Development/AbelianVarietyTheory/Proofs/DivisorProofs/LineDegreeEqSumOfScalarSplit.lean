module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleAdelicMatrixFamilyOrdersFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

namespace GlobalTheory.Nef

theorem degLine_eq_sum_of_split : ∀ (k E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field E] [Algebra k E], IsFF k E → ∀ (m n : ℕ) (G : Place k E → Matrix (Fin 2) (Fin 2) E), admitted G → ∀ (S : Place k E → Matrix (Fin n) (Fin n) E) (q : Fin n → E) (c : E) (w : Fin m → Fin 2 → E), c ≠ 0 → (∀ j, w j ≠ 0) → (∀ P, ordVec P ((S P).mulVec q) = ord P c + ∑ j, ordVec P ((G P).mulVec (w j))) → degLine S q = ∑ j, degLine G (w j) := by
  intro k E _ _ _ _ _ hE m n G hG S q c w hc hw hpt
  obtain ⟨hcfin, hcsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k E hE c hc
  have hcs : (Function.support fun P : Place k E => ord P c).Finite :=
    hcfin.subset fun P hP => by
      intro h1
      apply hP
      simp [ord, h1]
  have hjs : ∀ j, (Function.support fun P : Place k E => ordVec P ((G P).mulVec (w j))).Finite := fun j =>
    ((GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k E hE 2 G hG).2 (w j) (hw j)).1.subset fun P hP => by
      intro h1
      apply hP
      show ordVec P ((G P).mulVec (w j)) = 0
      rw [ordVec, h1]
      simp
  have hss : (Function.support fun P : Place k E => ∑ j, ordVec P ((G P).mulVec (w j))).Finite :=
    (Set.finite_iUnion fun j => hjs j).subset fun P hP => by
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
      exact Set.mem_iUnion.2 ⟨j, hj⟩
  unfold degLine
  rw [finsum_congr hpt, finsum_add_distrib hcs hss, hcsum, zero_add]
  exact finsum_sum_comm _ _ fun j _ => hjs j

end GlobalTheory.Nef
