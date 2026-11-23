module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin


open Polynomial SemidirectProduct in
open scoped Classical in
theorem _root_.GlobalTheory.Shin.rootSum_map_frobeniusPow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F →+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (k : ℕ) (P : F[X]), _root_.GlobalTheory.CuspGL.rootSum θ k (P.map t) = _root_.GlobalTheory.CuspGL.rootSum θ (k * ringChar F ^ j) P := by
  intro F _ _ θ t j ht k P
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  haveI : CharP (AlgebraicClosure F) (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective (ringChar F)
  haveI : ExpChar (AlgebraicClosure F) (ringChar F) := ExpChar.prime Fact.out
  unfold _root_.GlobalTheory.CuspGL.rootSum
  have hmap : (P.map t).map (algebraMap F (AlgebraicClosure F)) =
      (P.map (algebraMap F (AlgebraicClosure F))).map
        (iterateFrobenius (AlgebraicClosure F) (ringChar F) j) := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [iterateFrobenius_def, ht, map_pow]
  rw [hmap, ← roots_map_of_injective_of_card_eq_natDegree
    (iterateFrobenius (AlgebraicClosure F) (ringChar F) j).injective
    IsAlgClosed.card_roots_eq_natDegree, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun α _ => ?_
  rw [Function.comp_apply, iterateFrobenius_def, map_pow, ← pow_mul, mul_comm]

end GlobalTheory.Shin
