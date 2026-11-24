module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AI

def interp {VW : Type*} (k i : ℕ) (x₁ x₂ a : VW) : ℕ → VW :=
  fun j => if j = 0 then x₂ else if j < 1 + 2 * i then x₁ else if j < 1 + 2 * k then x₂ else a

def consWord {VW : Type*} (k i : ℕ) (x x₁ x₂ a : VW) : ℕ → VW :=
  fun j => if j < 2 then x else if j = 2 then x₂ else if j < 3 + 2 * i then x₁ else
    if j < 1 + 2 * k then x₂ else a

theorem cons_cons_word {VW : Type*} (D k i : ℕ) (hk : 1 ≤ k) (x x₁ x₂ a : VW) :
    (Fin.cons x (Fin.cons x (word D k i x₁ x₂ a)) : Fin (D + 2) → VW) =
      fun j : Fin (D + 2) => consWord k i x x₁ x₂ a j := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [consWord]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [consWord]
    · simp only [Fin.cons_succ, consWord, word, Fin.val_succ]
      split_ifs <;> first | rfl | omega

end ReciprocityTheory.ChartRestriction.G.AI
