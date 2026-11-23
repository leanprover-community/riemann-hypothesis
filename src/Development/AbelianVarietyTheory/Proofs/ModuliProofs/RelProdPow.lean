module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
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
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace GlobalTheory.RelationPowers

theorem rel_pow {G U : Type} [Monoid G] [Monoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (x : G) (c : U) (h : R x c) (k : ℕ) : R (x ^ k) (c ^ k) := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact hmul _ _ _ _ ih h

theorem rel_prod_pow {G U : Type} [Monoid G] [CommMonoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (n : ℕ) (y : Fin n → G) (c : Fin n → U) (a : Fin n → ℕ) (h : ∀ i, R (y i) (c i)) :
    R (List.prod (List.ofFn fun i : Fin n => y i ^ a i)) (∏ i : Fin n, c i ^ a i) := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact hmul _ _ _ _ (rel_pow R h1 hmul _ _ (h 0) _)
      (ih (fun i => y i.succ) (fun i => c i.succ) (fun i => a i.succ) (fun i => h i.succ))

end GlobalTheory.RelationPowers
