module

public import Mathlib.Algebra.Polynomial.Degree.Defs
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

@[expose] public section

universe u_2 u_3

namespace Bl.general_b_fact_more

private lemma aux {R : Type u_2} [CommRing R] (q : Polynomial R) (m : ℕ) (h : q.natDegree ≤ 1) :
    (q ^ m).natDegree ≤ m ∧ (q ^ m).coeff m = q.coeff 1 ^ m := by
  constructor
  · calc (q ^ m).natDegree ≤ m * q.natDegree := Polynomial.natDegree_pow_le
      _ ≤ m * 1 := Nat.mul_le_mul_left _ h
      _ = m := Nat.mul_one m
  · have h2 := Polynomial.coeff_pow_of_natDegree_le (m := m) h
    simpa only [Nat.mul_one] using h2

private lemma aux2 {R : Type u_2} {ι : Type u_3} [CommRing R] (s : Finset ι) (q : ι → Polynomial R)
    (e : ι → ℕ) (h : ∀ i, (q i).natDegree ≤ e i) :
    (s.prod q).natDegree ≤ s.sum e ∧
      (s.prod q).coeff (s.sum e) = s.prod (fun i => (q i).coeff (e i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_⟩
    · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (h a) ih.1)
    · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (h a) ih.1, ih.2]

theorem goal1 :
    ∀ {R : Type u_2} {ι : Type u_3} [inst : CommRing R] (s : Finset ι)
      (p : ι → Polynomial R) (e : ι → ℕ),
      (∀ i, (p i).natDegree ≤ 1) →
        (s.prod fun i => p i ^ e i).natDegree ≤ s.sum e ∧
          (s.prod fun i => p i ^ e i).coeff (s.sum e) =
            s.prod (fun i => (p i).coeff 1 ^ e i) := by
  intro R ι _ s p e hp
  have h := aux2 s (fun i => p i ^ e i) e (fun i => (aux (p i) (e i) (hp i)).1)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  exact Finset.prod_congr rfl (fun i _ => (aux (p i) (e i) (hp i)).2)

end Bl.general_b_fact_more
