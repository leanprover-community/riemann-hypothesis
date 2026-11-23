module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Multiset.ZeroCons
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

theorem UpperTheory.Reformulated.B.PairCases.pair_cases :
    ∀ {a b c d : @Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)},
      @Eq (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
          (@Insert.insert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
            (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
            (@Multiset.instInsert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) a
            (@Singleton.singleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
              (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
              (@Multiset.instSingleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) b))
          (@Insert.insert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
            (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
            (@Multiset.instInsert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) c
            (@Singleton.singleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
              (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
              (@Multiset.instSingleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) d)) →
        Or
          (And (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) a c)
            (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) b d))
          (And (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) a d)
            (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) b c)) := by
  intro a b c d h
  rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons] at h
  rcases Multiset.cons_eq_cons.mp h with ⟨h1, h2⟩ | ⟨_, cs, h2, h3⟩
  · exact Or.inl ⟨h1, Multiset.singleton_inj.mp h2⟩
  · exact Or.inr ⟨(Multiset.singleton_eq_cons_iff _ |>.mp h3).1.symm,
      (Multiset.singleton_eq_cons_iff _ |>.mp h2).1⟩
