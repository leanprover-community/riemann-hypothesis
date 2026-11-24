module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Finiteness.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u_1 u_2

namespace GlobalTheory.CommonDenominatorForFinset

theorem exists_common_denominator {R : Type u_1} {A : Type u_2} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Module.Finite R A] (a : A)
    (h : ∀ b : A, ∃ s : R, s ≠ 0 ∧ ∃ r : Polynomial R,
      algebraMap R A s * b = Polynomial.aeval a r) :
    ∃ s : R, s ≠ 0 ∧ ∀ b : A, ∃ r : Polynomial R,
      algebraMap R A s * b = Polynomial.aeval a r := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := A)
  choose f hf0 r hr using h
  refine ⟨∏ b ∈ S, f b, Finset.prod_ne_zero_iff.mpr fun b _ => hf0 b, ?_⟩

  let N : Submodule R A :=
    { carrier := {b | ∃ p : Polynomial R, algebraMap R A (∏ b ∈ S, f b) * b = Polynomial.aeval a p}
      add_mem' := by
        rintro x y ⟨p, hp⟩ ⟨q, hq⟩
        exact ⟨p + q, by rw [mul_add, hp, hq, map_add (f := _)]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨p, hp⟩
        refine ⟨Polynomial.C c * p, ?_⟩
        rw [map_mul, Polynomial.aeval_C, ← hp, Algebra.smul_def]
        ring }

  have hgen : (S : Set A) ⊆ N := by
    intro b hb
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem f hb
    refine ⟨Polynomial.C t * r b, ?_⟩
    rw [map_mul, Polynomial.aeval_C, ← hr b, ht, map_mul]
    ring
  have htop : (⊤ : Submodule R A) ≤ N := by
    rw [← hS, Submodule.span_le]
    exact hgen
  intro b
  exact htop Submodule.mem_top

end GlobalTheory.CommonDenominatorForFinset
