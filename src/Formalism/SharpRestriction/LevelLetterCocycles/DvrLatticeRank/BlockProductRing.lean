module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.EigenRingInvariants
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace DualFramesAlt.BlockProductRing

open PowerSeries

theorem prod_div_block {M : Type*} [CommMonoid M] (m : ℕ) (hm : 0 < m) (g : ℕ → M) (e : ℕ) :
    ∏ k ∈ Finset.range (m * e), g (k / m) = ∏ j ∈ Finset.range e, g j ^ m := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [mul_add_one, Finset.prod_range_add, ih, Finset.prod_range_succ]
    congr 1
    have hc : ∀ x ∈ Finset.range m, g ((m * e + x) / m) = g e := by
      intro x hx
      rw [Finset.mem_range] at hx
      congr 1
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hx, zero_add]
    rw [Finset.prod_congr rfl hc, Finset.prod_const, Finset.card_range]

theorem prod_ite_block {M : Type*} [CommMonoid M] (m : ℕ) (hm : 0 < m) (x : M) (k : ℕ) :
    ∏ i ∈ Finset.range k, (if i / m = k / m then x else 1) = x ^ (k % m) := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have hset : Finset.filter (fun i => i / m = k / m) (Finset.range k) = Finset.Ico (m * (k / m)) k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hik, hd⟩
      refine ⟨?_, hik⟩
      rw [← hd]
      exact Nat.mul_div_le i m
    · rintro ⟨hle, hik⟩
      refine ⟨hik, le_antisymm (Nat.div_le_div_right hik.le) ?_⟩
      rw [Nat.le_div_iff_mul_le hm, mul_comm]
      exact hle
  rw [hset, Nat.card_Ico]
  have h := Nat.mod_add_div k m
  generalize m * (k / m) = q at h ⊢
  generalize k % m = r at h ⊢
  omega

theorem dvd_of_mk_eq {O : Type*} [CommRing O] {y c : O} {F : PowerSeries O}
    (h : Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) F = Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) (C c)) :
    ∃ H, F - C c = (X - C y) * H := by
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  exact ⟨H, hH⟩

theorem mk_eq_of_mem {O : Type*} [CommRing O] {y : O} {F G : PowerSeries O} (h : F - G ∈ DualFramesAlt.eigenRingInvariants.Ia y) :
    Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) F = Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) G :=
  Ideal.Quotient.eq.mpr h

theorem mem_of_factor {O : Type*} [CommRing O] (y : O) (F : PowerSeries O) :
    (X - C y) * F ∈ DualFramesAlt.eigenRingInvariants.Ia y :=
  Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

end DualFramesAlt.BlockProductRing
