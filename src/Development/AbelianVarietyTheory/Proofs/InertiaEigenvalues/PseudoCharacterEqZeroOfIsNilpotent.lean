module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace GlobalTheory.PsChar

theorem alt_pow_eq_prod {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (y : M)
    (hy : ∀ m : ℕ, 2 ≤ m → T (y ^ m) = 0) :
    ∀ (n : ℕ) (z : Fin n → M), (∀ i, ∃ a : ℕ, 1 ≤ a ∧ z i = y ^ a) →
      alt T n z = ∏ i, T (z i) := by
  intro n
  induction n with
  | zero => simp [alt]
  | succ n ih =>
    intro z hz
    obtain ⟨a, ha, hza⟩ := hz 0
    have hs : ∑ i : Fin n, alt T n (Function.update (Fin.tail z) i (z 0 * Fin.tail z i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      obtain ⟨b, hb, hzb⟩ := hz i.succ
      have he : z 0 * Fin.tail z i = y ^ (a + b) := by
        rw [pow_add, ← hza, ← hzb]; rfl
      rw [he, ih]
      · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [Function.update_self]
        exact hy _ (by omega)
      · intro j
        by_cases hj : j = i
        · subst hj
          exact ⟨a + b, by omega, by rw [Function.update_self]⟩
        · rw [Function.update_of_ne hj]
          exact hz j.succ
    rw [alt, ih (Fin.tail z) (fun i => hz i.succ), hs, sub_zero, Fin.prod_univ_succ]
    simp only [Fin.tail_def]

theorem IsPsChar.apply_eq_zero_of_pow {M A : Type*} [Monoid M] [CommRing A] [IsReduced A] {d : ℕ} {T : M → A}
    (hT : IsPsChar d T) (y : M) (hy : ∀ m : ℕ, 2 ≤ m → T (y ^ m) = 0) : T y = 0 := by
  have h := alt_pow_eq_prod T y hy (d + 1) (fun _ => y) (fun _ => ⟨1, le_rfl, (pow_one y).symm⟩)
  rw [hT.alt_eq_zero] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact IsNilpotent.eq_zero ⟨d + 1, h.symm⟩

theorem apply_eq_zero_of_isNilpotent (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ)
    (T : R →ₗ[k] k) (hT : IsPsChar d (fun x => T x)) (x : R) (hx : IsNilpotent x) : T x = 0 := by
  obtain ⟨N, hN⟩ := hx
  have key : ∀ r j : ℕ, 1 ≤ j → N ≤ j + r → T (x ^ j) = 0 := by
    intro r
    induction r with
    | zero =>
      intro j _ hj
      rw [pow_eq_zero_of_le (by simpa using hj) hN, map_zero]
    | succ r ih =>
      intro j h1 hj
      refine hT.apply_eq_zero_of_pow (x ^ j) fun m hm => ?_
      show T ((x ^ j) ^ m) = 0
      rw [← pow_mul]
      have : j * 2 ≤ j * m := Nat.mul_le_mul_left j hm
      exact ih _ (by omega) (by omega)
  simpa using key N 1 le_rfl (by omega)

end GlobalTheory.PsChar
