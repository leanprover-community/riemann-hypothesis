module

public import Mathlib.RingTheory.AdicCompletion.Basic
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

@[expose] public section

namespace GlobalTheory.LimitSeriesPowSmul

theorem mem_pow_smul_top_iff {R : Type} [CommRing R] (p : R) (n : ℕ) (x : R) :
    x ∈ ((Ideal.span {p}) ^ n • (⊤ : Submodule R R)) ↔ p ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_limit_series {R : Type} [CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R) : ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p})
    (fun k => ∑ i ∈ Finset.range k, p ^ i * f i) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pow_smul_top_iff, ← Finset.sum_range_add_sum_Ico _ hmn,
        sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun i hi => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow p (Finset.mem_Ico.mp hi).1) _)
  exact ⟨L, fun k => (mem_pow_smul_top_iff p k _).mp ((SModEq.sub_mem).mp (hL k))⟩

theorem target : ∀ {R : Type} [inst : CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R), ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L :=
  by
  intro R _ p _ f
  exact exists_limit_series p f

end GlobalTheory.LimitSeriesPowSmul
