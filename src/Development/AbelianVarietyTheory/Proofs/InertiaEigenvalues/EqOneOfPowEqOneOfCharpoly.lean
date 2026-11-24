module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Separable

@[expose] public section

open Polynomial

namespace GlobalTheory.FinOrd

theorem eq_one_of_pow_eq_one_of_charpoly (K : Type) [Field K] [CharZero K] (N : ℕ)
    (M : Matrix (Fin N) (Fin N) K) (h : ∃ m : ℕ, 0 < m ∧ M ^ m = 1)
    (hc : M.charpoly = (X - 1) ^ N) : M = 1 := by
  obtain ⟨m, hm, hM⟩ := h
  have hpr : Prime (X - 1 : K[X]) := by simpa using prime_X_sub_C (1 : K)

  have hsep : (X ^ m - 1 : K[X]).Separable := by
    simpa using separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero
  have h1 : minpoly K M ∣ X ^ m - 1 := minpoly.dvd_iff.2 (by simp [hM])

  have h2 : minpoly K M ∣ (X - 1) ^ N := by
    rw [← hc]; exact minpoly.dvd_iff.2 (Matrix.aeval_self_charpoly M)
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hpr N).1 h2

  have hsi : ((X - 1 : K[X]) ^ i).Separable := hsep.of_dvd (hi.symm.dvd.trans h1)
  have hle : minpoly K M ∣ X - 1 := by
    rcases hsi.of_pow' with hu | ⟨-, rfl⟩ | rfl
    · exact absurd hu hpr.not_unit
    · simpa using hi.dvd
    · exact hi.dvd.trans (by simp)
  have h0 : Polynomial.aeval M (X - 1 : K[X]) = 0 := minpoly.dvd_iff.1 hle
  simpa [sub_eq_zero] using h0

end GlobalTheory.FinOrd
