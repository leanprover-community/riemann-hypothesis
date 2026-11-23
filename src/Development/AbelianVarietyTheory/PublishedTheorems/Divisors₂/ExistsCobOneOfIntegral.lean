module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonneAt

@[expose] public section

noncomputable section

open CategoryTheory WittVector Ideal TensorProduct Coalgebra

namespace GlobalTheory.PrismModel

open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

section Eps

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

private theorem zeta_add_pow_p_pow_eq_zeta (ε : PreTilt O p) (n k : ℕ) :
    zeta ε (n + k) ^ p ^ k = zeta ε n := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, zeta_succ_pow, ih]

theorem isPrimitiveSystem_of_one {ε : PreTilt O p} (h : IsPrimitiveRoot (zeta ε 1) p) :
    IsPrimitiveSystem ε := by
  intro n
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    have h0 := zeta_add_pow_p_pow_eq_zeta ε 0 1
    rw [zero_add, pow_one] at h0
    rw [← h0, h.pow_eq_one]
  | succ n =>
    have h1 : zeta ε (n + 1) ^ p ^ n = zeta ε 1 := by
      have h2 := zeta_add_pow_p_pow_eq_zeta ε 1 n
      rwa [add_comm 1 n] at h2
    rw [IsPrimitiveRoot.iff_orderOf]
    apply orderOf_eq_prime_pow
    · rw [h1]
      exact h.ne_one (Fact.out : p.Prime).one_lt
    · rw [pow_succ, pow_mul, h1, h.pow_eq_one]

end Eps

section Mu

variable {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A]

variable {p : ℕ} [Fact p.Prime]

end Mu

end GlobalTheory.PrismModel
