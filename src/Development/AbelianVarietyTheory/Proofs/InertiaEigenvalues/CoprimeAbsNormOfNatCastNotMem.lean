module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.Linter.HaveILetI
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

namespace GlobalTheory.CoprimeAbsNorm

open NumberField IsDedekindDomain

theorem coprime_absNorm_of_natCast_notMem {E : Type} [Field E] [NumberField E]
    {P : HeightOneSpectrum (RingOfIntegers E)} {m : ℕ}
    (hm : (m : RingOfIntegers E) ∉ P.asIdeal) :
    Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpN
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : Finite (RingOfIntegers E ⧸ P.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hcard : p ∣ Nat.card (RingOfIntegers E ⧸ P.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hpN
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hcard
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have hpx : (p : RingOfIntegers E ⧸ P.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have hp0 : (p : RingOfIntegers E ⧸ P.asIdeal) = 0 :=
    (mul_eq_zero.mp hpx).resolve_right hx0
  have hpP : (p : RingOfIntegers E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  obtain ⟨k, rfl⟩ := hpm
  apply hm
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.CoprimeAbsNorm
