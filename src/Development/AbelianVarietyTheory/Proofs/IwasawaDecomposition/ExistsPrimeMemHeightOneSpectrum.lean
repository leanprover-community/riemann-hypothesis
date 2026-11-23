module

import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPrincipalIdealRingLoc
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

namespace GlobalTheory.PrimeInHeightOneSpectrum

theorem exists_prime_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ P := by
  apply GlobalTheory.PlaceInt.LocBasis.exists_prime_mem <;> assumption

theorem exists_prime_mem_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  haveI := v.isPrime
  exact exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal)
    (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot) (Ideal.absNorm_mem _)

theorem target : ∀ {K : Type} [inst : Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v :=
  fun v => exists_prime_mem_heightOneSpectrum v

end GlobalTheory.PrimeInHeightOneSpectrum
