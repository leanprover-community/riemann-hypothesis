module

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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.Qk8.exists_place :
    ∀ {F : Type} [inst : Field F] [NumberField F] (p : ℕ),
    Nat.Prime p →
      ∃ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
        (↑p : NumberField.RingOfIntegers F) ∈ w.asIdeal := by
  intro F _ _ p hp
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hinj : Function.Injective (algebraMap ℤ (NumberField.RingOfIntegers F)) :=
    (algebraMap ℤ (NumberField.RingOfIntegers F)).injective_int
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := NumberField.RingOfIntegers F) (Ideal.span {(p : ℤ)}) ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := hinj (by rw [hx, map_zero])
      rw [hx0]
      exact Ideal.zero_mem _)
  have hmem : (p : NumberField.RingOfIntegers F) ∈ Q := by
    have h : (p : ℤ) ∈ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQP]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at h
    exact h
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  intro hbot
  rw [hbot, Ideal.mem_bot] at hmem
  exact hp.ne_zero (Nat.cast_eq_zero.mp hmem)
