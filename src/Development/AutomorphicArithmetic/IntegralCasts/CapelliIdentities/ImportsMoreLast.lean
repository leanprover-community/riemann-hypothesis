module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.AffineMonoid.Basic
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

theorem UpperTheory.Reformulated.B.Qk10.exists_w :
    ∀ (K : Type) [inst : Field K] [NumberField K] {p : ℕ},
    Nat.Prime p →
      ∃ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (↑p : NumberField.RingOfIntegers K) ∈ w.asIdeal := by
  intro K _ _ p hp
  have hnu : ¬ IsUnit (p : NumberField.RingOfIntegers K) := by
    intro h
    have h1 : IsUnit (algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ)) := by
      simpa using h
    have h2 : IsUnit (p : ℤ) := (isUnit_map_iff _ _).mp h1
    exact (Nat.prime_iff_prime_int.mp hp).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span {(p : NumberField.RingOfIntegers K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (p : NumberField.RingOfIntegers K) ∈ M :=
    hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  rw [Ideal.mem_bot] at hmem
  exact hp.ne_zero (Nat.cast_eq_zero.mp hmem)
