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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

namespace NP

open IsDedekindDomain

variable {k : Type} [Field k] [NumberField k]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 k)) : ∃ p : Nat.Primes, ((p : ℕ) : 𝓞 k) ∈ v.asIdeal := by
  have hP : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 k) ∈ v.asIdeal → ∃ p : Nat.Primes, ((p : ℕ) : 𝓞 k) ∈ v.asIdeal := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro _ h; exact absurd (by simpa using h) (v.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).2)
    | prime q hq => intro _ h; exact ⟨⟨q, hq⟩, h⟩
    | mul a b ha hb =>
      intro hab h
      rw [Nat.cast_mul] at h
      rcases v.isPrime.mem_or_mem h with h | h
      · exact ha (fun h0 => hab (by rw [h0, zero_mul])) h
      · exact hb (fun h0 => hab (by rw [h0, mul_zero])) h
  exact hP _ (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem v.asIdeal)

theorem prime_unique (v : HeightOneSpectrum (𝓞 k)) {p q : Nat.Primes} (hp : ((p : ℕ) : 𝓞 k) ∈ v.asIdeal)
    (hq : ((q : ℕ) : 𝓞 k) ∈ v.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes p.2 q.2).2 fun h => hne (Subtype.ext h)
  obtain ⟨u, w, huw⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 k))
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huw]
  simp only [eq_intCast, Int.cast_natCast]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hq)

theorem finite_over (p : Nat.Primes) : {v : HeightOneSpectrum (𝓞 k) | ((p : ℕ) : 𝓞 k) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((p : ℕ) : 𝓞 k)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast p.2.ne_zero
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

end NP

end PositivityTheory.Xgf
