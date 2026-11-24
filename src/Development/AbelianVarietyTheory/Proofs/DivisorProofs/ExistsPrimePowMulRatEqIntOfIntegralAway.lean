module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

open IsDedekindDomain

theorem ratint_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ),
    (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) →
    ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  intro p hp q h
  have hp' : p.Prime := hp.out
  have key : ∀ {l : ℕ}, l.Prime → l ∣ q.den → l = p := by
    intro l hl hld
    by_contra hne
    have hlI : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
    let v : HeightOneSpectrum ℤ :=
      ⟨Ideal.span {(l : ℤ)}, (Ideal.span_singleton_prime hlI.ne_zero).2 hlI, by simpa using hl.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro e
      have h1 : (l : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (by
        have : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
        rw [← e] at this
        exact Ideal.mem_span_singleton.1 this |>.elim (fun c hc => by
          exact Ideal.mem_span_singleton.2 ⟨c, hc⟩))
      have h2 : l ∣ p := Int.natCast_dvd_natCast.1 h1
      exact hne ((Nat.prime_dvd_prime_iff_eq hl hp').1 h2)
    have hq := h ⟨v, hv⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hq
    have hq2 : v.valuation ℚ q ≤ 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hq
    have hb : ((q.den : ℤ)) ≠ 0 := by exact_mod_cast q.den_nz
    have hcop : ((q.den : ℤ)) ∈ v.asIdeal → q.num ∉ v.asIdeal := by
      intro hd hn
      have hd' : (l : ℤ) ∣ (q.den : ℤ) := Ideal.mem_span_singleton.1 hd
      have hn' : (l : ℤ) ∣ q.num := Ideal.mem_span_singleton.1 hn
      have hc : IsCoprime q.num (q.den : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        exact_mod_cast q.reduced
      exact hlI.not_unit (hc.isUnit_of_dvd' hn' hd')
    have e : q = ((algebraMap ℤ ℚ q.num) / (algebraMap ℤ ℚ (q.den : ℤ))) := by
      simp [Rat.num_div_den]
    rw [e, v.valuation_div_le_one_iff ℚ q.num hb hcop] at hq2
    exact hq2 (Ideal.mem_span_singleton.2 (Int.natCast_dvd_natCast.2 hld))
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hld => key hl hld)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  have : ((p : ℚ) ^ q.den.primeFactorsList.length) = (q.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.den_mul_eq_num]

end GlobalTheory
