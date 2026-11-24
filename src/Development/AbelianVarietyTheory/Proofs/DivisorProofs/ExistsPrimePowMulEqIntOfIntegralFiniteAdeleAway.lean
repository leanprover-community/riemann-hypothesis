module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.RatDenAwayP

theorem val_le_one (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) (v : AwayP p) :
    v.1.valuation ℚ q ≤ 1 := by
  have h1 : (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) v.1 ∈ v.1.adicCompletionIntegers ℚ := h v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  exact h1

def primeHOS (l : ℕ) (hl : l.Prime) : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(l : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl)
  ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero

theorem prime_dvd_den (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) {l : ℕ} (hl : l.Prime)
    (hd : l ∣ q.den) : l = p := by
  by_contra hne
  have hv : (primeHOS l hl).asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro e
    have e' : Ideal.span {(l : ℤ)} = Ideal.span {(p : ℤ)} := e
    rw [Ideal.span_singleton_eq_span_singleton] at e'
    have h1 : l ∣ p := Int.natCast_dvd_natCast.1 e'.dvd
    have h2 : p ∣ l := Int.natCast_dvd_natCast.1 e'.symm.dvd
    exact hne (Nat.dvd_antisymm h1 h2)
  let v : AwayP p := ⟨primeHOS l hl, hv⟩
  have hq := val_le_one p q h v
  have hden : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) < 1 := by
    rw [valuation_lt_one_iff_mem]
    show ((q.den : ℤ)) ∈ Ideal.span {(l : ℤ)}
    rw [Ideal.mem_span_singleton]; exact_mod_cast hd
  have hnum : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ q.num) < 1 := by
    have e : algebraMap ℤ ℚ q.num = q * algebraMap ℤ ℚ (q.den : ℤ) := by
      rw [algebraMap_int_eq, eq_intCast, eq_intCast, Int.cast_natCast, Rat.mul_den_eq_num]
    rw [e, map_mul]
    calc (primeHOS l hl).valuation ℚ q * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ))
        ≤ 1 * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) := by gcongr
      _ < 1 := by rw [one_mul]; exact hden
  rw [valuation_lt_one_iff_mem] at hnum
  change q.num ∈ Ideal.span {(l : ℤ)} at hnum
  rw [Ideal.mem_span_singleton, Int.natCast_dvd] at hnum
  have hc : Nat.Coprime l q.den := Nat.Coprime.coprime_dvd_left hnum q.reduced
  exact (Nat.Prime.coprime_iff_not_dvd hl).1 hc hd

end GlobalTheory.RatDenAwayP

namespace GlobalTheory

theorem ratDen_pow_of_intAfP : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p →
    ∃ k : ℕ, ∃ a : ℤ, ((p ^ k : ℕ) : ℚ) * q = a := by
  intro p _ q h
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hd => RatDenAwayP.prime_dvd_den p q h hl hd)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  rw [← hden]
  exact Rat.den_mul_eq_num q

end GlobalTheory
