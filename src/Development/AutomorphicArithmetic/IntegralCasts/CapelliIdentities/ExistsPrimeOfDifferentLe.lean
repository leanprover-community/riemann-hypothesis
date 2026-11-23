module

public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

attribute [local instance] Subfield.toField._proof_1 SubfieldClass.toField._proof_12 SubringClass.toRing._proof_8

theorem UpperTheory.Reformulated.B.Qj12.exists_prime_of_different_le :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥H.F)),
    differentIdeal ℤ (NumberField.RingOfIntegers ↥H.F) ≤ v.asIdeal →
      ∃ (p : ℕ),
        Nat.Prime p ∧
          p ∣ H.QS * H.q * H.d ∧
            (↑p : NumberField.RingOfIntegers ↥H.F) ∈
              v.asIdeal := by
  intro R H v h
  have h1 := h (Ideal.absNorm_mem _)
  rw [NumberField.absNorm_differentIdeal H.F] at h1
  have h0 : (NumberField.discr H.F).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.F)
  rw [← Nat.prod_primeFactorsList h0, Nat.cast_list_prod, ← Multiset.prod_coe] at h1
  obtain ⟨x, hx, hxv⟩ := (v.isPrime.multiset_prod_mem_iff_exists_mem _).1 h1
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hx)
  have hpp := Nat.prime_of_mem_primeFactorsList hp
  refine ⟨p, hpp, H.der.discr_primes.1 p hpp ?_, hxv⟩
  rw [H.der.discr_sq]
  exact (Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactorsList hp)).trans (dvd_pow_self _ two_ne_zero)
