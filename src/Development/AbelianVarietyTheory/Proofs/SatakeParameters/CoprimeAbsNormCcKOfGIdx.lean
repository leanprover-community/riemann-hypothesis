module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.HostCls
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem exists_prime_ge_dvd_absNorm {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] {p : ℕ} (hp : p.Prime) (I : Ideal S) (hI : I ≠ ⊥)
    (h : p ∣ Ideal.absNorm I) :
    ∃ P : Ideal S, P.IsPrime ∧ I ≤ P ∧ p ∣ Ideal.absNorm P := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ J hJ =>
    rw [Ideal.isUnit_iff.1 hJ, Ideal.absNorm_top] at h
    exact absurd (Nat.dvd_one.1 h) hp.one_lt.ne'
  | h₃ J P hJ hP ih =>
    rw [map_mul] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact ⟨P, Ideal.isPrime_of_prime hP, Ideal.mul_le_left, h⟩
    · obtain ⟨Q, hQ, hle, hd⟩ := ih hJ h
      exact ⟨Q, hQ, Ideal.mul_le_right.trans hle, hd⟩

theorem coprime_absNorm_ccK_of_gIdx :
    ∀ (D : D7) (T p : ℕ), GIdx D.host T p → Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  intro D T p h
  obtain ⟨hp, -, hc, -⟩ := h
  have hj : jacobiSym (-(D.host.d : ℤ)) p ≠ 1 :=
    ((primeClass_eq_inert_iff _).1 hc).2.2.2.1
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  obtain ⟨P, hP, hle, hdP⟩ := exists_prime_ge_dvd_absNorm hp _ D.host.ccK_ne_bot hd
  obtain ⟨h1, h2⟩ := D.host.ccK_split P hP hle
  rw [← (Nat.prime_dvd_prime_iff_eq hp h1).1 hdP] at h2
  exact hj h2

end GlobalTheory
