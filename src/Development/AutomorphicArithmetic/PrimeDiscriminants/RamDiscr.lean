module

public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SmallRam
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

open NumberField IsDedekindDomain Ideal

noncomputable section

namespace Formalism.HC

theorem dvd_discr_of_mem_sq (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → (p : 𝓞 E) ∈ P → (p : 𝓞 E) ∈ P ^ 2) : (p : ℤ) ∣ discr E := by
  by_contra hd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  obtain ⟨P, hPm, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (span {(p : ℤ)})
  have hP := hPm.isPrime
  have hb : span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hv : (p : 𝓞 E) ∈ P := by simpa using (Ideal.liesOver_span_iff hP.ne_top hpz).1 hlo
  have hun := (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd P hP (by simpa using hv)
  have hu : P.under ℤ = span {(p : ℤ)} := hlo.over.symm
  have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)
  have : (P.under ℤ).IsMaximal := hu ▸ hmax
  have : Finite (P.under ℤ).ResidueField := inferInstance
  have he : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (span {(p : ℤ)}) = span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P hb] at he
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h P hP hv

theorem dvd_discr_of_sqrt (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {a : E} (ha : a ^ 2 = -(p : E)) :
    (p : ℤ) ∣ discr E := by
  have hi : IsIntegral ℤ a := IsIntegral.of_pow two_pos (ha ▸ (isIntegral_natCast p).neg)
  let b : 𝓞 E := ⟨a, hi⟩
  have hb : b ^ 2 = -(p : 𝓞 E) := RingOfIntegers.ext (by
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast]; exact ha)
  refine dvd_discr_of_mem_sq E hp fun P hP hv => ?_
  have h1 : b ∈ P := hP.mem_of_pow_mem 2 (hb ▸ P.neg_mem hv)
  have h2 := (P ^ 2).neg_mem (Ideal.pow_mem_pow h1 2)
  rwa [hb, neg_neg] at h2

theorem HostAx.dvd_discr_of_dvd_QS {φ : Frame} (H : HostAx φ) (hE : H.toHostRaw.Exact) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.QS) :
    (l : ℤ) ∣ discr H.E :=
  dvd_discr_of_mem_sq H.E hl fun P _ hv => H.mem_sq_of_dvd_QS hE hl hd P hv

end Formalism.HC

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem q_dvd_discr : (H.q : ℤ) ∣ discr H.E := Formalism.HC.dvd_discr_of_sqrt H.E H.q_prime H.sqq_sq

theorem dvd_discr_iff_dvd_condN {p : ℕ} (hp : p.Prime) : (p : ℤ) ∣ discr H.E ↔ p ∣ H.condN := by
  refine ⟨H.der.discr_primes.1 p hp, fun h => ?_⟩
  rcases (H.dvd_condN_iff hp).1 h with h | rfl | rfl
  · exact H.toHostAx.dvd_discr_of_dvd_QS H.QS_exact hp h
  · exact H.q_dvd_discr
  · exact H.der.discr_primes.2.2

theorem dvd_natAbs_discr_iff {p : ℕ} (hp : p.Prime) : p ∣ (discr H.E).natAbs ↔ p ∣ H.condN :=
  Int.natCast_dvd.symm.trans (H.dvd_discr_iff_dvd_condN hp)

end Formalism.BasicNotions.Host

end
