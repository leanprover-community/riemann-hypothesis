module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Mathlib.NumberTheory.NumberField.CMField
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
public import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.SplitPlace

theorem two_primes (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (p : Ideal (𝓞 F)) [p.IsMaximal] (P P' : p.primesOver (𝓞 E)) (hne : P ≠ P') :
    (∀ R : p.primesOver (𝓞 E), R = P ∨ R = P') ∧
      ∀ R : p.primesOver (𝓞 E), R.1.ramificationIdx (𝓞 F) * R.1.inertiaDeg (𝓞 F) = 1 := by
  classical
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, h2] at hsum
  have hpos : ∀ P : p.primesOver (𝓞 E),
      1 ≤ P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) := fun P =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hall : ∀ R : p.primesOver (𝓞 E), R = P ∨ R = P' := by
    intro R
    by_contra hR
    push Not at hR
    have h3 := Finset.sum_le_sum_of_subset (f := fun P : p.primesOver (𝓞 E) =>
      P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (Finset.subset_univ {R, P, P'})
    rw [hsum, Finset.sum_insert (by simp [hR.1, hR.2]), Finset.sum_pair hne] at h3
    have := hpos R
    have := hpos P
    have := hpos P'
    omega
  refine ⟨hall, fun R => ?_⟩
  have h3 := Finset.sum_le_sum_of_subset (f := fun P : p.primesOver (𝓞 E) =>
    P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (Finset.subset_univ {P, P'})
  rw [hsum, Finset.sum_pair hne] at h3
  have := hpos P
  have := hpos P'
  rcases hall R with rfl | rfl <;> omega

theorem split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → (∀ P P' : HeightOneSpectrum (𝓞 E), Over P v → Over P' v → P ≠ P' → ∀ R : HeightOneSpectrum (𝓞 E), Over R v → R = P ∨ R = P') ∧ ∀ P : HeightOneSpectrum (𝓞 E), Over P v → Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ (∀ (a : OF E) (k : ℕ), algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ k ↔ a ∈ v.asIdeal ^ k) ∧ ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal := by
  intro E _ _ _ v hv
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  have hm : ∀ P : HeightOneSpectrum (𝓞 E), Over P v → P.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) :=
    fun P h => ⟨P.isPrime, ⟨h.symm⟩⟩
  have hne : ∀ P P' (h : Over P v) (h' : Over P' v), P ≠ P' →
      (⟨_, hm P h⟩ : v.asIdeal.primesOver (𝓞 E)) ≠ ⟨_, hm P' h'⟩ :=
    fun P P' h h' hn he => hn (HeightOneSpectrum.ext (congrArg Subtype.val he))
  refine ⟨fun P P' h h' hn R hR => ?_, fun P hP => ?_⟩
  · rcases (two_primes _ E h2 v.asIdeal _ _ (hne P P' h h' hn)).1 ⟨_, hm R hR⟩ with e | e
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val e))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val e))
  obtain ⟨Q, Q', hn, h, h'⟩ := hv
  have hef := (two_primes _ E h2 v.asIdeal _ _ (hne Q Q' h h' hn)).2 ⟨_, hm P hP⟩
  have hlo : P.asIdeal.LiesOver v.asIdeal := ⟨hP.symm⟩
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have he : v.asIdeal.ramificationIdx' P.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    exact Nat.eq_one_of_mul_eq_one_right hef
  have hf : v.asIdeal.inertiaDeg' P.asIdeal = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  refine ⟨?_, fun a k => ?_, fun b => ?_⟩
  · rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal v.asIdeal v.isPrime v.ne_bot, hf, pow_one]
  · rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot] at he
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.intValuation_le_pow_iff_mem,
      ← HeightOneSpectrum.intValuation_liesOver v P a, he, pow_one]
  · rw [Ideal.inertiaDeg'_algebraMap] at hf
    let _ := Ideal.Quotient.field v.asIdeal
    obtain ⟨c, hc⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hf).2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨a, Ideal.Quotient.eq.1 hc.symm⟩

end GlobalTheory.CMVal.Euler.SplitPlace
