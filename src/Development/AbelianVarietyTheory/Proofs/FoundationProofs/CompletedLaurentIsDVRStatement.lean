module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletedLaurentQuotPrimeEquivLaurentFp
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.LocalRing
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.K5

namespace GlobalTheory.K5

theorem dvr_of_separated {S : Type*} [CommRing S] (π : S) (hn : ∀ n : ℕ, π ^ n ≠ 0)
    (hnu : ¬ IsUnit π) (hu : ∀ x, ¬ π ∣ x → IsUnit x) (hsep : ∀ x, (∀ n : ℕ, π ^ n ∣ x) → x = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  classical
  have hfac : ∀ x : S, x ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra h
      push Not at h
      exact hx (hsep x fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (h n))
    have h1 : π ^ (Nat.find hex) ∣ x := by
      rcases h : Nat.find hex with _ | m
      · simp
      · have := Nat.find_min hex (m := m) (by omega)
        simpa using this
    obtain ⟨u, hxu⟩ := h1
    refine ⟨Nat.find hex, u, hu u ?_, hxu⟩
    rintro ⟨v, hv⟩
    exact Nat.find_spec hex ⟨v, by rw [pow_succ, mul_assoc, ← hv]; exact hxu⟩
  have : Nontrivial S := ⟨⟨π ^ 0, 0, hn 0⟩⟩
  have : NoZeroDivisors S := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨a, u, hu', rfl⟩ := hfac x h.1
    obtain ⟨b, v, hv', rfl⟩ := hfac y h.2
    apply hn (a + b)
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy]; ring
    exact ((hu'.mul hv').mul_left_eq_zero).1 this⟩
  have hd : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := by simpa using hn 1
  have hprime : Prime π := by
    refine ⟨hπ0, hnu, fun a b hab => ?_⟩
    by_contra h
    push Not at h
    exact hnu (isUnit_of_dvd_unit hab ((hu a h.1).mul (hu b h.2)))
  refine ⟨hd, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, hprime.irreducible, fun {x} hx => ?_⟩, hprime.irreducible⟩
  obtain ⟨n, u, hu', rfl⟩ := hfac x hx
  exact ⟨n, hu'.unit, rfl⟩

theorem adicCompletion_dvr {R : Type*} [CommRing R] [IsDomain R] (a : R) (ha : a ≠ 0)
    (hmax : (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a}).IsMaximal) :
    ∃ _ : IsDomain (AdicCompletion (Ideal.span {a}) R),
      IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R) ∧
        Irreducible (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := by
  have fg : (Ideal.span {a}).FG := Submodule.fg_span_singleton _
  have hc := AdicCompletion.isAdicComplete_self (Ideal.span {a}) fg
  rw [Ideal.map_span, Set.image_singleton] at hc
  have hnu : ¬ IsUnit (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := fun h =>
    hmax.ne_top (Ideal.span_singleton_eq_top.2 h)
  have := isLocalRing_of_isAdicComplete_maximal
    (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a})
  refine dvr_of_separated _ (fun n hn => ?_) hnu (fun x hx => ?_) (fun x hx => ?_)
  · rw [← map_pow] at hn
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (n + 1)) hn
    rw [AlgHom.commutes, map_zero, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ] at h2
    have h3 : a ^ n * a ∣ a ^ n * 1 := by simpa using h2
    exact hnu ((isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero n ha)).1 h3)).map _)
  · by_contra hxu
    have : x ∈ IsLocalRing.maximalIdeal _ := hxu
    rw [← IsLocalRing.eq_maximalIdeal hmax, Ideal.mem_span_singleton] at this
    exact hx this
  · refine hc.toIsHausdorff.haus' x fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx n

theorem completed_laurent_isDVR (p : ℕ) [Fact p.Prime] :
    ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  have hp : (p : Lau p) ≠ 0 := by
    have h : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [← map_natCast (HahnSeries.C : ℤ_[p] →+* Lau p)]
    exact HahnSeries.C_ne_zero h
  obtain ⟨e⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))
  have := adicCompletion_dvr (p : Lau p) hp (by rw [map_natCast]; exact hmax)
  rw [map_natCast] at this
  exact this

end GlobalTheory.K5
