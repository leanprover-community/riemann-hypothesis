module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericallyRegularQuotientDominatingPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationQuotientComapEquiv
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem generically_regular_quotient_of_finiteType_int :
    ∀ (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧
      ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q →
        IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
  intro B _ _ p hp
  by_cases h : ∀ a : ℤ, algebraMap ℤ B a ∈ p → a = 0
  · exact GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime ℤ B p h
  push_neg at h
  obtain ⟨a, ha, ha0⟩ := h
  have hP : (p.comap (algebraMap ℤ B)) ≠ ⊥ := by
    intro hb
    apply ha0
    have : a ∈ p.comap (algebraMap ℤ B) := ha
    rw [hb] at this
    simpa using this
  obtain ⟨x, hx, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (Ideal.IsPrime.comap _) hP
  set l := x.natAbs with hl
  have hlp : l.Prime := Int.prime_iff_natAbs_prime.mp hxp
  haveI : Fact l.Prime := ⟨hlp⟩
  have hlmem : (l : B) ∈ p := by
    have hx' : algebraMap ℤ B x ∈ p := hx
    rcases Int.natAbs_eq x with h1 | h1
    · rw [h1] at hx'
      simpa [hl] using hx'
    · rw [h1] at hx'
      simpa [hl] using hx'
  set I : Ideal B := Ideal.span {(l : B)} with hI
  let mk := Ideal.Quotient.mk I
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker mk = I := Ideal.mk_ker
  have hIp : I ≤ p := by
    rw [hI, Ideal.span_le]; simpa using hlmem
  have hl0 : ∀ a ∈ Ideal.span {((l : ℕ) : ℤ)}, (Int.castRingHom (B ⧸ I)) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    have : ((l : ℕ) : B ⧸ I) = 0 := by
      have h0 : (Ideal.Quotient.mk I) (l : B) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span rfl)
      simpa using h0
    simp [this]
  let ψ : ZMod l →+* B ⧸ I :=
    (Ideal.Quotient.lift (Ideal.span {((l : ℕ) : ℤ)}) (Int.castRingHom (B ⧸ I)) hl0).comp
      (Int.quotientSpanNatEquivZMod l).symm.toRingHom
  letI : Algebra (ZMod l) (B ⧸ I) := ψ.toAlgebra
  haveI : IsScalarTower ℤ (ZMod l) (B ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.FiniteType (ZMod l) (B ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod l) (B ⧸ I)
  haveI : PerfectField (FractionRing (ZMod l)) := by
    have : Finite (FractionRing (ZMod l)) :=
      Finite.of_equiv _ (FractionRing.algEquiv (ZMod l) (ZMod l)).toEquiv.symm
    infer_instance

  have corr : ∀ (r : Ideal B), r.IsPrime → I ≤ r → (r.map mk).IsPrime ∧ (r.map mk).comap mk = r := by
    intro r hr hIr
    refine ⟨Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hIr), ?_⟩
    rw [Ideal.comap_map_of_surjective' mk hmk, hker]
    exact sup_eq_left.mpr hIr
  obtain ⟨p', hp', rfl⟩ : ∃ p' : Ideal (B ⧸ I), p'.IsPrime ∧ p'.comap mk = p :=
    ⟨p.map mk, corr p hp hIp⟩
  have hdom : ∀ a : ZMod l, algebraMap (ZMod l) (B ⧸ I) a ∈ p' → a = 0 := by
    intro a ha
    by_contra ha0
    exact hp'.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((IsUnit.mk0 a ha0).map _))
  obtain ⟨g', hg'p, hg'⟩ := GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime (ZMod l) (B ⧸ I) p' hdom
  obtain ⟨g, rfl⟩ := hmk g'
  refine ⟨g, fun hg => hg'p hg, ?_⟩
  intro q hq hpq hgq
  have hIq : I ≤ q := hIp.trans hpq
  obtain ⟨q', hq', rfl⟩ : ∃ q' : Ideal (B ⧸ I), q'.IsPrime ∧ q'.comap mk = q :=
    ⟨q.map mk, corr q hq hIq⟩
  have hpq' : p' ≤ q' := by
    intro y hy
    obtain ⟨y, rfl⟩ := hmk y
    exact hpq hy
  have hreg := hg' q' hpq' (fun h => hgq h)
  obtain ⟨e⟩ := GlobalTheory.localization_quotient_comap_equiv B (B ⧸ I) mk hmk p' q'
  exact IsRegularLocalRing.of_ringEquiv e.symm

end GlobalTheory
