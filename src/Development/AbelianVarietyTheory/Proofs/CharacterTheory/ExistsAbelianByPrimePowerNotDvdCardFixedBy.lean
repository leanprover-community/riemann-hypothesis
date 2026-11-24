module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByPowPrimePowModEqStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByQuotientEqRelIndexOfPRegularStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCoprimeOrderOfPowPrimePowStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsSylowOverSubgroupStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_abelianByPrimePower_not_dvd_card_fixedBy₂ :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime →
      ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by
  intro G _ _ x p hp
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_coprime_orderOf_pow_prime_pow' G x p hp
  obtain ⟨H, hCH, hnorm, hpow, hidx⟩ := GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex G (Subgroup.zpowers (x ^ p ^ k)) p hp
  have hN : ∀ g : G, g ∈ Subgroup.normalizer ((Subgroup.zpowers (x ^ p ^ k) : Subgroup G) : Set G) ↔
      ∀ d ∈ Subgroup.zpowers (x ^ p ^ k), g * d * g⁻¹ ∈ Subgroup.zpowers (x ^ p ^ k) := by
    intro g
    constructor
    · intro hg d hd
      exact (Subgroup.mem_normalizer_iff.1 hg d).1 hd
    · intro h
      exact Subgroup.mem_normalizer_fintype h
  refine ⟨H, ⟨p, hp, (Subgroup.zpowers (x ^ p ^ k)).subgroupOf H, ⟨?_⟩, ?_, ?_⟩, ?_⟩
  · intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn
  · intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hm, ← hn]
    exact (Commute.refl _).zpow_zpow m n
  · intro g
    obtain ⟨j, hj⟩ := hpow g g.2
    exact ⟨j, by rw [Subgroup.mem_subgroupOf]; simpa using hj⟩
  · intro hd
    haveI : Finite (G ⧸ H) := inferInstance
    have h1 := GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime G (x ^ p ^ k) p H _ hk hCH hpow hN
    have h2 := GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy G (G ⧸ H) x p k hp
    apply hidx _ hN
    rw [← h1]
    exact (h2.dvd_iff dvd_rfl).2 hd

end GlobalTheory.BI
