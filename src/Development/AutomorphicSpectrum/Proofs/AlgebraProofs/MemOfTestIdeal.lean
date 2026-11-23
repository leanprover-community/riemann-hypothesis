module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeTestPointMembershipStatement
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

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaTest

theorem mem_of_test_ideal : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ (L : AddSubgroup Ω), LocFree R 1 L → ∀ v : Ω, (∃ m : ℕ, (p : Ω) ^ m * v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → algebraMap Ω C v ∈ spanOver RC (algebraMap Ω C '' L)) → v ∈ L := by
  intro o Ω _ _ _ R p hp hp0 hN hF hI L hL v hm htest
  let e : Ω ≃ₗ[Ω] (Unit → Ω) := (LinearEquiv.funUnique Unit Ω Ω).symm
  have hL' : LocFree R 1 (L.map e.toLinearMap.toAddMonoidHom) :=
    LatticeGoodness.locFree_map_equiv R e hL
  have hmem : ∀ x : Ω, e x ∈ L.map e.toLinearMap.toAddMonoidHom ↔ x ∈ L := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine (hmem v).1 (GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI 1 _ hL' (e v) ?_ ?_)
  · obtain ⟨m, hm⟩ := hm
    refine ⟨m, ?_⟩
    have : (p : Ω) ^ m • e v = e ((p : Ω) ^ m * v) := by
      rw [← smul_eq_mul, map_smul]
    rw [this]
    exact (hmem _).2 hm
  · intro C _ _ _ _ RC ht
    let g : C →+ (Unit → C) :=
      (LinearEquiv.funUnique Unit C C).symm.toLinearMap.toAddMonoidHom
    have hg : bcMap Ω C Unit (e v) = g (algebraMap Ω C v) := by
      funext u
      simp [bcMap, e, g]
    rw [hg]
    have h1 := AddSubgroup.mem_map_of_mem g (htest C RC ht)
    unfold spanOver at h1 ⊢
    rw [AddMonoidHom.map_closure] at h1
    refine (AddSubgroup.closure_mono ?_) h1
    rintro _ ⟨_, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, ha, bcMap Ω C Unit (e x), ⟨e x, (hmem x).2 hx, rfl⟩, ?_⟩
    funext u
    simp [bcMap, e, g]

end GlobalTheory.CompanionTheory.Ar.Num.HaTest
