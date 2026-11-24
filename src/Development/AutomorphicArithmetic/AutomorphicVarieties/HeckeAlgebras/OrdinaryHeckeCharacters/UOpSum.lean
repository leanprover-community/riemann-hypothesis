module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.uOpSum :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a : G), a ∈ I.P → (∃ s : Finset G, (∀ u ∈ s, u ∈ I.N) ∧ ∀ x ∈ I.N, ∃! u, u ∈ s ∧ u⁻¹ * x ∈ I.Nconj a) ∧ ∀ s : Finset G, (∀ u ∈ s, u ∈ I.N) → (∀ x ∈ I.N, ∃! u, u ∈ s ∧ u⁻¹ * x ∈ I.Nconj a) → s.card = (I.Nconj a).relIndex I.N ∧ ∀ v ∈ fixd π I.N, I.uOp π a v = ∑ u ∈ s, π (u * a) v := by
  intro G _ I A M _ _ _ π a ha
  classical
  have hfin : Finite (I.N ⧸ (I.Nconj a).subgroupOf I.N) :=
    Nat.finite_of_card_ne_zero (I.fin_N a ha)
  letI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _
  have key : ∀ x y : I.N, (QuotientGroup.mk x : I.N ⧸ (I.Nconj a).subgroupOf I.N) = QuotientGroup.mk y ↔
      (x : G)⁻¹ * y ∈ I.Nconj a := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  refine ⟨⟨Finset.univ.image (fun q : I.N ⧸ (I.Nconj a).subgroupOf I.N => ((q.out : I.N) : G)), ?_, ?_⟩, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact q.out.2
  · intro x hx
    refine ⟨((QuotientGroup.mk (⟨x, hx⟩ : I.N) : I.N ⧸ (I.Nconj a).subgroupOf I.N).out : I.N),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (key _ ⟨x, hx⟩).1 (QuotientGroup.out_eq' _)
    · rintro u ⟨hu, hux⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have h := (key q.out ⟨x, hx⟩).2 hux
      rw [QuotientGroup.out_eq'] at h
      rw [h]
  · intro s hs hu
    let i : ∀ u ∈ s, I.N ⧸ (I.Nconj a).subgroupOf I.N := fun u h => QuotientGroup.mk ⟨u, hs u h⟩
    have inj : ∀ u₁ (h₁ : u₁ ∈ s) u₂ (h₂ : u₂ ∈ s), i u₁ h₁ = i u₂ h₂ → u₁ = u₂ := by
      intro u₁ h₁ u₂ h₂ h
      have h' := (key ⟨u₁, hs _ h₁⟩ ⟨u₂, hs _ h₂⟩).1 h
      exact (hu u₂ (hs _ h₂)).unique ⟨h₁, h'⟩ ⟨h₂, by simp⟩
    have surj : ∀ q ∈ (Finset.univ : Finset (I.N ⧸ (I.Nconj a).subgroupOf I.N)), ∃ u h, i u h = q := by
      intro q _
      obtain ⟨u, ⟨h, h'⟩, -⟩ := hu q.out q.out.2
      exact ⟨u, h, ((key ⟨u, hs u h⟩ q.out).2 h').trans (QuotientGroup.out_eq' q)⟩
    refine ⟨?_, ?_⟩
    · rw [Finset.card_bij i (fun _ _ => Finset.mem_univ _) inj surj, Subgroup.relIndex, Subgroup.index,
        Nat.card_eq_fintype_card, Finset.card_univ]
    · intro v hv
      rw [Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
      refine (Finset.sum_bij i (fun _ _ => Finset.mem_univ _) inj surj ?_).symm
      intro u h
      have h' := (key ⟨u, hs u h⟩ (i u h).out).1 (QuotientGroup.out_eq' _).symm
      obtain ⟨n, hn, e⟩ := Subgroup.mem_map.1 h'
      have e' : (((i u h).out : I.N) : G) * a = u * a * n := by
        have e2 : a * n * a⁻¹ = u⁻¹ * (((i u h).out : I.N) : G) := e
        calc (((i u h).out : I.N) : G) * a = u * (u⁻¹ * (((i u h).out : I.N) : G)) * a := by group
          _ = u * a * n := by rw [← e2]; group
      rw [e', map_mul π (u * a) n, Module.End.mul_apply, hv n hn]
