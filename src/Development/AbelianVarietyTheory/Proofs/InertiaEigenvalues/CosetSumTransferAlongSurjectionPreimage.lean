module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem cosetSum_transfer_surj {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (U0 : Subgroup G) (K : Subgroup H) (T : Subgroup G) (ψ : T →* H)
    (hψ : Function.Surjective ψ) (hTU : ∀ t : T, ψ t ∈ K ↔ (t : G) ∈ U0)
    (a φ' : H → ℂ) (β : G → V) (lam : V →ₗ[ℂ] ℂ)
    (ha : ∀ x, ∀ k ∈ K, a (x * k) = a x)
    (hfin : (Function.support fun d : H ⧸ K => a d.out).Finite)
    (hβ : ∀ x, ∀ u ∈ U0, β (x * u) = β x)
    (hφ : ∀ t : T, φ' (ψ t) = lam (β t)) :
    ∑ᶠ d : H ⧸ K, a d.out * φ' d.out = lam (∑ᶠ c : G ⧸ U0,
      if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then
        a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0) := by
  classical
  set F : G ⧸ U0 → V := fun c => if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then
        a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0 with hF
  let t : H ⧸ K → T := fun d => (hψ d.out).choose
  have ht : ∀ d, ψ (t d) = d.out := fun d => (hψ d.out).choose_spec
  let f : H ⧸ K → G ⧸ U0 := fun d => ((t d : G) : G ⧸ U0)

  have key : ∀ x y : T, ((x : G) : G ⧸ U0) = ((y : G) : G ⧸ U0) →
      ((x : G)⁻¹ * y ∈ U0) ∧ ∃ k ∈ K, ψ y = ψ x * k := by
    intro x y hxy
    rw [QuotientGroup.eq] at hxy
    refine ⟨hxy, ψ (x⁻¹ * y), (hTU _).2 (by simpa using hxy), ?_⟩
    simp [map_mul, map_inv]

  have hinj : Function.Injective f := by
    intro d d' h
    obtain ⟨-, k, hk, hkk⟩ := key _ _ h
    rw [ht, ht] at hkk
    rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d', QuotientGroup.eq, hkk]
    simpa using hk

  have hcover : ∀ x : T, f ((ψ x : H) : H ⧸ K) = ((x : G) : G ⧸ U0) ∧
      a (((ψ x : H) : H ⧸ K).out) = a (ψ x) := by
    intro x
    set d : H ⧸ K := ((ψ x : H) : H ⧸ K) with hd
    have h1 : d.out⁻¹ * ψ x ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    refine ⟨?_, ?_⟩
    · show (((t d : T) : G) : G ⧸ U0) = ((x : G) : G ⧸ U0)
      rw [QuotientGroup.eq]
      have : ψ ((t d)⁻¹ * x) ∈ K := by simpa [map_mul, map_inv, ht] using h1
      simpa using (hTU _).1 this
    · have := ha d.out _ h1
      simpa using this.symm

  have hval : ∀ d, F (f d) = a d.out • β (t d) := by
    intro d
    have hc : ∃ x : G, (x : G ⧸ U0) = f d ∧ x ∈ T := ⟨t d, rfl, (t d).2⟩
    simp only [hF, dif_pos hc]
    obtain ⟨hU, k, hk, hkk⟩ := key (t d) ⟨hc.choose, hc.choose_spec.2⟩ hc.choose_spec.1.symm
    rw [hkk, ha _ k hk, ht]
    congr 1
    have := hβ (t d : G) _ hU
    simpa using this

  set S : Finset (H ⧸ K) := hfin.toFinset with hS
  have hsupp : Function.support F ⊆ ↑(S.image f) := by
    intro c hc
    rw [Function.mem_support] at hc
    have hc' : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T := by
      by_contra hn
      exact hc (by simp only [hF, dif_neg hn])
    obtain ⟨x, rfl, hx⟩ := hc'
    obtain ⟨h1, h2⟩ := hcover ⟨x, hx⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, ?_, h1⟩)
    rw [hS, Set.Finite.mem_toFinset, Function.mem_support, h2]
    intro h0
    apply hc
    have hF' := hval ((ψ ⟨x, hx⟩ : H) : H ⧸ K)
    rw [h1, h2, h0, zero_smul] at hF'
    exact hF'
  have hL : Function.support (fun d : H ⧸ K => a d.out * φ' d.out) ⊆ ↑S := by
    intro d hd
    rw [hS, Set.Finite.coe_toFinset]
    exact fun h0 => hd (by simp only [h0, zero_mul])

  rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hsupp,
  Finset.sum_image (fun d _ d' _ h => hinj h), map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hval, map_smul, smul_eq_mul, ← hφ, ht]

end GlobalTheory
