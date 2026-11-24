module

public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.PrimeAvoid

theorem exists_basicOpen_between {X : Scheme.{0}} (U V₀ : X.Opens) (hU : IsAffineOpen U)
    (hV : V₀ ≤ U) (K : Set X) (hK : K.Finite) (hKV : K ⊆ V₀) :
    ∃ f : Γ(X, U), K ⊆ X.basicOpen f ∧ X.basicOpen f ≤ V₀ := by
  classical
  let W : Set (PrimeSpectrum Γ(X, U)) := hU.fromSpec ⁻¹' (V₀ : Set X)
  have hWo : IsOpen W := (hU.fromSpec ⁻¹ᵁ V₀).isOpen
  let I : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal Wᶜ
  let s : Set (Ideal Γ(X, U)) := PrimeSpectrum.asIdeal '' (hU.fromSpec ⁻¹' K)
  have hs : s.Finite := (hK.preimage hU.fromSpec.isOpenEmbedding.injective.injOn).image _
  have hnot : ¬ ((I : Set Γ(X, U)) ⊆ ⋃ P ∈ s, (P : Set Γ(X, U))) := by
    intro h
    obtain ⟨P, ⟨p, hpK, rfl⟩, hIp⟩ :=
      (Ideal.subset_union_prime_finite (f := fun P : Ideal Γ(X, U) => P) hs ⊥ ⊥
        (fun P hP _ _ => by obtain ⟨p, -, rfl⟩ := hP; exact p.isPrime)).1 h
    have hpW : p ∈ W := hKV hpK
    have hcl : p ∈ closure Wᶜ := by
      rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact (PrimeSpectrum.mem_zeroLocus _ _).2 hIp
    rw [hWo.isClosed_compl.closure_eq] at hcl
    exact hcl hpW
  obtain ⟨g, hgI, hgs⟩ := Set.not_subset.1 hnot
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact hV (hKV hx)
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen g p).2 fun hg => hgs (Set.mem_biUnion ⟨p, hx, rfl⟩ hg)
    exact hp
  · intro x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact X.basicOpen_le g hx
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := hx
    rw [hU.fromSpec_preimage_basicOpen] at hp
    have hp' := (PrimeSpectrum.mem_basicOpen g p).1 hp
    by_contra hpV
    exact hp' ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hgI p hpV)

end GlobalTheory.CompanionTheory.PrimeAvoid
