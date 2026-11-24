module

public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem mem_closure_singleton_iff_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (a b : PrimeSpectrum Γ(X, U)) :
    a ∈ closure ({b} : Set (PrimeSpectrum Γ(X, U))) ↔
      hU.fromSpec a ∈ closure ({hU.fromSpec b} : Set (X : Type u)) := by
  have hoi : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hind := (Scheme.Hom.isOpenEmbedding hU.fromSpec).toIsEmbedding.toIsInducing
  constructor
  · intro hab
    have h1 : b ⤳ a := specializes_iff_mem_closure.mpr hab
    exact specializes_iff_mem_closure.mp (hind.specializes_iff.mpr h1)
  · intro hab
    have h1 : hU.fromSpec b ⤳ hU.fromSpec a := specializes_iff_mem_closure.mpr hab
    exact specializes_iff_mem_closure.mp (hind.specializes_iff.mp h1)

private theorem mem_primeIdealOf_of_notMem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : (X : Type u)} (hx : x ∈ U) {f : Γ(X, U)}
    (hb : x ∉ X.basicOpen f) : f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  by_contra hfn
  apply hb
  have h1 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
    rw [hU.fromSpec_preimage_basicOpen f]
    exact (PrimeSpectrum.mem_basicOpen f _).mpr hfn
  have h2 : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h1
  rw [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h2
  exact h2

private theorem mem_primeIdealOf_of_mem_support {X : Scheme.{u}} {I : X.IdealSheafData}
    {U : X.affineOpens} {x : (X : Type u)} (hx : x ∈ U.1) {f : Γ(X, U.1)}
    (hf : f ∈ I.ideal U) (hxs : x ∈ I.support) :
    f ∈ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hz : x ∈ X.zeroLocus (I.ideal U : Set Γ(X, U.1)) :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem hx).mp hxs
  rw [Scheme.mem_zeroLocus_iff] at hz
  exact mem_primeIdealOf_of_notMem_basicOpen U.2 hx (hz f hf)

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.not_irreducibleComponent_subset_support
    {X : Scheme.{u}} {D : X.IdealSheafData} (hD : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor D)
    {Z : Set (X : Type u)} (hZ : Z ∈ irreducibleComponents (X : Type u)) :
    ¬ Z ⊆ (D.support : Set (X : Type u)) := by
  intro hsub
  have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 hZcl
  have hξ' : closure ({ξ} : Set (X : Type u)) = Z := hξ
  have hξZ : ξ ∈ Z := by rw [← hξ']; exact subset_closure rfl
  obtain ⟨U, f, hxU, hf, hDU⟩ := hD ξ
  have hfD : f ∈ D.ideal U := by rw [hDU]; exact Ideal.subset_span rfl
  have hfp : f ∈ (U.2.primeIdealOf ⟨ξ, hxU⟩).asIdeal :=
    EmbeddedResolution.mem_primeIdealOf_of_mem_support hxU hfD (hsub hξZ)
  have hmin : (U.2.primeIdealOf ⟨ξ, hxU⟩).asIdeal ∈ minimalPrimes Γ(X, U.1) := by
    refine ⟨⟨(U.2.primeIdealOf ⟨ξ, hxU⟩).isPrime, bot_le⟩, ?_⟩
    rintro q ⟨hq, -⟩ hqle
    have hqle' : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ≤ U.2.primeIdealOf ⟨ξ, hxU⟩ := hqle
    have hxy : (U.2.primeIdealOf ⟨ξ, hxU⟩) ∈
        closure ({(⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))} : Set (PrimeSpectrum Γ(X, U.1))) :=
      (PrimeSpectrum.le_iff_mem_closure ⟨q, hq⟩ (U.2.primeIdealOf ⟨ξ, hxU⟩)).mp hqle'
    have hξcl : ξ ∈ closure ({U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}
        : Set (X : Type u)) := by
      have h2 := (_root_.FunctorialResolution.EmbeddedResolution.mem_closure_singleton_iff_fromSpec U.2 (U.2.primeIdealOf ⟨ξ, hxU⟩) ⟨q, hq⟩).mp hxy
      rw [U.2.fromSpec_primeIdealOf ⟨ξ, hxU⟩] at h2
      exact h2
    have hZsub : Z ⊆ closure ({U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}
        : Set (X : Type u)) := by
      rw [← hξ']
      exact closure_minimal (Set.singleton_subset_iff.mpr hξcl) isClosed_closure
    have hyZ : U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈ Z :=
      hZ.2 isIrreducible_singleton.closure hZsub (subset_closure rfl)
    have hy : U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))
        ∈ closure ({ξ} : Set (X : Type u)) := by
      rw [hξ']; exact hyZ
    have hprimeLe : (U.2.primeIdealOf ⟨ξ, hxU⟩) ≤ (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) := by
      refine (PrimeSpectrum.le_iff_mem_closure (U.2.primeIdealOf ⟨ξ, hxU⟩) ⟨q, hq⟩).mpr ?_
      refine (_root_.FunctorialResolution.EmbeddedResolution.mem_closure_singleton_iff_fromSpec U.2 ⟨q, hq⟩ (U.2.primeIdealOf ⟨ξ, hxU⟩)).mpr ?_
      rw [U.2.fromSpec_primeIdealOf ⟨ξ, hxU⟩]
      exact hy
    exact hprimeLe
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hfp hmin hf

end FunctorialResolution.EmbeddedResolution
