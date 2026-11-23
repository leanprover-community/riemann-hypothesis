module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Imports
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : (∀ k, ι k) → AddSubgroup V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), QuotExact O x A A' E.lat E'.lat C.lat C'.lat → ∃ E'' : ChartBundle O (mseg x) N V, LatLE O x E' E'' ∧ LatLE O x E'' E ∧ QuotEquiv O x A A' E''.lat E'.lat ∧ QuotEquiv O x E.lat E''.lat C.lat C'.lat := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hQ
  obtain ⟨Γ, Δ, hΓ, hΔ, hX⟩ := hQ
  have bundleOfFamily : ∀ (N : ℕ) (W : Type) [AddCommGroup W] [Module Ω W],
      (∀ Γ : (∀ k, ι k) → AddSubgroup W, IsLatFamily O x Γ →
        (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) →
        ∃ E : ChartBundle O (mseg x) N W, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧
      ∀ E : ChartBundle O (mseg x) N W, IsLatFamily O x E.lat ∧
        ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) := by
    classical
    intro N W _ _
    refine ⟨fun Γ hfam hloc => ?_, fun E => ⟨⟨fun s _ => E.stable s, fun s t hs ht => E.overlap s t hs ht⟩, fun s hs => ⟨E.stable s, E.frame s hs⟩⟩⟩
    refine ⟨{ lat := fun s => if mseg x s = 0 then ⊥ else Γ s
              stable := ?_
              frame := ?_
              overlap := ?_ }, ?_⟩
    · intro s a ha e he
      by_cases h : mseg x s = 0
      · simp only [h, if_true, AddSubgroup.mem_bot] at he ⊢
        rw [he, smul_zero]
      · simp only [h, if_false] at he ⊢
        exact hfam.1 s h a ha e he
    · intro s hs
      simp only [hs, if_false]
      exact (hloc s hs).2
    · intro s t hs ht e he
      simp only [hs, ht, if_false] at he ⊢
      exact hfam.2 s t hs ht e he
    · intro s hs
      simp only [hs, if_false]
  obtain ⟨F, hF⟩ : ∃ F : (∀ k, ι k) → AddSubgroup V,
      F = fun s => (Δ s).comap (AddMonoidHom.inl V V₂) := ⟨_, rfl⟩
  have memF : ∀ s b, b ∈ F s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s b
    subst hF
    exact Iff.rfl
  have hFlat : IsLatFamily O x F := by
    refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
    · have h := hΔ.1.1 s hs a ha (v, 0) ((memF s v).1 hv)
      rw [memF]
      simpa using h
    · obtain ⟨m, hm⟩ := hΔ.1.2 s t hs ht (v, 0) ((memF s v).1 hv)
      refine ⟨m, ?_⟩
      rw [memF]
      simpa using hm
  have hFfree : ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (F s) := by
    intro s hs
    have hE := ((bundleOfFamily N V).2 E).2 s hs
    have hC := ((bundleOfFamily N₂ V₂).2 C).2 s hs
    have hC' := ((bundleOfFamily N₂ V₂).2 C').2 s hs
    have h := (GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main (chartRing O (mseg x) s) N N₂ (E.lat s) (C.lat s)
      (C'.lat s) (Δ s) hE hC hC' (fun a ha v hv => hΔ.1.1 s hs a ha v hv)
      (fun v w h => (hΔ.2 s hs).1 v w h) (fun v hv => (hΔ.2 s hs).2.1 v hv)
      (fun w => (hΔ.2 s hs).2.2.1 w) (fun w hw => (hX s hs).2.1 w hw)).2
    rw [hF]
    exact h
  obtain ⟨E'', hE''⟩ := (bundleOfFamily N V).1 F hFlat hFfree
  have memE'' : ∀ s, mseg x s ≠ 0 → ∀ b, b ∈ E''.lat s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s hs b
    rw [hE'' s hs, memF]
  refine ⟨E'', fun s hs b hb => ?_, fun s hs b hb => ?_,
    ⟨Γ, ⟨hΓ.1, fun s hs => ⟨fun v w h => ⟨((hΓ.2 s hs).1 v w h).1,
        (memE'' s hs w).2 (((hX s hs).2.2 w).2 ⟨v, h⟩)⟩,
      (hΓ.2 s hs).2.1, (hΓ.2 s hs).2.2.1, (hΓ.2 s hs).2.2.2⟩⟩,
      fun s hs => ⟨(hX s hs).1, fun w hw => ((hX s hs).2.2 w).1 ((memE'' s hs w).1 hw)⟩⟩,
    ⟨Δ, ⟨hΔ.1, fun s hs => ⟨(hΔ.2 s hs).1, (hΔ.2 s hs).2.1, (hΔ.2 s hs).2.2.1,
        fun v hv => (memE'' s hs v).1 hv⟩⟩,
      fun s hs => ⟨fun v hv => (memE'' s hs v).2 hv, (hX s hs).2.1⟩⟩⟩
  · exact (memE'' s hs b).2 ((hΔ.2 s hs).2.2.2 b hb)
  · exact ((hΔ.2 s hs).1 b 0 ((memE'' s hs b).1 hb)).1

end GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle
