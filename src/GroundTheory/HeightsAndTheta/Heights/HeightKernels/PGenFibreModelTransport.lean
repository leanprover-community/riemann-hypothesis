module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualStdModelField
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.QuotientLiftInjective
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial GenericFibreModelTransport

theorem GenFibreModelTransport.proof : GenFibreModelTransport.Statement := by
  intro K _ ι _ K' _ ι' _ v P' G Ω _ z hz Φ₀ _ _ hΦ₀ τ w q
  let φ : MRing ι' →+* G.Φ' := (aeval G.x').toRingHom
  let ψ : MRing ι' →+* Ω := eval₂Hom (Int.castRingHom Ω) z
  have : P'.IsPrime := hz ▸ RingHom.ker_isPrime ψ
  have hφ : ∀ a ∈ P', φ a = 0 := fun a ha => RingHom.mem_ker.1 (G.genericFibre_ker_target.symm ▸ ha)
  have hψ : ∀ a ∈ P', ψ a = 0 := fun a ha => RingHom.mem_ker.1 (hz.symm ▸ ha)
  let α : FractionRing (MRing ι' ⧸ P') →+* G.Φ' :=
    IsFractionRing.lift (quotient_lift_injective φ P' G.genericFibre_ker_target hφ)
  let β : FractionRing (MRing ι' ⧸ P') →+* Ω := IsFractionRing.lift (quotient_lift_injective ψ P' hz hψ)
  let ξ : (Σ k', ι' k') → FractionRing (MRing ι' ⧸ P') := fun p =>
    algebraMap _ _ (Ideal.Quotient.mk P' (X p))
  have hα : α ∘ ξ = G.x' := funext fun p => by simp [α, ξ, φ]
  have hβ : β ∘ ξ = z := funext fun p => by simp [β, ξ, ψ]
  let k := Subfield.closure (Set.range (ξ ∘ v))
  have h₁ : (algebraMap G.Φ G.Φ').fieldRange = k.map α := by
    rw [RingHom.map_field_closure, ← Set.range_comp, ← Function.comp_assoc, hα]
    refine le_antisymm ?_ (Subfield.closure_le.2 ?_)
    · rintro _ ⟨c, rfl⟩
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have key : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ Subfield.closure (Set.range (G.x' ∘ v)) := by
        intro f
        rw [aeval_def, eval₂_comp_left]
        convert eval₂_mem_closure _ (G.x' ∘ v) f using 2
        exact funext fun p => (G.compat p).symm
      rw [map_div₀]
      exact div_mem (key f) (key g)
    · rintro _ ⟨p, rfl⟩
      exact ⟨G.x p, (G.compat p).symm⟩
  have h₂ : (algebraMap Φ₀ Ω).fieldRange = k.map β := by
    rw [hΦ₀, RingHom.map_field_closure, ← Set.range_comp, ← Function.comp_assoc, hβ]
  obtain ⟨e₁, he₁⟩ := subfield_equiv k α (algebraMap G.Φ G.Φ') h₁
  obtain ⟨e₂, he₂⟩ := subfield_equiv k β (algebraMap Φ₀ Ω) h₂
  let s : Set (FractionRing (MRing ι' ⧸ P')) := Set.range fun t => ξ (w t) / ξ q
  have hs : ∀ (F : Type) [Field F] (γ : FractionRing (MRing ι' ⧸ P') →+* F) (y : (Σ k', ι' k') → F),
      γ ∘ ξ = y → γ '' s = Set.range fun t => y (w t) / y q := by
    rintro F _ γ y rfl
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun t => map_div₀ γ _ _)
  obtain ⟨f₁, t₁⟩ := adjoin_transport e₁ α (RingHom.ext he₁) s (ξ q)
  obtain ⟨f₂, t₂⟩ := adjoin_transport e₂ β (RingHom.ext he₂) s (ξ q)
  rw [hs _ α _ hα] at f₁ t₁
  rw [show α (ξ q) = G.x' q from congrFun hα q] at t₁
  rw [hs _ β _ hβ] at f₂ t₂
  rw [show β (ξ q) = z q from congrFun hβ q] at t₂
  refine ⟨?_, f₁.symm.trans f₂, t₁.symm.trans t₂⟩
  rw [← congrFun hα q, ← congrFun hβ q]
  exact (map_eq_zero α).trans (map_eq_zero β).symm

end GroundTheory.Heights₂.Heights
