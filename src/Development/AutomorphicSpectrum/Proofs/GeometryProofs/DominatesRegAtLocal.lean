import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem dominates_localRings : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) :=
  PositivityTheory.HtPt.Mb.dom_local

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominates_regAt_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.dominates_localRings
