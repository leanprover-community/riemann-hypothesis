import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections
import BuildAid.ForwardExisting

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subobject_pullback_sections : ∀ {X : Scheme.{0}} {E : X.Modules} (D S : Subobject E) (V : X.Opens), secs ((Subobject.pullback D.arrow).obj S) V = (D.arrow.app V) ⁻¹' secs S V := by
  first | exact @GlobalTheory.CompanionTheory.GE.secs_pullback_arrow | exact GlobalTheory.CompanionTheory.GE.secs_pullback_arrow | (intros; apply GlobalTheory.CompanionTheory.GE.secs_pullback_arrow <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem killed_restrictSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules} (J : X.IdealSheafData)
    (D : Subobject E) (S : ℕ → Subobject E) (c : ℕ)
    (h : ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U →
      ∀ x ∈ secs D U, a • x ∈ secs (S n) U) (e : ℕ) :
    Killed J (restrictSys I D S c e) := by
  intro U a ha x
  have hle : (Subobject.pullback D.arrow).obj (S (e + c)) ≤ GlobalTheory.CompanionTheory.GE.restrictSys I D S c e := by
    unfold GlobalTheory.CompanionTheory.GE.restrictSys
    exact le_sup_left
  have hmem : a • x ∈ GlobalTheory.CompanionTheory.GE.secs ((Subobject.pullback D.arrow).obj (S (e + c))) U := by
    rw [GlobalTheory.T.subobject_pullback_sections, Set.mem_preimage, Scheme.Modules.Hom.app_smul]
    exact h (e + c) U a ha _ (by unfold GlobalTheory.CompanionTheory.GE.secs; exact Set.mem_range_self x)
  unfold GlobalTheory.CompanionTheory.GE.secs at hmem ⊢
  obtain ⟨y, hy⟩ := hmem
  refine ⟨ConcreteCategory.hom (Scheme.Modules.Hom.app (Subobject.ofLE _ _ hle) U) y, ?_⟩
  rw [← hy, ← Subobject.ofLE_arrow hle, Scheme.Modules.Hom.comp_app] <;> rfl

end GlobalTheory.CompanionTheory.GE
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_system_killed_by_ideal : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules} (J : X.IdealSheafData) (D : Subobject E) (S : ℕ → Subobject E) (c : ℕ), (∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U) → ∀ e, Killed J (restrictSys I D S c e) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.killed_restrictSys
end
