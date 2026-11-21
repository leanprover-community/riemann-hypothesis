import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsCurveThroughSpecialPoint
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_fibreCurve_through_closed_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ∀ (y x : Cpt ξ) (g : Ω), ¬ unitAt ξ y (algebraMap O Ω ϖ) → y.1 ⤳ x.1 → IsClosed ({x.1} : Set X) → g ∈ regAt ξ x → unitAt ξ y g → ¬ unitAt ξ x g → ∃ (Γ : FibreCurve ξ (algebraMap O Ω ϖ)) (i : Γ.C.I), y.1 ⤳ centre Γ.η ∧ unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ g ∧ centre (Γ.z i) = x.1 := by
  exact @PositivityTheory.Xgn.exists_curve_through_special_point

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_fibre_closed_specialization : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ∀ (y x : Cpt ξ) (g : Ω), ¬ unitAt ξ y (algebraMap O Ω ϖ) → y.1 ⤳ x.1 → IsClosed ({x.1} : Set X) → g ∈ regAt ξ x → unitAt ξ y g → ¬ unitAt ξ x g → ∃ (Γ : FibreCurve ξ (algebraMap O Ω ϖ)) (i : Γ.C.I), y.1 ⤳ centre Γ.η ∧ unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ g ∧ centre (Γ.z i) = x.1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.exists_fibreCurve_through_closed_point
