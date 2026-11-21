import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegMin

theorem exists_semiAbelian_idempotent_image : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (H : Over S) (_ : GrpObj H) (i : H ⟶ G) (r : G ⟶ H), IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 H ∧ r ≫ i = e ∧ IsSemiAbelian H := by
  intro S G _ _ hG e he hee
  obtain ⟨H, hgrp, _, i, r, hH, hi, hr, hir, hri⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image S G hG e he hee
  exact ⟨H, hgrp, i, r, hi, hr, hir, hri, hH⟩

end GlobalTheory.SiegMin
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_direct_factor_of_idempotent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (H : Over S) (_ : GrpObj H) (i : H ⟶ G) (r : G ⟶ H), IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 H ∧ r ≫ i = e ∧ IsSemiAbelian H := by
  atlas_forward_decl GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image
