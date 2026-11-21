import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicPropertiesStatement
import BuildAid.ForwardExisting

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_classical_point_lifting_residue_point : ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (U : X.Opens), (U : Set X).Nonempty → ∀ (p : ℕ) [Fact p.Prime], (∀ x : Sp (kb p) ⟶ X, ∃ b : Sp (OO p) ⟶ X, rPt p ≫ b = x ∧ Set.range (gPt p ≫ b) ⊆ U) ∧ (∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X)) := by
  first | exact @GlobalTheory.exists_integral_point_lifting_residue_point | exact GlobalTheory.exists_integral_point_lifting_residue_point | (intros; apply GlobalTheory.exists_integral_point_lifting_residue_point <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.fib_of_indep : ∀ C : Core, C.Indep → C.Fib := by
  intro C hI p _ y τ x hx
  obtain ⟨-, hlft, -, hint, hflat, -, -, -, -, -, -, hdom, htest⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  have := C.lft
  have hne : ((C.GG.hom ⁻¹ᵁ C.U : C.G.toScheme.Opens) : Set C.G.toScheme).Nonempty := by
    obtain ⟨w, hw⟩ := hdom.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨w, hw⟩
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨b', hb'x, hb'U⟩ :=
    (@GlobalTheory.T.exists_classical_point_lifting_residue_point C.G.toScheme hint (C.GG.hom ≫ C.π) hflat hlft' (C.GG.hom ⁻¹ᵁ C.U) hne p _).1 x
  have hcl : C.Cl (b' ≫ C.GG.hom) := by
    rintro _ ⟨s, rfl⟩
    have := hb'U ⟨s, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact this
  obtain ⟨b, hby, hbx⟩ := hI p (b' ≫ C.GG.hom) y hcl (htest p y τ).1
    (by rw [← Category.assoc, hb'x, hx]) b' rfl
  obtain ⟨c, hc, hcb⟩ := τ.lift b hby
  refine ⟨rPt p ≫ c, by rw [Category.assoc, hc], ?_⟩
  rw [Category.assoc, hcb, hbx, hb'x]

end GlobalTheory.ZJ
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep : ∀ C : Core, C.Indep → C.Fib := by
  atlas_forward_decl GlobalTheory.ZJ.Core.fib_of_indep
end
