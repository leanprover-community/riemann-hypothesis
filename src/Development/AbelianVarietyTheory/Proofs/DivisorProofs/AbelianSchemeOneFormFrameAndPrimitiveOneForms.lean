import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantOneFormFrameAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormsPrimitiveAbelianScheme

section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem hasFrame_and_primF_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasFrame (OAff A.hom) ∧ PrimF A := by
  intro R _ A _ g hA hg
  obtain ⟨M, _, _, j, hfin, hproj, hb⟩ := GlobalTheory.T.exists_invariant_oneForm_frame_abelianScheme R A g hA hg
  exact ⟨hasFrame_of_isBaseChange R (AffOp A.left) (OAff A.hom) M j fun U ↦ ⟨_, fun _ ↦ rfl, hb U⟩,
    GlobalTheory.T.globalOneForms_primitive_abelianScheme R A g hA hg⟩

end GlobalTheory.AbCoh
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_oneFormFrame_and_primitiveOneForms : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.PrimF A := by
  atlas_forward_decl GlobalTheory.AbCoh.hasFrame_and_primF_of_isAbelianScheme
