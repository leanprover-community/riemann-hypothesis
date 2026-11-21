import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PartIOfSemistableReductionOfArcFam
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFamilyPointWithFramesOfLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRingStatement
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimQuotientLeOne
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulMemAdjoinOfMemPowRange
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPointDeterminesPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_triples_complete_DVR_torsion : GlobalTheory.LN.UDvrSt := by
  first | exact @GlobalTheory.LN.uDvrSt_holds | exact GlobalTheory.LN.uDvrSt_holds | (intros; apply GlobalTheory.LN.uDvrSt_holds <;> assumption)
end

section
namespace GlobalTheory

theorem _root_.GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion :
    _root_.GlobalTheory.ThetaPtDeterminesSt ∧ _root_.GlobalTheory.EndDeterminedOnTorsionSt := by
  have hL := _root_.GlobalTheory.allSixLaws
  refine ⟨_root_.GlobalTheory.thetaPt_determines hL.1,
    _root_.GlobalTheory.endDeterminedOnTorsion hL.1 ?_⟩
  exact _root_.GlobalTheory.card_zeros_on_torsion_coset_le hL.1.mulN
    (fun K _ X _ p L hL => _root_.GlobalTheory.SectionRing.exists_sectionRing K X p L hL)
    (_root_.GlobalTheory.PowSec.exists_basis_sections hL.1.globalSectionsRank)
    (_root_.GlobalTheory.veryAmple_lbPow hL.1.ample)
    (_root_.GlobalTheory.exists_mulPull_sec hL.1.mulPull)
    (fun K _ X p g hp U hU hne => _root_.GlobalTheory.SmoothDim.ringKrullDim_affineOpen K X p g hp U hU hne)
    _root_.GlobalTheory.polAV_isIntegral_of_isAlgClosed
    (fun K T _ _ _ _ 𝒜 _ m x hx hne d s hs hpow => _root_.GlobalTheory.isIntegral_adjoin_of_mul_pow_mem K T 𝒜 m x hx hne d s hs hpow)
    _root_.GlobalTheory.graded_bezout_bound

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion : GlobalTheory.ThetaPtDeterminesSt ∧ GlobalTheory.EndDeterminedOnTorsionSt := by
  first | exact @GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion | exact GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion | (intros; apply GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem arcFam_closed : GlobalTheory.LN.ArcFamSt :=
  GlobalTheory.T.exists_arc_family_point_with_frames_of_laws GlobalTheory.lawsAndExpansions GlobalTheory.allSixLaws.2.2.2.2.2 GlobalTheory.T.uniformisation_triples_complete_DVR_torsion GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing
    GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion.1 GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion.2 GlobalTheory.thetaUnifAV_closed

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsArcFamilyPointWithFrames_proof : GlobalTheory.LN.ArcFamSt := by
  first | exact @GlobalTheory.arcFam_closed | exact GlobalTheory.arcFam_closed | (intros; apply GlobalTheory.arcFam_closed <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.partI_of_semistableReduction :
    _root_.GlobalTheory.Published.SemistableReductionSt → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PartI := fun h =>
  _root_.GlobalTheory.partI_of_semistableReduction_of_arcFam h _root_.GlobalTheory.arcFam_closed

end GlobalTheory
end
