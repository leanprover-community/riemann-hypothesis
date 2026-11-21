import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosetsStatement
import BuildAid.ForwardExisting

section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

theorem normaliseGroupClause_holds : NormaliseGroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ ν _ μ hμ
  exact GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ hμ

end GlobalTheory
end

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_haar_group_quotient_integral_formula : NormaliseGroupClause := by
  atlas_forward_decl GlobalTheory.normaliseGroupClause_holds
