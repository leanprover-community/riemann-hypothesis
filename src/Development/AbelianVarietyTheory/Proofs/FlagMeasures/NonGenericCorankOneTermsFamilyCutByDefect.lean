import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericTermClassesEqRowsInDoubleCoset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericFamilyClassesDetermineRows

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem famNG_holds : FamNG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hC => ?_⟩
  have hT : ConcTie X Y := hC.2.2
  exact ⟨rfl, GlobalTheory.T.nonGeneric_term_classes_eq_rows_in_double_coset D X Y u u' hT, (GlobalTheory.NGClass.ngClass_rows D X Y u u' hT).2.1⟩

end GlobalTheory.SnFam
end
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_generic_corank_one_terms_family_cut_by_defect : GlobalTheory.SnFam.FamNG := by
  atlas_forward_decl GlobalTheory.SnFam.famNG_holds
