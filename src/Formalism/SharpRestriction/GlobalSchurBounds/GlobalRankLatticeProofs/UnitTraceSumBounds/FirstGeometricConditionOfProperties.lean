import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawAlt
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CoefWfZero
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RetcutA
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglPtW

section
namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.GL3r7 Formalism.MainNotions.Ext


end Formalism.MainNotions.Ext.CutA
end

section
namespace Formalism.MainNotions.Ext

theorem addPtW_holds : AddPtW :=
  fun p _ g hOk hF σ a b ha hb =>
    formal_group_add_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 hF σ a b ha hb

theorem mulPtW_holds : MulPtW :=
  fun p _ g hOk c hc σ a ha =>
    formal_group_mul_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 c hc σ a ha





end Formalism.MainNotions.Ext
end

section
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.GL3r7 Formalism.MainNotions.Ext.CutA

theorem firstGeometricCondition_of_properties (D : D7) (hc : cube D) (he : endInt D) (hOK : PhNormOK D) :
    beBiadd D ∧ phNorm D ∧ beConj D ∧ beDiag D ∧ jetsPh D ∧ PhGram D ∧ PhUnitary D ∧ PhIsotropic D ∧ PhDual D ∧ SDiff D ∧
      endIntW D ∧ splitZero D := by
  have ha := addInt_holds D
  have hB := beBiadd_of_cube D hc
  have hn := phNorm_of' phNormOfUnits_holds phNormClosed_holds D hOK he ha hB
  have hb := beConj_of' beConjOfNorm_holds D he ha hn hB
  have hG := phGram_of phGramG_holds D he ha hn hb hB
  exact ⟨hB, hn, hb, beDiag_of' beDiagG_holds D he ha hn hb hB, jetsPh_of' jetsHigh_holds jetsOne_holds jetsTwo_holds D hc hn hb, hG,
    phUnitary_of gramUnitEq_holds D hG, phIsotropic_of gramIsoEq_holds D hG, phDual_of phDualOfGram_holds D hG,
    sDiff_of sDiffOfGram_holds D hG hb, stmt_endIntW_holds D he, splitZero_of' splitZeroG_holds D he ha hn hb hB⟩


end Formalism.MainNotions.Ext
end
