module

public import Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant
public import Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
public import Formalism.EllipticTorsion.Statement
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
public import Formalism.EllipticTorsion.EllipticTorsionProofs.NDeriv
public import Mathlib
public import Formalism.FormalGroupLog.LogDeterminesLaw
public import Formalism.EllipticTorsion.EllipticTorsionProofs.JetsTwo
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsSubgroupHolds
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion
public import Formalism.EllipticTorsion.EllipticTorsionProofs.TorInt
public import Formalism.EllipticTorsion.EllipticTorsionProofs.WSeries
public import Formalism.EllipticTorsion.EllipticTorsionProofs.WPoint
public import Formalism.EllipticTorsion.EllipticTorsionProofs.WChord
public import Formalism.EllipticTorsion.EllipticTorsionProofs.WSubst
public import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsUnitFactor
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsParamDef
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsHomDef
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeTwo
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeThree

@[expose] public section

universe u

namespace Formalism.ELL

theorem formal_group_points_subgroup : FormalGroupPointsSubgroup'.{u} := formal_group_points_subgroup_holds
theorem formal_group_points_no_torsion : FormalGroupPointsTorsionFree.{u} := formal_group_points_no_prime_to_p_torsion
theorem torsionIntegral : TorsionIntegral.{u} := torsionIntegral_of formal_group_points_no_torsion

theorem wSeriesUnique : WSeriesUnique.{u} := wSeriesExistsUnique_holds
theorem wSeriesLead : WSeriesLead.{u} := wSeriesLeadingTerm_holds
theorem wSubstUnique : WSubstUnique.{u} := wSeriesSubstUnique_holds
theorem wPoint : WPoint.{u} := wSeriesNonsingularPoint_holds
theorem wChordSeries : WChordSeries.{u} := wChordSeries_of wSubstUnique
theorem wChordSubst : WChordSubst.{u} := wChordSubst_of wSeriesSubstUnique_holds
theorem wFormalGroup : WFormalGroup.{u} := by
  apply wFormalGroup_of <;> first | exact wChordSeries | exact wChordSubst | exact wPoint | exact wSubstUnique | exact wSeriesUnique | exact wSeriesLead

theorem formal_group_points_param : FormalGroupPointsParametrisation.{u} := by
  apply formal_group_points_param_of <;> first | exact intValuedZp | exact nAddSubgroup | exact nZpSmul | exact nPderiv | exact lwP₂ | exact unitCancel | exact compExpWeight | exact lemma2Weights | exact frobExpand | exact wFormalGroup | exact formal_group_points_subgroup | exact formal_group_points_no_torsion | exact isoExpand | exact isoVanish | exact changeIntegral | exact wPoint | exact wSubstUnique | exact wChordSubst | exact wChordSeries | exact veluIntegralModel | exact veluUSeries | exact modelUnit

theorem cubeTwo : CubeTwo.{u} := cube_two
theorem cubeThree : CubeThree.{u} := chordDeterminantFactor_holds

end Formalism.ELL
