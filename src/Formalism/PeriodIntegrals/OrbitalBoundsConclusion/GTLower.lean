import Formalism.PeriodIntegrals.GTLower
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.GTBranchOf
import Formalism.PeriodIntegrals.SchurFock
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.SchurFockOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.GTLowerOf

section
theorem gelfand_tsetlin_branching : PI.GTBranch :=
  PI.WGB.gTBranch_of_steps highest_weight_irreducible (PI.WGB.extremalFacts_of_A highest_weight_irreducible) PI.WGB.fixed_line_exists
    PI.WGB.stable_complement_exists PI.WGB.highest_weight_vector_exists
    (PI.WGB.realize_of highest_weight_irreducible (PI.WGB.extremalFacts_of_A highest_weight_irreducible) PI.WGB.fixed_line_exists
      PI.WGB.stable_complement_exists PI.WGB.highest_weight_vector_exists)
end

section
theorem schur_fock : PI.SchurFock := PI.WSF.schurFock_of highest_weight_irreducible
end

section
theorem gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) : PI.GTLower :=
  PI.WGL.gTLower_of h2 highest_weight_irreducible gelfand_tsetlin_branching schur_fock
end
