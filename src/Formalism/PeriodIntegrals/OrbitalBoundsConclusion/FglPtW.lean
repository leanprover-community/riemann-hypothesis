module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.AddGenThm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.MulGenThm
public import Formalism.PeriodIntegrals.FglPtW

@[expose] public section

theorem formal_group_add_generation : PI.FglPtW.AddGen := PI.FglPtW.Wk.addGen_thm

theorem formal_group_mul_generation : PI.FglPtW.MulGen := PI.FglPtW.Wk.mulGen_thm

