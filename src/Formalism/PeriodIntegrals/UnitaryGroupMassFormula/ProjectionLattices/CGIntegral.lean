import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.FinrankIntertw
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.IsIntegralTraceOfPow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.MajAtZeroRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.StarMapTraceOfPowEqOne

noncomputable section

namespace PI.Dv.GLP

open NumberField

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

def cG (T : GoodSet K G) (x : G) : K := ∑ s, cS T s x





end PI.Dv.GLP
