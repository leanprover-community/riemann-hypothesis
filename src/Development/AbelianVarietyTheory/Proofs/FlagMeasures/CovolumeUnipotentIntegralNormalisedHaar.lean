module

import Mathlib.Tactic.Linter.HaveILetI
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.CovarianceFormula

@[expose] public section

open scoped Classical ENNReal
open MeasureTheory

noncomputable section

namespace GlobalTheory.CovNFormulaPf

theorem main : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula :=
  Formalism.MainStatements.RowRest.covariance_formula

end GlobalTheory.CovNFormulaPf
