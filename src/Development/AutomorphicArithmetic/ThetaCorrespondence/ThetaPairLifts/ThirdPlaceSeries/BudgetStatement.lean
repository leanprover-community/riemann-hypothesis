import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeightStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BudgetAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
theorem _root_.GlobalTheory.T.budget_of_hostN_of_liftWeight_of_size : (∀ M, _root_.GlobalTheory.CovTop.HostNAlt M) → _root_.GlobalTheory.CovTop.LiftWeightNumerator → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition := by
  atlas_forward_decl _root_.GlobalTheory.CovHt.BudgetPf.budget_alt
end
