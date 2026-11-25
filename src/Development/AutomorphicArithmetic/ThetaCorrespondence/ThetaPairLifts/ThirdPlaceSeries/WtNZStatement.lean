module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ

@[expose] public section



section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

theorem _root_.GlobalTheory.T.lift_weight_numerator : _root_.GlobalTheory.CovTop.LiftWeightNumerator := by
  first | exact @_root_.GlobalTheory.CovTop.WtShape.wtN_z
end
