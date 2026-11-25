module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatement

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.rationality_of_resolution_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK
