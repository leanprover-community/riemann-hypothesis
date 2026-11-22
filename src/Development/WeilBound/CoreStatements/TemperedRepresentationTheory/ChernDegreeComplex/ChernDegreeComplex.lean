import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqIntegralTopChernFormComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace PositivityTheory.Tls2.Chern2

theorem chernDegreeComplex : GlobalTheory.Published.ChernDegreeComplex :=
  _root_.GlobalTheory.ChernDegree.chernDegreeComplex

end PositivityTheory.Tls2.Chern2
