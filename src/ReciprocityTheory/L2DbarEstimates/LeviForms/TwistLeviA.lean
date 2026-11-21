import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ExistsChartPartition

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

noncomputable section

def tlFlr (a b s : ℝ) : ℝ := s + Real.smoothTransition ((a - s) / (a - b)) * (a - s)





def tlK (c t : ℝ) : ℝ :=
  -Real.log (tlFlr (19 / 20) (9 / 10) (c - t) + Real.log (tlFlr (19 / 20) (9 / 10) (c - t)))


open Filter Topology

def tlKp (c t : ℝ) : ℝ := (1 + 1 / (c - t)) / ((c - t) + Real.log (c - t))

def tlKpp (c t : ℝ) : ℝ :=
  1 / ((c - t) ^ 2 * ((c - t) + Real.log (c - t))) + ((1 + 1 / (c - t)) / ((c - t) + Real.log (c - t))) ^ 2












end

end ReciprocityTheory.L2DbarEstimates.I
