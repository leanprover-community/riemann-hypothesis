module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable ChartPartition integralWith
  locDens chartPartMeasure integral_chartPartMeasure isFiniteMeasure_chartPartMeasure existsPartition
  locDensCont mIntegrableCont)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

theorem tendsto_ell : Tendsto ell (𝓝[>] 0) atTop :=
  Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

section Signed

variable {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

end Signed

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential)

attribute [local instance] projectiveLineBorel

attribute [local instance] projectiveLine_borelSpace

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
