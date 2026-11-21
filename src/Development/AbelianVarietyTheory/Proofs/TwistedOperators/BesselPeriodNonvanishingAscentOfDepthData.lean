import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowDataHaveDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockConjugatesSpanDepthData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLiftsFixedByCongruenceDepthOfDepthData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRung
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselNonvanishingTower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiNonvanishingTower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodGridFramesOfDepthFixed

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_depFixed : DepFixed → Ascent := fun hD =>
  have hTot : FockTot := GlobalTheory.T.fockConjugates_span_depth_data
  have hPart : PartFixed := GlobalTheory.T.gridLiftsFixedByCongruenceDepth_of_depthData hD GlobalTheory.T.firstRow_data_have_depth
  GlobalTheory.T.besselPeriod_ascent_of_tower_rungs (GlobalTheory.T.existsGoodGridFrames_of_depthFixed hD) (GlobalTheory.T.nonvanishing_thetaTower_bottom_rung hTot) (GlobalTheory.T.fourierJacobi_to_bessel_nonvanishing_tower hTot hPart)
    (GlobalTheory.T.bessel_to_fourierJacobi_nonvanishing_tower hTot hPart)

end GlobalTheory.Asc
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_period_nonvanishing_ascent_of_depth_data : DepFixed → Ascent := by
  atlas_forward_decl GlobalTheory.Asc.ascent_of_depFixed
