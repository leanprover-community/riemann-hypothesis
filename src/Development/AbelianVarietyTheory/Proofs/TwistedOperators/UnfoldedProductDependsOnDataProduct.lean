import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearLeftLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearRightLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearLeftLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearRightLargeDepth

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.RowVal.conLin_big : Big fun ch => ConLin ch :=
  GlobalTheory.RowReal.big_mono (fun ch h => GlobalTheory.ConnectionLinear.conLin_of_positions ch h.1.1.1 h.1.1.2 h.1.2 h.2)
    (((GlobalTheory.T.thetaContraction_linear_left_largeDepth.and GlobalTheory.T.thetaContraction_linear_right_largeDepth).and GlobalTheory.T.lastSeesaw_linear_left_largeDepth).and GlobalTheory.T.lastSeesaw_linear_right_largeDepth)
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedProduct_depends_on_dataProduct : Big fun ch => ConLin ch := by
  atlas_forward_decl GlobalTheory.RowVal.conLin_big
