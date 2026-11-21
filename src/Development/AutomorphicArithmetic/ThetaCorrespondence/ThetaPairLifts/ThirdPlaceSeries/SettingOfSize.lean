import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun.SetFromSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
set_option maxHeartbeats 1600000 in
theorem setting_of_size_alt (p : PtAt ex Csz) (hp : p.PointConditions') (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (he : GlobalTheory.GLq.ESerTie D) :
    HidaSetting L p.R.toRealDat p.F.lv2 :=
  setting_of_exAt p hp.exAt hs he
end GlobalTheory.BigTop.Fun.SetFromSize
namespace GlobalTheory.BigTop.Fun
theorem setAt_of_sizeAt_alt (h : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt) : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint :=
  h.imp fun _ _ _ a => _root_.GlobalTheory.BigTop.Fun.evPt_mono a fun _ _ _ p hp b he => _root_.GlobalTheory.BigTop.Fun.SetFromSize.setting_of_size_alt p hp b he
end GlobalTheory.BigTop.Fun
end
end
