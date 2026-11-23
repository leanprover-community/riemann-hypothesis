module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmegaUnramifiedHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXCovolPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXFrameVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSDLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSIdx
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DvPosC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MassDataPosAllOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocVol
  Formalism.L2.SG.NGAnalytic.MassDataLemmas

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nTy_holds : OnTied fun D X hb Y u u' X0 ψ =>
    Formalism.L2.SG.MassDataConc.InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
      (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) := by
  intro _ _ _ _ _ _ _ _ D _ X Y u u' _ hb X0 ψ hT
  exact inTypedC_loc X hb Y.hK _ _ u u' X0 ψ _ 0 0 1 _ _ _ _ _ _ _
    (fun X v => SDL.sdLocX_holds X v) (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) sTypIdx_holds
    hT.2.1 hT.2.2.1

theorem frameVolAt_of_prodConv (hP : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ) : OnTied fun D X hb Y u u' X0 ψ =>
    FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
      (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT
  exact frameVolAt_of X hb Y u u' X0 ψ 0 0 1 _ _ _ _ _ hT.2.1 hT.2.2.1
    (hP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT)

theorem nPos_of (hSW : PI.VolStabS.MassDataS.SWXS) (hP : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ) :
    OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hH : Formalism.L2.SG.TypedSets.HypX X hb (Y.FN u) (Y.FN u') u u' :=
    ⟨hT.1, hCtx.2.2.1, Y.FN_fund u, Y.FN_fund u'⟩
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1
    (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)
    (locHaarPosC_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _)
    (covolPosC_of X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _ hSW hT.2.1 hT.2.2.2.1
      hT.1 hT.2.2.2.2.2.2)
    (Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of X hb Y u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _ hK2 hV)
    (recPosC_of_dv X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _
      (fun X v => dvPosC_holds X v) hH)
    (hP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT) (Formalism.L2.SG.Pf.MassDataPos.cooOf_pos X u u')
    (Formalism.L2.SG.WConst.kapN_pos (D := D)) le_rfl le_rfl one_pos

end Formalism.L2.SG.Pf.MassDataX
