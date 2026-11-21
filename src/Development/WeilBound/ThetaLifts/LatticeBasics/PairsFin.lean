import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
import Development.WeilBound.ThetaLifts.LatticeBasics.PolFin
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
import Development.WeilBound.ThetaLifts.SmallCones.SoStab
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid

section
namespace GlobalTheory.ThK.Dbl

theorem polFinTri : PolFin := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => polFin (PositivityTheory.ThKG.pairV h)

theorem pairsIrr_of_arch (hO : PositivityTheory.ThKF.ArchOp) : PairsIrr :=
  pairsIrr_of PositivityTheory.ThKH.Locrep.locRepEx PositivityTheory.ThKF.pureAct hO polFinTri

end GlobalTheory.ThK.Dbl
end

section
namespace GlobalTheory.ThK.Dbl

theorem pairsIrr : PairsIrr := pairsIrr_of_arch PositivityTheory.ThKF.A.archOp

theorem pairsStable : PairsStable :=
  pairsStable_of (PositivityTheory.ThKEnd.Grp.matchStab_of PositivityTheory.ThKF.A.archOp PositivityTheory.ThKF.pureAct PositivityTheory.ThKEst.level PositivityTheory.ThKCT.soStab_of)

end GlobalTheory.ThK.Dbl
end
