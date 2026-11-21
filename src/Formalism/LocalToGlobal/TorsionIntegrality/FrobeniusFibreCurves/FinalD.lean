import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.XTwoDvdOfRestrictThirdZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Wp3ApplyEqSqMulSubSqMul
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.RealAdelicInertTransportTypeFormsEqAlt
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffLawWithInverseThree
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.FirstLevelOfThreeVarParallelogram
import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LawDifferenceThree

section
noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.L2.Th1.A (fgl iSer logSer wpReg g₂ g₃ IntModel)

def CurveFrobStick : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    (at1 0 (sgW W s2) * at1 1 (sgW W s2) * at1 2 (sgW W s2)) ^ 3 * det3 (wpReg W) =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
        (evalSumThree (sgW W s2) * evalDiffThree 0 1 (sgW W s2) * evalDiffThree 0 2 (sgW W s2) * evalDiffThree 1 2 (sgW W s2))

def CurveParThree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W → Simeq (par3 (fgl W) (iSer W) (phW W s2)) 0

def CurveCocycleIntegralAllResidues : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W →
    DivAB (beW W s2) ∧ swap2 (beW W s2) = beW W s2 ∧
      Simeq (d1 (fgl W) (beW W s2)) 0 ∧ Simeq (d1 (fgl W) (swap2 (beW W s2))) 0 ∧
      ∀ n : ℕ, 3 ≤ n → ‖PowerSeries.constantCoeff ((Dinv (logSer W))^[n] (phW W s2))‖ ≤ 1

end Formalism.L2.Th1.B
end
end

section
namespace Formalism.L2.Th1.B

open Formalism.L2.Th1.A (bridgeWp bridgeLaw bridgeCurve bridgeCurve3)

theorem shearLemma : ShearLemma := Wr.shearedWronskianUniqueness
theorem tauRule : TauRule := Det.tau_derivative_rule_holds
theorem detRule : DetRule := Det.determinant_derivative_rule_holds
theorem frobStickLog : FrobStickLog := Fs.FrobStickLog_of shearLemma tauRule detRule
theorem frobStick : FrobStick := Fs.FrobStick_of frobStickLog
theorem frobStickStar : FrobStickStar := Fs.FrobStickStar_of frobStick
theorem fIUnit : FIUnit := E2.formal_inverse_unit_holds
theorem parThree : ParThree := E2.ParThree_of frobStickStar fIUnit
theorem cubeFromPars : CubeFromPars := E3.cube_relation_from_parallelograms
theorem first_level_all_formal_groups : LogSigmaPullbackCocycleJets := E3.log_sigma_pullback_cocycle_jets_of_parallelogram_and_cube parThree cubeFromPars

end Formalism.L2.Th1.B
end
