module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutComponentSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutNonemptySt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutOneGeneratorSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsClaimSeq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWLift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoFiltSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleProductPosSt
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A36
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FullOfCharts
import Development.WeilBound.CoreStatements.HodgeTatePoints.Imports
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Assembly
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimSeq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutComponent
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutDimLower
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutMultPos
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutNonempty
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutOneGenerator
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutZeroNotLe
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGlobalFunctionsIntegral
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointDegreePos
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PQuotTrans
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWLift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoPiece
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoReduce
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSplit
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleProductPos
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZeroIdealChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.HtPt.Ktw

theorem a52 :
    GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator.proof
    GroundTheory.Heights₂.Heights.Kleiman.GlobalFunctionsIntegral.proof

theorem a53 :
    GroundTheory.Heights₂.Heights.Kleiman.CutNonempty.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutNonempty.proof a52

theorem a54 :
    GroundTheory.Heights₂.Heights.Kleiman.CutComponent.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutComponent.proof
    GroundTheory.Heights₂.Heights.Kleiman.CutZeroNotLe.proof a53
    GroundTheory.Heights₂.Heights.Kleiman.CutDimLower.proof

theorem a55 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleProductPos.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleProductPos.proof hR
    GroundTheory.Heights₂.Heights.Kleiman.PointDegreePos.proof a54
    GroundTheory.Heights₂.Heights.Kleiman.CutMultPos.proof

theorem a56 :
    GroundTheory.Heights₂.Heights.Kleiman.ClaimSeq.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.ClaimSeq.proof
    GroundTheory.Heights₂.Heights.Kleiman.ZeroIdealChart.proof

theorem a57 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Filt.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Filt.proof
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.Exists.proof

theorem a58 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Reduce.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Reduce.proof a57
    GroundTheory.Heights₂.Heights.Kleiman.QuotTrans.proof
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Piece.proof

theorem a59 :
    GroundTheory.Heights₂.Heights.Kleiman.ClaimVanish.Statement.{0, 0} :=
  PositivityTheory.HtPt.KtwS.ClaimVanish.assembled a58 a4
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.TwistSplit.proof a56

theorem a60 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Statement.{0, 0, 0} :=
  PositivityTheory.HtPt.KtwS.StepTwo.assembled a58 a4
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.TwistSplit.proof

theorem a61 :
    GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Lift.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Lift.proof a56 a59 a60

theorem a62 :
    GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen.proof a4
    GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated.proof

theorem a63 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.assembled a39 a43 a48 a51 hR (a55 hR) a61 a62
    GroundTheory.Heights₂.Heights.Kleiman.PointGenerated.proof

theorem a72 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleNefPlusAmple.assembled a39 a43 a48 a51 hR (a55 hR) a61 a62
    GroundTheory.Heights₂.Heights.Kleiman.PointGenerated.proof

end PositivityTheory.HtPt.Ktw
