module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMono
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLog
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSection
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailShift
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.OfListTailLog
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdCocycle
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdComparison
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdDivides
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdEqHolo
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdMetric
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdNormCont
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdPartition
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdSectionProps
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdTransition
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdWeight
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBddOnInner
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PChartCont
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PCoordDivDivisible
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PHyperplaneDivisible
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PIndicatorSmooth
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailLog
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMono
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMonoDens
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMonoRaise
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLocDensContOnOpen
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormHolo
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PMIntMonoOfDensLe
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PMIntegrableOfDensLe
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PNormSqSmooth
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegRCont
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegSection
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegYoDense
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailLogOfMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailShift
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open GroundTheory.Heights₂.Heights.AnalyticLimit

theorem ListMono.full : ListMono.Statement :=
  ListMono.proof ListMonoRaise.proof ListMonoDens.proof LocDensContOnOpen.proof
    MIntegrableOfDensLe.proof MIntMonoOfDensLe.proof

theorem RegSection.full : RegSection.Statement :=
  RegSection.proof RegYoDense.proof RegRCont.proof
    (BdMetric.proof ChartCont.proof
      (BdTransition.proof RegYoDense.proof BdEqHolo.proof
        (BdDivides.proof (CoordDivDivisible.proof HyperplaneDivisible.proof)))
      (BdCocycle.proof RegYoDense.proof BdEqHolo.proof)
      (LogNormHolo.proof ChartCont.proof)
      (BdWeight.proof BdPartition.proof IndicatorSmooth.proof NormSqSmooth.proof))
    (BdSectionProps.proof BdEqHolo.proof)
    (BdNormCont.proof ChartCont.proof BdEqHolo.proof)
    (BdComparison.proof ChartCont.proof BddOnInner.proof)

theorem TailShift.full : TailShift.Statement := TailShift.proof

theorem LemmaETailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : LemmaETailLog.Statement :=
  LemmaETailLog.proof h TailLogOfMass.proof

theorem ListTailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : ListTailLog.Statement :=
  ListTailLog.of_lemmaE (LemmaETailLog.of_lemmaETailMass h) ListMono.full RegSection.full
    TailShift.full

end GroundTheory.Heights₂.Heights.ForSecondHalf
