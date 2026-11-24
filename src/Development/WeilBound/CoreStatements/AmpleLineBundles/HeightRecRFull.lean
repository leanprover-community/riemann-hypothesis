module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartDehom
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightRecR
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightAssemblyFull
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredPlacesFinite
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredRingNormal
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalLengthPlaces
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalNormalIndex
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCard
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCentred
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterChart
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSupp
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterLe
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterMemIff
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterPrime
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterZero
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartDehom
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMax
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMult
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartQuot
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartRing
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartTerm
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitConjSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatio
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDivVertical
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitFiniteSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitLocalSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlaceCentredSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlacesRingQuot
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PSubringPrimeMaximal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterMemIff
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMax
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartQuot

@[expose] public section

namespace CoverDenseAlt
open GroundTheory.Heights₂.Heights

theorem heightRecR_full : HeightRecR.Statement :=
  have hM : OrbitChartMax.Statement := OrbitChartMax.proof
  have hQ : OrbitChartQuot.Statement := OrbitChartQuot.proof
  have hIff : OrbitCenterMemIff.Statement := OrbitCenterMemIff.proof
  HeightRecR.proof OrbitDivVertical.proof
    (OrbitFiniteSum.proof OrbitDegreeRatio.proof
      (OrbitLocalSum.proof OrbitChartRing.proof hM
        (OrbitChartResidue.proof hM hQ (OrbitChartDehom.proof hM hQ))
        OrbitChartMult.proof
        (LocalLengthPlaces.proof LocalQuotCard.proof CentredPlacesFinite.proof
          (LocalQuotCentred.proof CentredRingNormal.proof LocalNormalIndex.proof) PlacesRingQuot.proof)
        OrbitCenterChart.proof PlaceCentredSum.proof OrbitChartTerm.proof)
      (OrbitCenterZero.proof OrbitCenterLe.proof hIff
        (OrbitCenterDivSupp.proof hIff (OrbitCenterPrime.proof hIff) SubringPrimeMaximal.proof)))
    (OrbitArchSum.of_conjSum OrbitConjSum.proof)

theorem chartDehom_full : OrbitChartDehom.Statement :=
  OrbitChartDehom.proof OrbitChartMax.proof OrbitChartQuot.proof

end CoverDenseAlt
