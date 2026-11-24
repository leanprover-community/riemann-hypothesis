module

public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PAENeighbourhoods
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PAETopologicalRing
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PClosureIsSubmonoid
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEDenseInAE
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEichlerAtPlace
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEichlerDense
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PHypPairExists
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PLocalInClosure
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PLocalRingHypotheses
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.POrthProjection
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PPlaceMaps
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAHolds
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAOpenHolds
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PTruncation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.StrongApprox

theorem AETopologicalRing.full : AETopologicalRing.Statement := AETopologicalRing.proof

theorem HypPairExists.full : HypPairExists.Statement := HypPairExists.proof

theorem EDenseInAE.full : EDenseInAE.Statement := EDenseInAE.proof AETopologicalRing.full

theorem OrthProjection.full : OrthProjection.Statement := OrthProjection.proof AETopologicalRing.full

theorem EichlerDense.full : EichlerDense.Statement :=
  EichlerDense.proof AETopologicalRing.full EDenseInAE.full OrthProjection.full

theorem ClosureIsSubmonoid.full : ClosureIsSubmonoid.Statement :=
  ClosureIsSubmonoid.proof AETopologicalRing.full EichlerDense.full

theorem LocalRingHypotheses.full : LocalRingHypotheses.Statement := LocalRingHypotheses.proof

theorem PlaceMaps.full : PlaceMaps.Statement := PlaceMaps.proof LocalRingHypotheses.full

theorem EichlerAtPlace.full : EichlerAtPlace.Statement := EichlerAtPlace.proof PlaceMaps.full

theorem LocalInClosure.full : LocalInClosure.Statement :=
  LocalInClosure.proof HypPairExists.full ClosureIsSubmonoid.full LocalRingHypotheses.full
    PlaceMaps.full EichlerAtPlace.full

theorem Truncation.full : Truncation.Statement := Truncation.proof LocalInClosure.full

theorem AENeighbourhoods.full : AENeighbourhoods.Statement :=
  AENeighbourhoods.proof AETopologicalRing.full PlaceMaps.full

theorem SAHolds.full : ReciprocityTheory.ChartRestriction.G.SA.SAStatement :=
  SAHolds.proof HypPairExists.full AENeighbourhoods.full Truncation.full

theorem SAOpenHolds.full : ReciprocityTheory.ChartRestriction.G.SA.SAOpenStatement :=
  SAOpenHolds.proof SAHolds.full AETopologicalRing.full

end GroundTheory.Heights₂.Heights.StrongApprox
