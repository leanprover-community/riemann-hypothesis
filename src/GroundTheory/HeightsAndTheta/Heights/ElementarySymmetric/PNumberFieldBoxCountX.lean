module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNumberFieldBoxCount
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCovolumeRelIndex
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PEmbeddingSumPlaces
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeCountVolume
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeImageZLattice
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PMixedBoxCount
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNumberFieldBoxCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace GroundTheory.Heights₂.Heights.Targets

theorem NumberFieldBoxCount.proof_closed : NumberFieldBoxCount.Statement :=
  NumberFieldBoxCount.proof LatticeImageZLattice.proof CovolumeRelIndex.proof EmbeddingSumPlaces.proof
    (MixedBoxCount.proof LatticeCountVolume.proof)

end GroundTheory.Heights₂.Heights.Targets
