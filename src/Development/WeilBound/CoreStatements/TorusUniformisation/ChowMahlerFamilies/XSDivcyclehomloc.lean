module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
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

namespace PositivityTheory.Xgn.A_s_divcyclehomloc

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem homLocRingLocal : HomLocRingLocal.Statement.{0} :=
  HomLocRingLocal.proof (HomLocRingIsLocal.proof HomLocRingMem.proof)
    (HomLocRingNoetherian.proof HomLocRingMem.proof)
    (HomLocRingDimLe.proof HomLocRingMem.proof (HomLocRingIsLocal.proof HomLocRingMem.proof))

end PositivityTheory.Xgn.A_s_divcyclehomloc

theorem PositivityTheory.Xgn.t_s_divcyclehomloc : GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.Statement.{0} :=
  GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.proof PositivityTheory.Xgn.A_s_divcyclehomloc.homLocRingLocal
