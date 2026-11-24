module

public import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantMem
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DomPow
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylIntRat
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMul
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylSat
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockDiagBound
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockHerm
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockPos
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockRowAdj
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockWeightOrth
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRaise
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRowWeight
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HighestWeightVectorNeZero
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowNuSum
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRowDivStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.GradedWeylDivisibility

theorem bidetMem : BideterminantMem := bideterminantMem
theorem hwMem : HWMem := highestWeightVectorMem
theorem hwNe : HWNe := highestWeightVectorNeZero
theorem hwRowWeight : HWRowWeight := highestWeightVectorRowWeight
theorem dualWeylSat : DualWeylSat := dualWeylModuleSaturated
theorem dualWeylPoint : DualWeylPoint := dualWeylModuleMemIff
theorem dualWeylRowStable : DualWeylRowStable := dualWeylModuleRowActionStable
theorem rowDivStable : RowDivStable := dualWeylModuleRowDividedPowerStable
theorem dualWeylRowGraded : DualWeylRowGraded := dualWeylModuleRowGraded
theorem dualWeylMap : DualWeylMap := dualWeylModuleMap
theorem dualWeylIntRat : DualWeylIntRat := dualWeylModuleIntRat
theorem weylLeDual : WeylLeDual := by
  intro R _ r n hn ν hν
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hwMem R r n hn ν hν
  | cons x w ih => exact rowDivStable R r n ν x.1 x.2.1 x.2.2 _ ih
theorem dualWeylNonDom : DualWeylNonDom := dualWeylModuleNonDominant
theorem bidetDominance : BideterminantDominance := bideterminantDominance
theorem dualWeylMul : DualWeylMul := dualWeylModuleMul
theorem hwRaise : HWRaise := highestWeightVectorRaising
theorem weylRowDivStable : WeylRowDivStable := weylModuleRowDividedPowerStable
theorem rowNuSum : RowNuSum := rowPartSum
theorem fockHerm : FockHerm := fischerInnerConjSymm_holds
theorem fockPos : FockPos := fischerInnerPos
theorem fockWeightOrth : FockWeightOrth := fischerInnerWeightOrthogonal_holds
theorem fockSubAdj : FockSubAdj := fischerInnerSubstitutionAdjoint
theorem fockRowAdj : FockRowAdj := fischerInnerRowActionAdjoint
theorem domPow : DomPow := dominancePowerProduct_holds
theorem fockDiagBound : FockDiagBound := fockDiagBound_of domPow

end Formalism.GradedWeylDivisibility
