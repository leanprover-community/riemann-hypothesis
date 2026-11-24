module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreIncomp
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocResidueDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreOverFinite
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocMaxIdeals
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueAdjoin
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueDeg
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFibreDim
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFrac
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFnDegRelDeg
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjDeg
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.NumericalSegre
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

theorem projDeg_all :
    ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by
  intro F _ K _ ι _ K' _ ι' _
  exact GroundTheory.Heights₂.Heights.Targets.ProjDeg.of_found
    (GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof
        GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof
        GroundTheory.Heights₂.Heights.NumbersDVR.DivPushForwardLocalZero))
    GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg.proof F ι ι'

theorem semilocMaxIdeals_of_fibreIncomp (hFI : FibreIncomp.Statement) : SemilocMaxIdeals.Statement :=
  SemilocMaxIdeals.proof (FibreOverFinite.proof hFI) hFI SemilocIntegral.full LocRingDimOne.full

theorem semilocResidueDeg_of_fibreIncomp (hFI : FibreIncomp.Statement) (hFD : FibreDimStatement) :
    SemilocResidueDeg.Statement :=
  SemilocResidueDeg.proof (SemilocResidueFibreDim.proof (FibreDivSupp.proof hFI) hFD FibreDimensionZero.full)
    (SemilocResidueAdjoin.proof
      (SemilocResidueFrac.proof SemilocFinite.full (semilocMaxIdeals_of_fibreIncomp hFI))
      ChartScalingIndep.full)

end GroundTheory.Heights₂.Heights.ForSecondHalf
