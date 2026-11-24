module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartTorsion
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PIncidenceNull
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PLengthDecomp
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormEval
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormLocalization
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormLength
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParAlgIndep
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParDVRIsDVR
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParFracIsFractionRing
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PPrimitiveScale
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBFinite
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBGeneric
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PVertTermEq
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

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

theorem NormLength.full : NormLength.Statement := NormLength.proof
theorem VertTermEq.full : VertTermEq.Statement := VertTermEq.proof
theorem ParAlgIndep.full : ParAlgIndep.Statement := ParAlgIndep.proof
theorem NormFormEval.full : NormFormEval.Statement := NormFormEval.proof
theorem ChartTorsion.full : ChartTorsion.Statement := ChartTorsion.proof
theorem ChowFormHomog.full : ChowFormHomog.Statement := ChowFormHomog.proof
theorem IncidenceNull.full : IncidenceNull.Statement := IncidenceNull.proof
theorem LengthDecomp.full : LengthDecomp.Statement := LengthDecomp.proof
theorem NormFormLocalization.full : NormFormLocalization.Statement := NormFormLocalization.proof
theorem ParDVRIsDVR.full : ParDVRIsDVR.Statement := ParDVRIsDVR.proof
theorem ParFracIsFractionRing.full : ParFracIsFractionRing.Statement := ParFracIsFractionRing.proof
theorem PrimitiveScale.full : PrimitiveScale.Statement := PrimitiveScale.proof
theorem SecBGeneric.full : SecBGeneric.Statement := SecBGeneric.proof
theorem SecBFinite.full : SecBFinite.Statement :=
  SecBFinite.proof IncidenceNull.full ChartTorsion.full PrimitiveScale.full

end GroundTheory.Heights₂.Heights.Vertical
