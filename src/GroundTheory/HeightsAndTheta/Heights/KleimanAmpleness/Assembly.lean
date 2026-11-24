module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GeneratedTwistSysZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropHilbWSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropTermSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountTopSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWLift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmplePowSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleProductPosSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LeadingCoeffPosCut
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleNefPlusAmple
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmplePow
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

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem GraphClosed.full : GraphClosed.Statement.{u, w} := GraphClosed.proof
theorem VeryAmplePow.full : VeryAmplePow.Statement.{u, w} := VeryAmplePow.proof

theorem SectionExists.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) : SectionExists.Statement.{u, w} :=
  SectionExists.proof (SectionCount.assembled hTop hF hT hH hR) VeryAmplePow.full
    (LeadingCoeffPos.proof_of_cut hR hPos)

theorem VeryAmpleNefPlusAmple.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    VeryAmpleNefPlusAmple.Statement.{u, w} :=
  VeryAmpleNefPlusAmple.proof Generated.full (SectionExists.assembled hTop hF hT hH hR hPos)
    (StepThree.assembled hL hG) GraphClosed.full hPt

theorem NefProductNonneg.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    NefProductNonneg.Statement.{u, w} :=
  NefProductNonneg.proof (VeryAmpleNefPlusAmple.assembled hTop hF hT hH hR hPos hL hG hPt) hR

end GroundTheory.Heights₂.Heights.Kleiman
