module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumCut
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumPointDeg
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StMixedTwistShift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PCutRestrLenExact
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumCut
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumPointDeg
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFilt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFiltStep
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteSections
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumRestrict
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTail
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
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

namespace PositivityTheory.HtPt.Kra

open GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem surjectiveClosed : SurjectiveClosed.Statement.{u, w} :=
  SurjectiveClosed.proof Extension.proof IdealTwistFamily.proof (TildeVanish.proof SerreVanish.full)

theorem finiteSections : FiniteSections.Statement.{u, w} :=
  FiniteSections.proof Extension.proof (TildeTail.proof SerreTail.full)

theorem intersectionNumberCut_of_mixedTwistShift (h : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} :=
  InterNumCut.proof (CycleSplit.Filt.proof (CycleSplit.Filt.Step.proof surjectiveClosed finiteSections))
    (CutRestrLenExact.proof surjectiveClosed finiteSections) h

theorem interNumPointDeg : InterNumPointDeg.Statement.{u, w} :=
  InterNumPointDeg.proof (InterNumRestrict.proof
    (RestrLenRestrict.proof surjectiveClosed PrimeFiltration.RestrictQuot.proof))

end PositivityTheory.HtPt.Kra
