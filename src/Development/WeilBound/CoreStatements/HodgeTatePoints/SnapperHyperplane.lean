module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumAdditive
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumEventual
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StMixedTwistShift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperHyperplaneSt
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumAdditive
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumEventual
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterSumTopVanish
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMixedTwistShift
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrLenEuler
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotDevissageX
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperSectionX
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubsetDiffConst
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDiffPoly
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplane
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplaneMid
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

namespace PositivityTheory.HtPt.Kra

open GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem snapperHyperplane : SnapperHyperplane.Statement.{u, w} :=
  SnapperHyperplane.proof SnapperQuotAdd.closed SnapperQuotDevissage.closed SnapperHyperplaneMid.proof

theorem mixedTwistShift : MixedTwistShift.Statement.{u, w} :=
  MixedTwistShift.proof snapperHyperplane SnapperSection.full SnapperDiffPoly.proof RestrLenEuler.proof
    SubsetDiffConst.proof

theorem interNumEventual : InterNumEventual.Statement.{u, w} :=
  InterNumEventual.proof snapperHyperplane SnapperSection.full

theorem interNumAdditive : InterNumAdditive.Statement.{u, w} :=
  InterNumAdditive.proof interNumEventual (InterSumTopVanish.proof mixedTwistShift)

end PositivityTheory.HtPt.Kra
