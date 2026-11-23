module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenRestrictSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsClaimSeq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTwistSplit
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsLineBundleTwistMulOf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanish
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleNefPlusAmple
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

namespace PositivityTheory.HtPt.KtwS

open GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem LineTwist.full_of_charts : LineTwist.Statement.{u, w} :=
  fun _ _ _ _ _ _ _ Q₁ Q₂ => ⟨KThm.lbTwist Q₁ Q₂, rfl⟩

theorem TwistAlg.full_of_charts : TwistAlg.Statement.{u, w} := by
  intro S _ Ω _ _ N x M p q m m' b₁ b₂ h
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  rw [KThm.sub_twist, KThm.sub_pow, KThm.sub_pow, KThm.sub_pow, KThm.sub_twistMul M p m I hi,
    KThm.sub_twistMul M q m' I hi, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
    KThm.span_zpow_pow I hi, KThm.span_zpow_pow I hi, KThm.span_zpow_pow I hi, mul_mul_mul_comm,
    ← pow_add, KThm.span_zpow_mul I hi]
  have e1 : p * (q * b₁ + b₂) = q * (p * b₁) + p * b₂ := by ring
  have e2 : m * ((q * b₁ + b₂ : ℕ) : ℤ) = m' * ((p * b₁ : ℕ) : ℤ) + m * (b₂ : ℤ) := by
    push_cast
    linear_combination (b₁ : ℤ) * h
  rw [e1, e2]

theorem StepTwo.assembled (hRed : StepTwo.Reduce.Statement.{u, v, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hS : TwistSplit.Statement.{u, w}) : StepTwo.Statement.{u, v, w} :=
  StepTwo.proof hRed LineTwist.full_of_charts TwistAlg.full_of_charts RestrictTwist.full
    (NefRestrict.assembled hRL) StepData.JProper.full SubvarDrop.full PrimeFiltration.Point.full
    PrimeFiltration.Restrict.full hRQ (TwistVanish.assembled hS)

theorem ClaimVanish.assembled (hRed : StepTwo.Reduce.Statement.{u, w, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hS : TwistSplit.Statement.{u, w}) (hCS : ClaimSeq.Statement.{u, w}) : ClaimVanish.Statement.{u, w} :=
  ClaimVanish.proof (StepTwo.assembled hRed hRL hRQ hS) (TwistVanish.assembled hS) hCS

end PositivityTheory.HtPt.KtwS
