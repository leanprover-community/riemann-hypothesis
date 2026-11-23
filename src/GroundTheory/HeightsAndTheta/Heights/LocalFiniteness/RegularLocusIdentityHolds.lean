module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMGeneralPoint
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightOneGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffCentre
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthTransverseSlice
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusIdentity
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserBranchSimpleZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMGeneralPoint
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMHeightOneGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveGermComponents
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveProperClosedFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveRegularOffCentre
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFibreRadicalAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicDerivNeZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthTransverseSlice
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalizeQuotientStages
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusIdentity
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUniformiserBranchSimpleZero
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds
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

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadicalAway : GroundTheory.Heights₂.Heights.GenericFibreRadicalAway.Statement :=
  @GroundTheory.Heights₂.Heights.GenericFibreRadicalAway.proof GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadical

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffCentre : GroundTheory.Heights₂.Heights.CurveRegularOffCentre.Statement :=
  @GroundTheory.Heights₂.Heights.CurveRegularOffCentre.proof GroundTheory.Heights₂.Heights.CurveGermComponents.proof GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffFinite GroundTheory.Heights₂.Heights.CurveProperClosedFinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LengthTransverseSlice : GroundTheory.Heights₂.Heights.LengthTransverseSlice.Statement :=
  @GroundTheory.Heights₂.Heights.LengthTransverseSlice.proof GroundTheory.Heights₂.Heights.AutoClose.CMLengthParameters GroundTheory.Heights₂.Heights.LocalizeQuotientStages.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CMGeneralPoint : GroundTheory.Heights₂.Heights.CMGeneralPoint.Statement :=
  @GroundTheory.Heights₂.Heights.CMGeneralPoint.proof GroundTheory.Heights₂.Heights.AutoClose.CMLocusOpen

theorem GroundTheory.Heights₂.Heights.AutoClose.UniformiserBranchSimpleZero : GroundTheory.Heights₂.Heights.UniformiserBranchSimpleZero.Statement :=
  @GroundTheory.Heights₂.Heights.UniformiserBranchSimpleZero.proof GroundTheory.Heights₂.Heights.AutoClose.UniformiserLocallyInjective GroundTheory.Heights₂.Heights.InjectiveHolomorphicDerivNeZero.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CMHeightOneGeneral : GroundTheory.Heights₂.Heights.CMHeightOneGeneral.Statement :=
  @GroundTheory.Heights₂.Heights.CMHeightOneGeneral.proof GroundTheory.Heights₂.Heights.AutoClose.CMLocusOpen

theorem GroundTheory.Heights₂.Heights.AutoClose.regular_locus_identity_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularLocusIdentity.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularLocusIdentity.proof GroundTheory.Heights₂.Heights.AutoClose.regular_off_hypersurface_holds
