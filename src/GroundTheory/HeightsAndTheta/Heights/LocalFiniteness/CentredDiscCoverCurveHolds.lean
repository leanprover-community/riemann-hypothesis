module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchFillDimension
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchGermDimOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchOffHypersurface
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCentredDiscCoverCurve
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscriminantSheetCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDominantFibreBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOffZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceOnComponent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntAdd
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarMassNearSmall
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchFillDimension
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchGermDimOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchOffHypersurface
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCentredDiscCoverCurve
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveMinimalPrimeQuotient
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDominantFibreBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOffZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimComponentBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogIntegrable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceOnComponent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PReducedNormalisationPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarIntAdd
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarMassNearSmall
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZeroDimIsolated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
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

theorem GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LogIntegrable : GroundTheory.Heights₂.Heights.LogIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.LogIntegrable.proof GroundTheory.Heights₂.Heights.SheetSumMeasurable.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompare GroundTheory.Heights₂.Heights.VarSlabMeasure.full GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite

theorem GroundTheory.Heights₂.Heights.AutoClose.VarIntAdd : GroundTheory.Heights₂.Heights.VarIntAdd.Statement :=
  @GroundTheory.Heights₂.Heights.VarIntAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.BranchGermDimOne : GroundTheory.Heights₂.Heights.BranchGermDimOne.Statement :=
  @GroundTheory.Heights₂.Heights.BranchGermDimOne.proof GroundTheory.Heights₂.Heights.LocalDimComponentBound.proof GroundTheory.Heights₂.Heights.ZeroDimIsolated.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full

theorem GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound : GroundTheory.Heights₂.Heights.DominantFibreBound.Statement :=
  @GroundTheory.Heights₂.Heights.DominantFibreBound.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full

theorem GroundTheory.Heights₂.Heights.AutoClose.branchFillDimension_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.centredDiscCoverCurve_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.full

theorem GroundTheory.Heights₂.Heights.AutoClose.PlaceOnComponent : GroundTheory.Heights₂.Heights.PlaceOnComponent.Statement :=
  @GroundTheory.Heights₂.Heights.PlaceOnComponent.proof GroundTheory.Heights₂.Heights.ReducedNormalisationPlace.proof GroundTheory.Heights₂.Heights.CurveMinimalPrimeQuotient.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem GroundTheory.Heights₂.Heights.AutoClose.LelongLimitOffZero : GroundTheory.Heights₂.Heights.LelongLimitOffZero.Statement :=
  @GroundTheory.Heights₂.Heights.LelongLimitOffZero.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.VarMassNearSmall : GroundTheory.Heights₂.Heights.VarMassNearSmall.Statement :=
  @GroundTheory.Heights₂.Heights.VarMassNearSmall.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact
