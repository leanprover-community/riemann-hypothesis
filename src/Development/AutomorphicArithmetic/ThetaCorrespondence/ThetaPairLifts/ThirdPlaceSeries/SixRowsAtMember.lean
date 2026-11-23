module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTwistCoresOverTrueColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeColumnValuationsBundlePointsOverColumnStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealSideColumnsCompatibleBundlePointsOverColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferenceChainEvaluationBundlePointsOverColumnsAStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferencePeriodIntegralBundlePointsOfOverColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainEvaluationRationalIntegralBundlePoinStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodsIntegralAtBundlePointsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc
theorem six_rows_at_member_alt : ∀ (𝒮 : Slots) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPointAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.Row_tie S Lk) ∧
    (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints S Lk) := by
  intro 𝒮 Lk
  have hC : OverCols (sAnd (IsGoodE 𝒮) fun _ _ _ _ _ => True) :=
    (GlobalTheory.T.goodTwistCores_over_trueColumns 𝒮 (fun _ _ _ _ _ => True)).2
  have hT : LargeBaseCondition KPx (IsBuiltE 𝒮) fun _ _ _ _ _ => True := largeBaseProperty_true
  exact ⟨⟨_, hT, GlobalTheory.T.referenceChainEvaluationAtBundlePoints_of_overCols _ hC _ Lk⟩, ⟨_, hT, GlobalTheory.T.twistedChainEvaluation_rational_integral_bundlePoints _ hC _ Lk⟩,
    ⟨_, hT, GlobalTheory.T.referencePeriodIntegral_bundlePoints_of_overColumns _ hC _ Lk⟩, ⟨_, hT, GlobalTheory.T.twistedPeriods_integral_at_bundlePoints _ hC _ Lk⟩,
    ⟨_, hT, GlobalTheory.T.realSideColumnsCompatible_bundlePoints_overColumns _ hC _ Lk⟩, ⟨_, hT, GlobalTheory.T.levelPrimeColumnValuations_bundlePoints_overColumns _ hC _ Lk⟩⟩
end GlobalTheory.Fc
end
