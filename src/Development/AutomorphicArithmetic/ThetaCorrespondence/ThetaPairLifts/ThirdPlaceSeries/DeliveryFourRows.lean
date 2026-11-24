module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FireStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FramesExOfRealisationStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfDecayStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaFireRowRecTieStatement
public import Formalism.LocalRingCardinality.NFLeTwoMulTSq
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem atAll_fourRows' : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
      AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.summandRealBound 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.ThresholdPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.FramePointSummands 𝒜 σ := by
  intro hDS hHC hRD hCW 𝒜 σ
  have hF : AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ := fun Fm hc x hx i =>
    _root_.GlobalTheory.T.indefinite_scale_theta_equality_alt hDS hHC hRD hCW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B
  refine ⟨hF, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_⟩
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_bound_right_alt hRD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B (Fm.parT x hx i).nV_ge (hF Fm hc x hx i).1
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_identity_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).Rr (hF Fm hc x hx i).1
  · exact _root_.GlobalTheory.T.framesEx_of_realPins_indefinite_scale _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).pins
end GlobalTheory.Fc.Ind
end
end
