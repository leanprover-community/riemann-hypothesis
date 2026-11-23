module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticConstantGenericBoundOfNormalisedStepsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticGenericBoundOfChoiceStepPositiveStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfCutBoundPositiveStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericHeightBoundOfLocalEstimatesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

theorem rowMainEqP_of_pinned (hCh : PN.NGChain) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLocGenPinnedG) (hT : StepThmBGP) : GlobalTheory.SnPos.RowMainEqP :=
  GlobalTheory.T.equalWordGenericBound_of_cutBound_positive hCh Formalism.L2.SG.Pf.MainEqCut.meanAmplitudeGeneric_holds
    (GlobalTheory.T.generic_height_bound_of_local_estimates Formalism.L2.SG.NGCut.sizes_of_hypotheses hC hN hP (stepHeightG_of_normOne hO)
      (GlobalTheory.T.analyticGenericBound_of_choiceStep_positive hTi hB (GlobalTheory.T.analyticConstantGenericBound_of_normalisedSteps hE hV hL hT)))

end GlobalTheory.SnPos
