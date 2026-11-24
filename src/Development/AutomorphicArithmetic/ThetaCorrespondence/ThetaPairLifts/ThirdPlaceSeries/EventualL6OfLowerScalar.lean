module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualL6OfLowerBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCOnPtOfGuardedStatement
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

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem eventual_L6_of_lower_scalar_alt : _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
    (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.summandL6Bound 𝒜 σ := by
  intro h 𝒜 σ hd hr
  have hG : EvW (_root_.GlobalTheory.Fc.Ind.conditionOnPoint fun _ _ _ _ => True) 𝒜 σ :=
    Formalism.MainNotions.Pk.Closed.of_class fun Fm _ _ _ => ⟨0, fun _ _ _ _ => trivial⟩
  have key := _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun _ => True) (fun _ _ _ _ => True) lowScalarPt ?_ 𝒜 σ hd hr hG
  · exact key
  · obtain ⟨a, ha, h⟩ := h
    refine ⟨a, ha, fun e he hle => ?_⟩
    obtain ⟨K, hK⟩ := h e he hle
    refine ⟨K, fun Fm CH hc hL _ => ⟨0, le_rfl, ?_⟩⟩
    obtain ⟨x0, hx0⟩ := hK Fm CH hc hL
    exact ⟨x0, fun x hx hle i p hp _ C _ => hx0 x hx hle i p hp C⟩
end GlobalTheory.Fc.Ind
end
end
