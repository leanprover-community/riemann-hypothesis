module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountConstant
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountLocallyConstant
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StManifoldZerosComplementConnected
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
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Analysis.Analytic.Linear

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem UnbranchedProperCountConstant.proof (hloc : UnbranchedProperCountLocallyConstant.Statement)
    (hconn : ManifoldZerosComplementConnected.Statement) : UnbranchedProperCountConstant.Statement := by
  intro σ _ Y d A D δ hD hDc hmap hprop hδ hsec
  by_cases hne : ∃ y ∈ D, δ y ≠ 0
  swap
  · push Not at hne
    exact ⟨0, fun y hy hy' => absurd (hne y hy) hy'⟩
  obtain ⟨y₀, hy₀D, hy₀⟩ := hne
  have hreg : ∀ y ∈ D, IsRegularPointOf D y := fun y hy =>
    ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, analyticOnNhd_id, fun _ _ => rfl, by simp⟩
  have hS : IsPreconnected (D \ {z | δ z = 0}) := hconn (Fin d) D δ hDc hreg hδ ⟨y₀, hy₀D, hy₀⟩
  have hL := hloc σ Y d A D δ hD hmap hprop hsec
  let f : (Fin d → ℂ) → ℕ := fun y => {x | x ∈ Y ∧ A x = y}.ncard
  have hcont : ContinuousOn f (D \ {z | δ z = 0}) := by
    intro y hy
    refine ContinuousAt.continuousWithinAt ((continuousAt_const (y := f y)).congr ?_)
    filter_upwards [(hL y hy.1 hy.2).2] with y' hy'
    simp only [f, Set.ncard_def, hy']
  refine ⟨f y₀, fun y hy hyδ => ?_⟩
  rw [← (hL y hy hyδ).1.cast_ncard_eq]
  exact congrArg _ (hS.constant hcont ⟨hy, hyδ⟩ ⟨hy₀D, hy₀⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
