module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxCount
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxSmall
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxLattice
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

theorem CurveBoxCount.proof (hS : CurveBoxSmall.Statement) (hL : CurveBoxLattice.Statement) :
    CurveBoxCount.Statement := by
  intro K _ ι _ Ω _ y A c R hP hB hA hc hR hRu
  obtain ⟨C, hC⟩ := hL K ι Ω y A c R hP hB hA hc hR hRu
  refine ⟨C, fun τ hτ => ?_⟩
  have e : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ =
      Real.log (Nat.card {s : chartLat y A.a τ //
        ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / chartUnit y c A.a τ)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ}) := by
    unfold smallSectionCount
    rw [Nat.card_congr (Equiv.subtypeEquivRight (p := fun s : chartLat y A.a τ => IsSmallH (mCoordIdeal y) y A τ (s : Ω))
      fun s => hS K ι Ω y A c hP hB hc τ (s : Ω))]
  rw [e]
  exact hC τ hτ

end GroundTheory.Heights₂.Heights.Targets
