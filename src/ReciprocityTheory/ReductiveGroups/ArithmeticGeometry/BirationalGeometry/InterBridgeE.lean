module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeAnalytic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeD
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem analyticAt_lift_chart (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => R.lift x ((R.A.chart j).symm v)) u := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.analyticAt_lift_chart R.toAnRes x j hu

theorem brQ_eq_local {x z : R.X} (hz : z ∈ R.U x) :
    brQ R Ψ z = fun i => Ψ (segre (R.lift x z)) i.succ / Ψ (segre (R.lift x z)) 0 := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.brQ_eq_local R.toAnRes Ψ hz

theorem analyticAt_segre_lift (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((R.A.chart j).symm v)))) u := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.analyticAt_segre_lift R.toAnRes Ψ x j hu

theorem analyticAt_brQ (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.analyticAt_brQ R.toAnRes Ψ x j hj h0

theorem brQ_image_null_of
    (hS : ∀ j, volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.brQ_image_null_of R.toAnRes Ψ hS

end ReciprocityTheory.ChartRestriction.G.Geo
