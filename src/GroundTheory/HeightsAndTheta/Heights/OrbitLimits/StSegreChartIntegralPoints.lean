module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartObjects
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StokesObjects
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

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar ptsIntegral pot segre PBlk)
open GroundTheory.Heights₂.Heights (varInt IsDegZeroSmooth segreChartSet segreChartComponents chartLift)

def SegreChartIntegralPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin 0 → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (δ : ℝ)
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin 0 → (Fin m → ℂ) → ℝ),
    IsArithVar P 1 → IsDegZeroSmooth g → 0 < δ →
    (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    (∀ x ∈ segreChartSet P σ i, G =ᶠ[𝓝 x] g ∘ chartLift σ i) →
      ptsIntegral P (pot L) g = ∑ J ∈ segreChartComponents P σ i, varInt J 0 G Φ

end GroundTheory.Heights₂.Heights.Targets
