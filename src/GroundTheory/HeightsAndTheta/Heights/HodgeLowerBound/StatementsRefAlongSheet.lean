module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
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

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def RefAlongSheet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (A : HermLine ι) (S : LogLogRegularisationSetting M Xo A)
    (γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ) (j : Fin S.R.N),
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P) →
    M.proj (γ y) ∈ (S.R.chart j).source →
    (∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ (S.R.chart j).source ∧
      DifferentiableAt ℂ (fun y'' => S.R.chart j (M.proj (γ y''))) y') →
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G y ∧ ∀ᶠ y' in 𝓝 y,
      Real.log (S.ref.h (γ y')) = S.R.q j (S.R.chart j (M.proj (γ y'))) + (G y').re

end GroundTheory.Heights₂.Heights.LowerBoundFree
