module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BlockResolutionMetricObjects
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def BlockResolutionMetricPair.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : HermLine ι) (P0' : Ideal (MRing ι)),
    A'.a = unitDeg d.k₀ → P0' ≤ mCoordIdeal d.y → IsSemipositiveRel P0' (mCoordIdeal d.y) A' →
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W₀ W₁ : Weight L) (dV : SmoothVolume A)
      (σ : ℕ → MvPolynomial (Σ k, ι k) ℚ → Fin A.n → d.R.X → ℂ),
      A.Compatible d.R.A ∧ W₀.IsSemipositive ∧ W₁.IsSemipositive ∧ dV.μ = d.dV ∧
      (∀ (n : ℕ) (b : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog b (blockDeg d.k₀ n) → σ n b ∈ L.sections n) ∧
      (∀ y : d.R.X, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
        (∀ (n : ℕ) (b : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog b (blockDeg d.k₀ n) →
          σ n b (chartIdx A y) y = eval (fun p => c p.1 * blockPt d y p) (map (algebraMap ℚ ℂ) b)) ∧
        W₀.φ (chartIdx A y) y = 2 * Real.log (d.A.h (fun p => c p.1 * blockPt d y p)) ∧
        W₁.φ (chartIdx A y) y = 2 * Real.log (A'.h (fun p => c p.1 * blockPt d y p))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ g : d.R.X → ℝ, Continuous g →
        ∫ y, g y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
          mInt d.R.A (fun _ => blockInterpPot d d.A A' t) g / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
