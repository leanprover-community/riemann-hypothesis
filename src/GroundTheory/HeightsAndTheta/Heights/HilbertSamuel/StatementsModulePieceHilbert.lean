module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModule
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.LengthLocQuotEqZero

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ModulePieceHilbert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J₁ J₂ : Ideal (MRing ι)) (N d : ℕ),
    IsMultiHomogIdeal J₁ → IsMultiHomogIdeal J₂ → J₂ ≤ J₁ → 0 < N →
    (∀ f ∈ J₁, (N : MRing ι) * f ∈ J₂) →
    (∀ W : Ideal (MRing ι), W.IsPrime → J₂ ≤ W → IsRelevant W →
      ringKrullDim (MRing ι ⧸ W) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∀ s : K → ℕ, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |Real.log (modPieceCard J₁ J₂ (a + s)) -
          (∑ᶠ W ∈ topComps J₂ d, ((multAt J₂ W : ℝ) - multAt J₁ W) * Real.log (charOf W) *
            (geoNum d W (fun _ k => (a k : ℤ)) : ℝ)) / (d.factorial : ℝ)| ≤
        C * ((∑ k, a k : ℕ) + 1 : ℝ) ^ d / ((∑ k, a k : ℕ) + 1 : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
