module

public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
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

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def DiscStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (K₀ : Subfield K),
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K) →
    ∀ S : Set K, (∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1) →
    (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε) →
    ∀ (c : ℤ → K) (b : ℕ), (∀ n, n < -(b : ℤ) → c n = 0) →
      (∀ t ∈ S,
        Filter.Tendsto (fun n => ‖c n * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ∀ τ ∈ K₀, ‖τ‖ = 1 → ‖∑' n, c n * (t * τ) ^ n‖ ≤ 1) →
      ∀ n, ‖c n‖ ≤ 1 ∧ (n < 0 → c n = 0)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
