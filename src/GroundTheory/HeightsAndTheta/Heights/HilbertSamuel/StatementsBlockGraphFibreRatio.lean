module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphImage
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGraphFibreRatio.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
    ∀ (G : GenFibre (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M))) (k : K) (i j : ι k),
      G.x' ⟨Sum.inl k, j⟩ ≠ 0 → G.x' ⟨Sum.inl k, i⟩ / G.x' ⟨Sum.inl k, j⟩ ∈ (algebraMap G.Φ G.Φ').range

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
