module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def GraphIsometricForms.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) (d : ℕ) (g : (Σ k, ι₂ k) → MRing ι) (δ : K₂ → K → ℕ)
    (B₁ : HermLine ι) (B : HermLine ι₂) (B₁' B' : HermLine (Sum.elim ι ι₂)),
    IsArithVar P d → (∀ q, IsMultiHomog (g q) (δ q.1)) → IsBasePtFree P g →
    (∀ k, B₁.a k = ∑ k₂, B.a k₂ * (δ k₂ k : ℤ)) →
    (∀ z ∈ mcPts P, B₁.h z = B.h (formApply g z)) →
    IsPullHerm Sum.inl inlV B₁ B₁' → IsPullHerm Sum.inr inrV B B' →
    IsIsometricOn (graphIdeal P g) B₁' B'

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
