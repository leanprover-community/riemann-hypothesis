module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRatioProductFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.local_ratio_product_formula : ∀ (L : Type) [Field L] [NumberField L] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (a : K → ℤ) (w : (Σ k, J k) → L) (c₀ : (k : K) → J k) (u : L),
    (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → u ≠ 0 →
    (∀ v, 0 < locRatio a w c₀ v) ∧ (Function.mulSupport (locRatio a w c₀)).Finite ∧
    ∑ᶠ v : FinitePlace L, (Real.log (locRatio a w c₀ v) - Real.log (v u)) =
      (∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
        ∑ σ : L →+* ℂ, (Real.log ‖σ u‖ + ∑ k, (a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum.ratio_sum | exact GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum.ratio_sum | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum.ratio_sum <;> assumption)
