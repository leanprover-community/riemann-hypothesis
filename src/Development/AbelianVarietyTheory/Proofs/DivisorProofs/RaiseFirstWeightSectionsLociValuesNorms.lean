module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem upAtPrime_groups_values_norms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (u : SmFn p) (a b : ℤ), (upperParabolic P u).H a b = P.H a b ∧ (∀ f, NV (upperParabolic P u) a b f = NV P a b f) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), val (upperParabolic P u) a b σ y f = val P a b σ y f * (Real.exp (-(a * u.u σ y) / 2) : ℝ) ∧ (upperParabolic P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(a * u.u σ y) / 2) := by
  intro k _ X _ p P u a b
  have key : ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      Real.exp (-(a * ((upperParabolic P u).L.φ σ).φ (pick ((upperParabolic P u).L.φ σ).isLB y) y + b * ((upperParabolic P u).A.φ σ).φ (pick ((upperParabolic P u).A.φ σ).isLB y) y) / 2)
        = Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)
          * Real.exp (-(a * u.u σ y) / 2) := by
    intro σ y
    rw [← Real.exp_add]
    congr 1
    show -(a * ((P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + u.u σ y) + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2 = _
    ring
  refine ⟨rfl, fun f => rfl, fun σ y f => ⟨?_, ?_⟩⟩
  · show ratVal _ y * ((Real.exp _ : ℝ) : ℂ) = ratVal _ y * ((Real.exp _ : ℝ) : ℂ) * _
    rw [key σ y, Complex.ofReal_mul, mul_assoc]
    rfl
  · show ‖ratVal _ y‖ * Real.exp _ = ‖ratVal _ y‖ * Real.exp _ * _
    rw [key σ y, mul_assoc]
    rfl

end GlobalTheory.HSAmp
