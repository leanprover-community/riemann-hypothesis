module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointAnalyticDisc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.dvr_point_analytic_disc : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W : X.Opens) (x : Cpt ξ) (N : X.Opens) (f : Ω), LocallyOfFiniteType s → IsCptGen ξ → genPt ξ ∈ W → x.1 ∉ W → x.1 ∈ N → IsDiscreteValuationRing (regAt ξ x) → f ∉ regAt ξ x → ∃ (V : X.Opens) (hV : IsAffineOpen V) (ψ : (Fin 1 → ℂ) → (Γ(X, V) →+* ℂ)) (r : (Fin 1 → ℂ) → ℂ) (C : ℝ), V ≤ N ∧ IsHolPts (ball 0 1) ψ ∧ (∀ z ∈ ball (0 : Fin 1 → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ genPt ξ ⤳ centre (spMap (ψ z) ≫ hV.fromSpec)) ∧ ∀ z ∈ punct 1 1 1, ⊤ ≤ (spMap (ψ z) ≫ hV.fromSpec) ⁻¹ᵁ W ∧ ValAt ξ (spMap (ψ z) ≫ hV.fromSpec) f (r z) ∧ r z ≠ 0 ∧ ‖(r z)⁻¹‖ ≤ C * ‖z 0‖ := by
  exact @GlobalTheory.CompanionTheory.Relay.dvr_point_analytic_disc
