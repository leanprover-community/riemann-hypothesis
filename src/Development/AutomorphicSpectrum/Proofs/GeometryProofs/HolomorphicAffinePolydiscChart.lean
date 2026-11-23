module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsHolomorphicChartAtPoint
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hol_polydisc_chart : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ) (T : Set X), SmoothOfRelativeDimension d s → Geo.ResK.HasSncCoords s d T → ∀ (x : Sp ℂ ⟶ X) (W : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ∃ (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W ∧ a ≤ d ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ Set.InjOn ψ (ball 0 1) ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ (centre (spMap (ψ z) ≫ hV.fromSpec) ∉ T ↔ z ∈ punct d a 1)) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧ κ b₀ = 0 ∧ ∀ b ∈ ball b₀ ε, κ b ∈ ball (0 : Fin d → ℂ) 1 ∧ y b = spMap (ψ (κ b)) ≫ hV.fromSpec :=
  @PositivityTheory.Xgn.exists_holomorphic_chart_at_point

end GlobalTheory.CompanionTheory.Ar.Flat
