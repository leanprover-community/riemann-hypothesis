module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpLogCoverBound
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.family_exp_log_cover_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n a : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (ρ : ℝ) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), 0 < ρ → ρ ≤ 1 → Flat.IsHolPts (Metric.ball 0 ρ) ψ → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x)) (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) → Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) → (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) → (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) → (∀ x : W, per x ∈ e.per ((ρ : ℂ) • z)) ∧ (∀ p ∈ e.per ((ρ : ℂ) • z), ∃ x : W, per x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : W), 0 < N → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N) → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x)) (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x')) (unitOn ζ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice <;> assumption)
