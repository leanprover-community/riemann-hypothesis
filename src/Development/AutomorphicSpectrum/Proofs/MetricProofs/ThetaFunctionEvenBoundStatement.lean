module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionEvenBound
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.theta_function_even_bound : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), 1 ≤ g → (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → (∀ l : a.u.Λ, a.χ l ^ 2 = 1) → ∀ (θ : (Fin g → ℂ) → ℂ) (b : ℝ), a.IsTheta 1 θ → a.IsThetaMeanSquareNorm θ b → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ √(2 * g) ∧ (∀ w, a.nrm 1 θ w ≤ b * Real.exp (g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g))) ∧ ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ), (∀ i, (m : ℂ) • r i ∈ a.u.Λ ∧ θ (r i) ≠ 0) → (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ a.u.Λ → θ w ≠ 0 → ∃! i, w - r i ∈ a.u.Λ) → Nonempty Ix ∧ (Fintype.card Ix : ℝ) * (Real.pi / 96 * (ρ ^ 2)⁻¹ - (g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g))) ≤ ∑ i, -Real.log (a.nrm 1 θ (r i) / b) := by
  exact @GlobalTheory.CompanionTheory.Ar.NForm.nform
