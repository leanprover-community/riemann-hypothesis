module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionSupBound
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

theorem _root_.GlobalTheory.T.theta_function_sup_bound : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → ∀ (m : ℕ) (θ : (Fin g → ℂ) → ℂ) (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ) (f : Ix → (Fin g → ℂ) → ℂ), 1 ≤ m → a.IsTheta 1 θ → θ ≠ 0 → (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ a.u.Λ → ∃ i, w - r i ∈ a.u.Λ) → (∀ i, (m : ℂ) • r i ∈ a.u.Λ) → (∀ i, a.IsTheta (m ^ 2) (f i)) → (∀ i (w : Fin g → ℂ) (N : ℕ), 1 ≤ N → (N : ℂ) • w ∈ a.u.Λ → a.nrm (m ^ 2) (f i) w = a.nrm 1 θ (r i + (m : ℂ) • w)) → (∀ i w, a.nrm (m ^ 2) (f i) w = a.nrm 1 θ (r i + (m : ℂ) • w)) ∧ ∀ F, a.IsTheta (m ^ 2) F → ∃ c : Ix → ℂ, F = ∑ i, c i • f i := by
  exact @GlobalTheory.CompanionTheory.ThetaSpan.theta_span
