module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodEqTriangularOrthonormal
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.period_eq_triangular_orthonormal_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (D : Datum H) (r : ℕ) (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ), GoodEmb c σ → D.p = Dw.p → D.q = Dw.q → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → (r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0) → ∃ d : Fin g → ℝ, (∀ j, 0 < d j) ∧ ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D (fun j => relab c σ (e j).1) P → ∃ x₀ ∈ X.dom, IsUnitFr X x₀ ∧ ∃ h₀ : Matrix (Fin g) (Fin g) ℂ, IsUnit h₀.det ∧ (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧ (∀ a j, (h₀ *ᵥ P a) j = perFr X x₀ (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ ∀ a b, (hermForm (Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) (h₀ *ᵥ P a) (h₀ *ᵥ P b)).im = D.EF a b := by
  first | exact @GlobalTheory.FrameNorm.period_eq_triangular_orthonormal | exact GlobalTheory.FrameNorm.period_eq_triangular_orthonormal | (intros; apply GlobalTheory.FrameNorm.period_eq_triangular_orthonormal <;> assumption)
