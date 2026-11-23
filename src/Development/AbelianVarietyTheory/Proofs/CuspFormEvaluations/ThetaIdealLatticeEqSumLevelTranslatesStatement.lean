module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaIdealLatticeEqSumLevelTranslates
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.theta_ideal_lattice_eq_sum_level_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ F : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ F → (∀ u : Matrix (Fin n) (Fin r) E, (∀ b, u b ∈ 𝔐 • L) → ∀ z, F z = epsW X (w : E) u * cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (u b)) (pv X idx x (u b)))) * F (fun b => z b + pv X idx x (u b))) → ∃ (s : Finset (Matrix (Fin n) (Fin r) E)) (cf : Matrix (Fin n) (Fin r) E → ℂ), (∀ y ∈ s, ∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ z, F z = ∑ y ∈ s, cf y * (κ * thA X bas idx (heisG X bas y v) x z) := by
  first | exact @GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates | exact GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates | (intros; apply GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates <;> assumption)
