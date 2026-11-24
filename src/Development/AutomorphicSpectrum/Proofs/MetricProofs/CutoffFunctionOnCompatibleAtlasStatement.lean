module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CutoffFunctionOnCompatibleAtlas
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

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.cutoff_function_on_compatible_atlas : ∀ (n p q : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas n X) (Z Cl U : Set X) (r : X → ℝ) (Γ : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), A.Compatible B → (∀ k, Metric.closedBall (0 : Fin n → ℂ) 2 ⊆ (B.chart k).target) → (∀ x, ∃ k, x ∈ (B.chart k).source ∧ B.chart k x ∈ Metric.ball (0 : Fin n → ℂ) 1) → IsClosed Z → IsClosed Cl → IsOpen U → U ⊆ Cl → (∀ x, x ∉ Z → Real.exp 1 ≤ r x) → (∀ (k : Fin B.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → (B.chart k).symm w₀ ∈ Cl → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (B.chart k).symm w ∉ Z → (Γ ((B.chart k).symm w)).PosDef ∧ ((Γ ((B.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)).PosSemidef ∧ (((C * r ((B.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - (Γ ((B.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => Γ ((B.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => Γ ((B.chart k).symm w') a b) w‖ ≤ C * Real.exp (r ((B.chart k).symm w) / 2)) → (∀ a b, A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).re) ∧ A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).im)) ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → (∀ x ∈ Cl \ Z, (((r x ^ C : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ x)).PosSemidef ∧ (((r x ^ C : ℝ) : ℂ) • blockG (Γ x) - 1).PosSemidef) ∧ ∀ (a b : Fin (p + q)) (k : Fin B.n), ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2), (B.chart k).symm w ∈ Cl \ Z → ‖fderiv ℝ (fun w' => blockG (Γ ((B.chart k).symm w')) a b) w‖ ≤ C * r ((B.chart k).symm w) ^ C * Real.exp (r ((B.chart k).symm w) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds | exact GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds | (intros; apply GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds <;> assumption)
