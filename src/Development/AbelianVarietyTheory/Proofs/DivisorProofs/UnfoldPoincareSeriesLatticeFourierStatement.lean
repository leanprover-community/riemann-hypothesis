module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldPoincareSeriesLatticeFourier
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.unfold_poincareSeries_lattice_fourier : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Γ : Type) [AddCommGroup Γ] (j : Γ →+ V), Function.Injective j → ∀ C : AddSubgroup Γ, (∀ R : ℝ, {c : Γ | c ∈ C ∧ ‖j c‖ ≤ R}.Finite) → Submodule.span ℝ (j '' (C : Set Γ)) = ⊤ → ∀ (n : ℕ) (t : Fin n → Γ) (Q : Γ → ℂ), (∀ x, Q x ≠ 0 → ∃ k, x - t k ∈ C) → (∀ k k', t k - t k' ∈ C → k = k') → (∀ x, ∀ c ∈ C, Q (x + c) = Q x) → ∀ F : V → ℂ, Integrable F μ → ∀ (a : Γ → ℂ) (l : Γ → V →ₗ[ℝ] ℝ), Summable (fun x => ‖a x‖) → l 0 = 0 → (∀ x, x ≠ 0 → l x ≠ 0) → (∀ x, a x ≠ 0 → ∀ c ∈ C, ∃ z : ℤ, l x (j c) = z) → (∀ v, ∑' x, Q x * F (j x + v) = ∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) → ∃ r : ℝ, 0 < r ∧ (∑ k, Q (t k)) * ∫ v, F v ∂μ = r * a 0 := by
  first | exact @GlobalTheory.PoincareUnfold.unfold_poincare_fourier | exact GlobalTheory.PoincareUnfold.unfold_poincare_fourier | (intros; apply GlobalTheory.PoincareUnfold.unfold_poincare_fourier <;> assumption)
