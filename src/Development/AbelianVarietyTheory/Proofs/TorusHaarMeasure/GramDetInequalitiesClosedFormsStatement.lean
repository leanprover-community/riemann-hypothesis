module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetInequalitiesClosedForms
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

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
theorem _root_.GlobalTheory.T.gramDet_inequalities_closed_forms : (∀ (m α β γ : Type) [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (M : Matrix m (α ⊕ β ⊕ γ) ℂ), (((M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))).det.re) * (((M)ᴴ * (M)).det.re) ≤ (((M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))).det.re) * (((M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))).det.re)) ∧ (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) ∧ (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ ω ∧ ∀ (i : ℕ) (M : Matrix (Fin r) (Fin i) ℂ), 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re) ∧ (((M)ᴴ * (M)).det.re) ≤ ω * (((a * M)ᴴ * (a * M)).det.re)) ∧ (0 < i → i < r → ∑ a ∈ S, ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) ^ (-δ) ≤ S.card * c)) ∧ (∀ (r p : ℕ), 0 < p → p < r → ∃ S : Finset (Matrix (Fin r) (Fin r) ℂ), S.Nonempty ∧ (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) ∧ (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧ ∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ ∃ s : Matrix (Fin r) (Fin r) ℂ, (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ s * a = a⁻¹ * s) := by
  first | exact @GlobalTheory.gramDet_closed_forms | exact GlobalTheory.gramDet_closed_forms | (intros; apply GlobalTheory.gramDet_closed_forms <;> assumption)
