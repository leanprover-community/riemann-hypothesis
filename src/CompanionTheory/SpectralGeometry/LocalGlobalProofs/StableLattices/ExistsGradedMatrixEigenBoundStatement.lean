module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsGradedMatrixEigenBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Matrix
open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo
theorem _root_.GlobalTheory.T.exists_graded_matrix_eigen_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε) (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) (f : ℝ → ℝ) (α β : ℝ), (∀ l : ℝ, 0 < l → (f l = -1 ∨ f l = 0 ∨ f l = 1) ∧ f l⁻¹ = - f l) → (∀ i, f (hT.eigenvalues i) = -1 → α ≤ hT.eigenvalues i) → (∀ i, f (hT.eigenvalues i) = 0 → β⁻¹ ≤ hT.eigenvalues i) → (∃ i, f (hT.eigenvalues i) ≠ 0) → ∃ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' ∧ ∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤ nsq (S7.toM g⁻¹ *ᵥ y) := by
  exact SpecGrad.grading_of_spectral
