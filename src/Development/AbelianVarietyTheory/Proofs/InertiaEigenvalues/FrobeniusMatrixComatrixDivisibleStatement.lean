module

public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixComatrixDivisible
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

open Matrix

theorem _root_.GlobalTheory.T.pow_dvd_entries_of_mul_eq_diagonal_pow : ∀ {R : Type} [CommRing R] [IsDomain R] (d N N₀ q : ℕ) (p : Fin d → ℕ) (ξ : R) (A A' B B' c c' V₀ V₀' : Matrix (Fin d) (Fin d) R), ξ ≠ 0 → B * B' = 1 → c * c' = 1 → V₀ * V₀' = 1 → A * A' = ξ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → ξ ^ q • (A * B * c) = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j)) → N₀ ≤ N → (∀ i, |(p i : ℤ) - q| ≤ N₀) → (∀ i j, ξ ^ (N - N₀) ∣ A i j) ∧ ∀ i j, ξ ^ (N - N₀) ∣ A' i j := by
  first | (exact @GlobalTheory.frobenius_matrix_comatrix_divisible) | (exact GlobalTheory.frobenius_matrix_comatrix_divisible) | (intros; apply GlobalTheory.frobenius_matrix_comatrix_divisible  <;> assumption)
