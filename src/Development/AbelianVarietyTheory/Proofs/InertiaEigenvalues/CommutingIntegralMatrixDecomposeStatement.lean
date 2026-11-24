module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixDecompose
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

open GlobalTheory.UnitDiscAlg

theorem _root_.GlobalTheory.T.commuting_integral_matrix_decompose : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → ∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ x z a₁ a₂ a₃ : Matrix (Fin n) (Fin n) E, (x * N = N * x ∧ z * N = N * z ∧ a₁ * N = N * a₁ ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖x i j‖ ≤ 1 ∧ ‖z i j‖ ≤ 1 ∧ ‖a₁ i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ x * x - x = ϖ • a₁ ∧ y * (1 - x) = ϖ • a₂ ∧ y * z * x - x = ϖ • a₃ := by
  first | exact @GlobalTheory.UnitDiscAlg.Red.main | exact GlobalTheory.UnitDiscAlg.Red.main | (intros; apply GlobalTheory.UnitDiscAlg.Red.main <;> assumption)
