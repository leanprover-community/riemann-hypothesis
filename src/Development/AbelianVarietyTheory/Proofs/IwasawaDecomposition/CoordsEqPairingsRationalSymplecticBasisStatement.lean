module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordsEqPairingsRationalSymplecticBasis
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

theorem _root_.GlobalTheory.T.coords_eq_pairings_rational_symplectic_basis : ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε φ : Fin g → Fin r → ℚ), r = 2 * g → Mqᵀ = -Mq → Mq.det ≠ 0 → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) → (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) → ∀ x : Fin r → ℚ, x = ∑ i, (-(x ⬝ᵥ Mq *ᵥ φ i)) • ε i + ∑ j, (x ⬝ᵥ Mq *ᵥ ε j) • φ j := by
  first | exact @GlobalTheory.coords_in_rational_symplectic_basis | exact GlobalTheory.coords_in_rational_symplectic_basis | (intros; apply GlobalTheory.coords_in_rational_symplectic_basis <;> assumption)
