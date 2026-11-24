module

public import Formalism.SatakeDualWeyl.Statement
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

namespace GlobalTheory

theorem gram_hermitian_and_trace_fixed :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, σ (σ x) = x) → σ δ = -δ →
  ∀ (n' r : ℕ) (JT : GL (Fin n') L) (z : Matrix (Fin n') (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ k j, σ (Γ k j) = - Γ j k) →
  (∀ j k, σ ((Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) j k) = (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) k j) ∧
  σ (δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z))) =
    δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z)) := by
  intro L _ _ σ δ hσ hδ n' r JT z Γ hJ hΓ
  have h1 : ∀ j k, σ ((Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) j k) =
      (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) k j := by
    intro j k

    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum,
    map_mul, hσ, hJ, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  refine ⟨h1, ?_⟩
  generalize Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z = G at h1 ⊢
  have h2 : σ (Matrix.trace (Γ * G)) = - Matrix.trace (Γ * G) := by

    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, hΓ, h1,
    ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [map_mul, hδ, h2]
  ring

end GlobalTheory
