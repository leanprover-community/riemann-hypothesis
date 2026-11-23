module

public import Formalism.HermitianCurvature.StatementU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BesselJUnitaryEquivariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset Matrix

namespace GlobalTheory

theorem sandwich_entry_sum {n : Type*} [Fintype n] (A M B : Matrix n n ℂ) (i j : n) :
    (A * M * B) i j = ∑ a, ∑ b, A i a * B b j * M a b := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem unitary_inv_eq_gram_conj {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  refine Matrix.inv_eq_left_inv ?_
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [mul_assoc, mul_assoc, ← mul_assoc gᴴ, h, BesselUnitary.gram_sq]

theorem unitary_conj_entry_and_inv_entry : ∀ (k r : ℕ) (i j : Fin (2 * r + k + 1)), (∃ co : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ, ∀ g ∈ B.GV k r, star (g i j) = ∑ a, ∑ b, co a b * g⁻¹ a b) ∧ ∃ q : B.Mat k r → ℂ, U.IsPolyDeg 1 q ∧ ∀ g ∈ B.GV k r, g⁻¹ i j = q g := by
  intro k r i j
  refine ⟨⟨fun a b => Hpk k r j a * Hpk k r b i, fun g hg => ?_⟩,
    fun g => (Hpk k r * gᴴ * Hpk k r) i j, ?_, fun g hg => by rw [unitary_inv_eq_gram_conj hg]⟩
  · have h : gᴴ = Hpk k r * g⁻¹ * Hpk k r := by
      rw [unitary_inv_eq_gram_conj hg]
      simp only [← mul_assoc]
      rw [BesselUnitary.gram_sq, one_mul, mul_assoc, BesselUnitary.gram_sq, mul_one]
    rw [← sandwich_entry_sum, ← h, Matrix.conjTranspose_apply]
  · refine ⟨∑ a, ∑ b, MvPolynomial.C (Hpk k r i a * Hpk k r b j) * MvPolynomial.X (Sum.inr (b, a)), ?_, fun g => ?_⟩
    · refine MvPolynomial.totalDegree_finsetSum_le fun a _ =>
        MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    · show (Hpk k r * gᴴ * Hpk k r) i j = _
      rw [sandwich_entry_sum]

      simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inr,
      Matrix.conjTranspose_apply]

end GlobalTheory
