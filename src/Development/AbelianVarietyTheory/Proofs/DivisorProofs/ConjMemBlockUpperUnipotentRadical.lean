module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

theorem blockUni_conj_mem (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ)
    (e : ι ≃ Fin a ⊕ Fin b) :
    ∀ p ∈ GlobalTheory.OrbDesc.blockPar (K := K) e, ∀ n ∈ GlobalTheory.OrbDesc.blockUni e,
      p * n * p⁻¹ ∈ GlobalTheory.OrbDesc.blockUni e := by
  intro p hp n hn
  obtain ⟨x, rfl⟩ := hn
  have hre : ∀ M N : Matrix ι ι K,
      Matrix.reindex e e (M * N) = Matrix.reindex e e M * Matrix.reindex e e N := by
    intro M N
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  have h21 : ∀ g ∈ blockPar (K := K) e, (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₂₁ = 0 := by
    intro g hg
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.zero_apply]
    apply hg
    simp [side]
  set P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K := Matrix.reindex e e (p : Matrix ι ι K) with hP
  set Q : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K :=
    Matrix.reindex e e ((p⁻¹ : GL ι K) : Matrix ι ι K) with hQ
  have hP21 : P.toBlocks₂₁ = 0 := h21 p hp
  have hQ21 : Q.toBlocks₂₁ = 0 := h21 _ (Subgroup.inv_mem _ hp)
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← hre, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp
  refine ⟨Multiplicative.ofAdd (fun i j => (P.toBlocks₁₁ * Matrix.of x.toAdd * Q.toBlocks₂₂) i j), ?_⟩
  apply Units.ext
  apply (Matrix.reindex e e).injective
  show Matrix.reindex e e (uMat e _) = Matrix.reindex e e ((p : Matrix ι ι K) * uMat e x.toAdd * ((p⁻¹ : GL ι K) : Matrix ι ι K))
  rw [hre, hre, ← hP, ← hQ]
  have hU : ∀ Y : Fin a → Fin b → K, Matrix.reindex e e (uMat e Y) = Matrix.fromBlocks 1 (Matrix.of Y) 0 1 := by
    intro Y
    simp [uMat]
  rw [hU, hU]
  rw [← Matrix.fromBlocks_toBlocks P, ← Matrix.fromBlocks_toBlocks Q] at hPQ ⊢
  rw [hP21, hQ21] at hPQ ⊢
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hPQ
  obtain ⟨h11, h12, -, h22⟩ := hPQ
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add] at h11 h12 h22 ⊢
  rw [h11, h22]
  congr 1
  have key : P.toBlocks₁₁ * Q.toBlocks₁₂ + (P.toBlocks₁₁ * Matrix.of x.toAdd + P.toBlocks₁₂) * Q.toBlocks₂₂
      = P.toBlocks₁₁ * Matrix.of x.toAdd * Q.toBlocks₂₂ := by
    rw [Matrix.add_mul, ← add_assoc, add_comm (P.toBlocks₁₁ * Q.toBlocks₁₂), add_assoc, h12, add_zero]
  rw [key]
  ext i j
  simp

end GlobalTheory.OrbDesc
