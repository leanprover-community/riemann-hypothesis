module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CornerUnip

theorem corner_symm_castSucc {m : ℕ} (i : Fin m) :
    (stdSum (rfl : m + 1 = m + 1)).symm (Fin.castSucc i) = Sum.inl i := by
  rw [Equiv.symm_apply_eq]; ext; simp [stdSum_inl]

theorem corner_symm_last (m : ℕ) :
    (stdSum (rfl : m + 1 = m + 1)).symm (Fin.last m) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]; ext; simp [stdSum_inr]

variable {R : Type} [CommRing R] {m : ℕ}

theorem corner_cc (u : GL (Fin m) R) (i j : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.castSucc i) (Fin.castSucc j) = (u : Matrix _ _ R) i j := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc]

theorem corner_cl (u : GL (Fin m) R) (i : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.castSucc i) (Fin.last m) = 0 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc, corner_symm_last]

theorem corner_lc (u : GL (Fin m) R) (j : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.last m) (Fin.castSucc j) = 0 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc, corner_symm_last]

theorem corner_ll (u : GL (Fin m) R) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.last m) (Fin.last m) = 1 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_last]

end GlobalTheory.CornerUnip

open GlobalTheory.CornerUnip in
theorem GlobalTheory.CornerUnip.corner_unipB_superDiag : ∀ (R : Type) [CommRing R] (m : ℕ) (u : GL (Fin m) R), u ∈ unipB R (Fin m) → corner u ∈ unipB R (Fin (m + 1)) ∧ superDiag (corner u) = superDiag u := by
  intro R _ m u hu
  rw [mem_unipB] at hu
  obtain ⟨hl, hd⟩ := hu
  refine ⟨?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact corner_lc u j
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j =>
          rw [corner_cc]
          exact hl i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · induction i using Fin.lastCases with
      | last => exact corner_ll u
      | cast i => rw [corner_cc]; exact hd i
  · unfold superDiag
    simp only [Finset.sum_filter]
    simp [Fin.sum_univ_castSucc, corner_cc, corner_cl, corner_lc, corner_ll]
