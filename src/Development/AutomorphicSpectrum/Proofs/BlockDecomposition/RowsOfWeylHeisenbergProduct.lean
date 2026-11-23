module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.LowerRows

variable {K : Type} [Field K] {n ρ p : ℕ}

theorem block_matrix_mul {m : ℕ} (a b c d a' b' c' d' : Matrix (Fin m) (Fin m) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockMatrix_mul_blockMatrix (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K) (b b' : Matrix (Fin ρ) (Fin p) K)
    (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockMatrix_add (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K) (b b' : Matrix (Fin ρ) (Fin p) K)
    (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  simp only [bl]
  rw [← Matrix.fromBlocks_add]
  rfl

theorem lowerRight_block_matrix {m : ℕ} (a b c d : Matrix (Fin m) (Fin m) K) :
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (blk4 a b c d) = d := by
  ext i j
  simp only [GlobalTheory.CompanionTheory.RatPtsUnn.blkD, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₂₂]

theorem lower_rows_word (σ : K →+* K) (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K)
    (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K) :
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  simp only [wM, nM, sM, eM, rowC, rowD, block_matrix_mul, BigCell.lowerLeft_block, lowerRight_block_matrix, blockMatrix_mul_blockMatrix,
    blockMatrix_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero, and_self]

theorem lower_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K),
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  intro K _ σ _ n ρ p hn a b c d ζ η
  exact lower_rows_word σ hn a b c d ζ η

end GlobalTheory.CompanionTheory.ZUnf.LowerRows
