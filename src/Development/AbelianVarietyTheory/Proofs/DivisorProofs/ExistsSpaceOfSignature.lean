module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem hasSignature_diag_signs (p q : ℕ) : Formalism.UG.HasSignature
    (Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ)) p q := by
  have hne : ∀ (i : Fin p) (j : Fin q), Fin.castAdd q i ≠ Fin.natAdd p j := fun i j h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  refine ⟨(finSumFinEquiv (m := p) (n := q)).symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply,
      Matrix.one_apply, (Fin.castAdd_injective p q).eq_iff]
    simp [Examples₂.sgn, Nat.not_le.2 i.isLt]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne i j)]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne j i).symm]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply,
      Matrix.neg_apply, Matrix.one_apply, (Fin.natAdd_injective q p).eq_iff]
    split_ifs <;> simp [Examples₂.sgn]

theorem exists_isV : ∀ (D : D7) (ν q : ℕ), q ≤ ν → ∃ X : LSp D, X.IsV ν q := by
  intro D ν q h
  obtain ⟨p, rfl⟩ : ∃ p, ν = p + q := ⟨ν - q, by omega⟩
  refine ⟨⟨diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q, GlobalTheory.PlaceModel.latFrame _⟩, rfl, fun τ => ?_,
    fun τ => ?_, GlobalTheory.PlaceModel.isSelfDualC_latFrame _⟩
  · have hg : (diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ =
        Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ) := by
      rw [diagSp_gram]
      ext i j
      change τ (if i = j then _ else 0) = if i = j then _ else 0
      by_cases hij : i = j <;> simp [hij, Examples₂.map_sgn]
    change Formalism.UG.HasSignature ((diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ) p q
    rw [hg]
    exact hasSignature_diag_signs p q
  · rw [Nat.add_sub_cancel]
    rfl

end GlobalTheory.ChiGrid
