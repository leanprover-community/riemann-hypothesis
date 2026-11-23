module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

lemma wOld_mul_ulFam (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (j : ℕ) :
    wOld N l a b * !![1, (j : ℤ); 0, (l : ℤ)] = (l : ℤ) • mat (gaOld N l a b h j) := by
  ext i m
  fin_cases i <;> fin_cases m <;>
    simp [wOld, gaOld, mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma wOld_det (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : (wOld N l a b).det = l := by
  rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * h

lemma mat_det_pos (γ : SL(2, ℤ)) : 0 < (mat γ).det := by simp [mat]

theorem trOld_eq : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ), 0 < l →
    trOld k N l a b h G = G + ((l : ℂ) ^ (2 - k)) • UlF k l (G ∣[k] toGL (wOld N l a b)) := by
  intro N l k a b h G hl
  have hW : 0 < (wOld N l a b).det := by rw [wOld_det N l a b h]; exact_mod_cast hl
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  unfold trOld
  congr 1
  rw [UlF, hkF, Finset.smul_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, ← toGL_mul _ _ hW.ne' (ulFam_det l hl j).ne']
  have e : wOld N l a b * ulFam l j = (l : ℤ) • mat (gaOld N l a b h j) := wOld_mul_ulFam N l a b h j
  rw [e, slash_toGL_smul k l hl _ (mat_det_pos _), smul_smul, ← zpow_add₀ hl', slash_SL_eq]
  simp

end GlobalTheory.HeckeFamilyMatrices
