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
public import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices

private def toGLQ (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℚ).mapMatrix M)
    (by rw [← RingHom.map_det]; simpa using hM)

private lemma toGL_eq_map (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    toGL M = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (toGLQ M hM) := by
  ext i j
  rw [toGL_val M hM]
  simp [toGLQ, Matrix.GeneralLinearGroup.map]

lemma isCusp_SL2Z_toGL_smul (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) {c : OnePoint ℝ}
    (hc : IsCusp c 𝒮ℒ) : IsCusp (toGL M • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  rw [toGL_eq_map M hM]
  exact ⟨toGLQ M hM • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem cuspAll_slash_toGL : ∀ (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (G : ℍ → ℂ), 0 < M.det →
    CuspAll k G → CuspAll k (G ∣[k] toGL M) := by
  intro k M G hM hG
  refine ⟨MDifferentiable.slash hG.1 k (toGL M), fun c hc => ?_⟩
  rw [← OnePoint.IsZeroAt.smul_iff]
  exact hG.2 _ (isCusp_SL2Z_toGL_smul M hM.ne' hc)

end GlobalTheory.HeckeFamilyMatrices
