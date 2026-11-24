module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.TorusConjProof

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_inv_diag {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) : mat s⁻¹ = Matrix.diagonal (fun i => ϖ ^ (-b i)) := by
  have h : mat s * Matrix.diagonal (fun i => ϖ ^ (-b i)) = 1 := by
    rw [hs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  calc mat s⁻¹ = mat s⁻¹ * (mat s * Matrix.diagonal (fun i => ϖ ^ (-b i))) := by rw [h, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_zpow_diag {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) (d : ℤ) :
    mat (s ^ d) = Matrix.diagonal (fun i => ϖ ^ (d * b i)) := by
  induction d using Int.induction_on with
  | zero => simp [mat_one]
  | succ k ih =>
    rw [zpow_add_one, mat_mul, ih, hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ]
    congr 1
    ring
  | pred k ih =>
    rw [zpow_sub_one, mat_mul, ih, mat_inv_diag hϖ hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ]
    congr 1
    ring


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_conj_apply {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) (g : GU σ r) (i j : Fin r) :
    mat (s * g * s⁻¹) i j = ϖ ^ (b i - b j) * mat g i j := by
  rw [mat_mul, mat_mul, mat_inv_diag hϖ hs, hs, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg,
    zpow_add₀ hϖ]
  ring

theorem torusConj : GlobalTheory.SatakeWeyl.TorusConj := by
  intro L _ _ ϖ σ r γ b b' d s s' g hϖ hb hs hs' hg
  apply mat_injective
  ext i j
  rw [mat_conj_apply hϖ hs', mat_conj_apply hϖ (mat_zpow_diag hϖ hs d)]
  by_cases h : γ i = γ j
  · rw [hb i j h, mul_sub]
  · have h0 : mat g i j = 0 := hg i j h
    rw [h0, mul_zero, mul_zero]

end GlobalTheory.SatakeWeyl.TorusConjProof
