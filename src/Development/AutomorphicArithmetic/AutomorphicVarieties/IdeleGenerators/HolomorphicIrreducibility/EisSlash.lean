module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

noncomputable section

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private def slashEquiv (N : ℕ) (x : ZMod N) (a b c d : ℤ) (hdet : a * d - b * c = 1) (hc : (c : ZMod N) = 0) :
    {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = x} ≃
      {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = x * (d : ZMod N)} where
  toFun v := ⟨(v.1.1 * a + v.1.2 * c, v.1.1 * b + v.1.2 * d), by
    obtain ⟨⟨m, n⟩, h1, h2⟩ := v
    simp only at h1 h2
    constructor <;> simp [h1, h2, hc]⟩
  invFun v := ⟨(v.1.1 * d - v.1.2 * c, -(v.1.1 * b) + v.1.2 * a), by
    obtain ⟨⟨m, n⟩, h1, h2⟩ := v
    simp only at h1 h2
    have h : (a : ZMod N) * d = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod N) hdet
      push_cast at this
      simpa [hc] using this
    constructor
    · simp [h1, hc]
    · push_cast
      rw [h1, h2]
      linear_combination x * h⟩
  left_inv v := by
    obtain ⟨⟨m, n⟩, h⟩ := v
    apply Subtype.ext
    apply Prod.ext
    · show (m * a + n * c) * d - (m * b + n * d) * c = m
      linear_combination m * hdet
    · show -((m * a + n * c) * b) + (m * b + n * d) * a = n
      linear_combination n * hdet
  right_inv v := by
    obtain ⟨⟨m, n⟩, h⟩ := v
    apply Subtype.ext
    apply Prod.ext
    · show (m * d - n * c) * a + (-(m * b) + n * a) * c = m
      linear_combination m * hdet
    · show (m * d - n * c) * b + (-(m * b) + n * a) * d = n
      linear_combination n * hdet

theorem eisSlash : EisSlash := by
  intro N k _ _ a γ hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ
  ext z
  rw [ModularForm.SL_slash_apply]
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (z : ℂ) = (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) := by
    simp [denom]
  have hsm : ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have hne : (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0 := by
    rw [← hden]
    exact denom_ne_zero _ z
  have key : ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) = (γ 0 0 : ℂ) * z + (γ 0 1 : ℂ) := div_mul_cancel₀ _ hne
  rw [hden]
  unfold eisFun
  rw [hsm, mul_assoc, ← tsum_mul_right]
  rw [← (slashEquiv N a (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) hdet hc).tsum_eq]
  congr 1
  congr 1
  funext v
  rw [← mul_zpow]
  congr 1
  simp only [slashEquiv, Equiv.coe_fn_mk]
  push_cast
  linear_combination ((v : ℤ × ℤ).1 : ℂ) * key

end UpperTheory.V.Sd
