module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepArith
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepBasic
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
import Mathlib.Tactic.ENatToNat
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

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Int

variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)

theorem rep_area_eq : area (cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2) := by
  rw [area, rep_omega1, rep_omega2]
  have hθ : (cmTheta b d).im = Real.sqrt d / 2 := by
    simp [cmTheta]
  have e : conj (lam * (a : ℂ)) * (lam * cmTheta b d) =
      ((Complex.normSq lam * a : ℝ) : ℂ) * cmTheta b d := by
    rw [map_mul, Complex.conj_natCast]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [e, Complex.im_ofReal_mul, hθ, abs_of_nonneg]
  exact mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (Real.sqrt_nonneg _) zero_le_two)

theorem rep_kappa_eq : repKappa a b d ha hd lam hlam = 2 / ((Real.sqrt d : ℝ) : ℂ) := by
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hsC : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hnC : ((Complex.normSq lam : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hlam).ne'
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [repKappa, rep_area_eq]
  push_cast
  field_simp

variable (m : Type) [Fintype m] [DecidableEq m]

theorem rep_H_int (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {x y : m → ℂ} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ∃ n c₂ : ℤ, stdH (cmL a b d ha hd lam hlam) m x y =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) ∧
      (stdH (cmL a b d ha hd lam hlam) m x y).im = c₂ := by
  have hxd : x ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ := by
    rw [hΛ]
    exact hx
  obtain ⟨c₂, hc₂⟩ := hxd y hy
  obtain ⟨m', hm'⟩ := hxd (cmTheta b d • y) (hθ y hy)
  have hsm : stdH (cmL a b d ha hd lam hlam) m x (cmTheta b d • y) =
      conj (cmTheta b d) * stdH (cmL a b d ha hd lam hlam) m x y := by
    rw [LinearMap.map_smulₛₗ]
    rfl
  have him : (stdH (cmL a b d ha hd lam hlam) m x y).im = c₂ := hc₂
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hsC : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'

  have hre : (b / 2 : ℝ) * c₂ - Real.sqrt d / 2 * (stdH (cmL a b d ha hd lam hlam) m x y).re = m' := by
    have h1 : (conj (cmTheta b d) * stdH (cmL a b d ha hd lam hlam) m x y).im = m' := by
      rw [← hsm]
      exact hm'
    rw [rep_conj_theta] at h1
    simp [Complex.mul_im, him] at h1
    linarith
  have hre' : (stdH (cmL a b d ha hd lam hlam) m x y).re = (b * c₂ - 2 * m') / Real.sqrt d := by
    field_simp
    linarith
  refine ⟨b * c₂ - m', c₂, ?_, him⟩
  rw [rep_kappa_eq, rep_conj_theta]
  calc stdH (cmL a b d ha hd lam hlam) m x y
      = ((stdH (cmL a b d ha hd lam hlam) m x y).re : ℂ) +
          ((stdH (cmL a b d ha hd lam hlam) m x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
    _ = _ := by
      rw [hre', him]
      push_cast
      field_simp
      ring

theorem rep_H_self_int (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {x : m → ℂ} (hx : x ∈ Λ) :
    ∃ n : ℤ, stdH (cmL a b d ha hd lam hlam) m x x = repKappa a b d ha hd lam hlam * n := by
  obtain ⟨n, c₂, h1, h2⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hx hx
  have him : (stdH (cmL a b d ha hd lam hlam) m x x).im = 0 := by
    rw [← rep_H_re (cmL a b d ha hd lam hlam) m x]
    simp
  have hc : (c₂ : ℂ) = 0 := by
    have : (c₂ : ℝ) = 0 := by rw [← h2, him]
    exact_mod_cast this
  refine ⟨n, ?_⟩
  rw [h1, hc]
  ring

end Int

end PI.UnitaryGroupMassFormula.UnimodLocStd
