module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
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
public import Mathlib.NumberTheory.ModularForms.QExpansion
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem periodic_comp_ofComplex_of_vadd' {f : ℍ → ℂ} {M : ℝ} (hper : ∀ τ : ℍ, f (M +ᵥ τ) = f τ) :
    Function.Periodic (f ∘ ofComplex) M := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]
  · push_neg at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem qParam_add_period {M : ℝ} (hM : M ≠ 0) (z : ℂ) :
    Function.Periodic.qParam M (z + M) = Function.Periodic.qParam M z := by
  unfold Function.Periodic.qParam
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [show 2 * π * Complex.I * (z + M) / M = 2 * π * Complex.I * z / M + 2 * π * Complex.I by field_simp,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem isBoundedAtImInfty_of_periodic_of_polyBound :
    ∀ (f : ℍ → ℂ) (h : ℕ) (C : ℝ) (A : ℕ), 0 < h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
      (∀ τ : ℍ, f ((h : ℝ) +ᵥ τ) = f τ) →
      (∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ h → ‖f τ‖ ≤ C * τ.im ^ A) → IsBoundedAtImInfty f := by
  intro f h C A hh hf hper hbd
  set M : ℝ := (h : ℝ) with hMdef
  have hM : 0 < M := by simp [hMdef, hh]
  have hperF : Function.Periodic (f ∘ ofComplex) M := periodic_comp_ofComplex_of_vadd' hper

  have hbd' : ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ C * τ.im ^ A := by
    intro τ hτ
    set n : ℤ := ⌊τ.re / M⌋
    have h1 : (n : ℝ) ≤ τ.re / M := Int.floor_le _
    have h2 : τ.re / M < n + 1 := Int.lt_floor_add_one _
    have hw : 0 < ((τ : ℂ) - n * M).im := by simpa using τ.im_pos
    set σ : ℍ := ⟨(τ : ℂ) - n * M, hw⟩
    have hσ : f σ = f τ := by
      have := hperF.sub_int_mul_eq (x := (τ : ℂ)) n
      simp only [Function.comp_apply, ofComplex_apply] at this
      rw [← this, ofComplex_apply_of_im_pos hw]
    have hσim : σ.im = τ.im := by
      change ((τ : ℂ) - (n : ℂ) * (M : ℂ)).im = τ.im
      simp
    have hσre : σ.re = τ.re - n * M := by
      change ((τ : ℂ) - (n : ℂ) * (M : ℂ)).re = τ.re - n * M
      simp
    have hre1 : n * M ≤ τ.re := by rwa [le_div_iff₀ hM] at h1
    have hre2 : τ.re < (n + 1) * M := by rwa [div_lt_iff₀ hM] at h2
    have habs : |σ.re| ≤ h := by
      rw [hσre, abs_le]
      constructor <;> nlinarith
    rw [← hσ, ← hσim]
    exact hbd σ (hσim ▸ hτ) habs

  set g : ℍ → ℂ := fun τ ↦ f τ * Function.Periodic.qParam M τ with hg
  have hnormg : ∀ τ : ℍ, ‖g τ‖ = ‖f τ‖ * Real.exp (-2 * π * τ.im / M) := by
    intro τ
    simp [hg, norm_mul, Function.Periodic.norm_qParam]
  have hgdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g :=
    hf.mul ((Function.Periodic.differentiable_qParam (h := M)).comp_mdifferentiable
      UpperHalfPlane.mdifferentiable_coe)
  have hgper : ∀ τ : ℍ, g (M +ᵥ τ) = g τ := by
    intro τ
    simp only [hg, hper, coe_vadd]
    rw [add_comm, qParam_add_period hM.ne']
  have hgzero : IsZeroAtImInfty g := by
    set c : ℝ := 2 * π / M with hc
    have hcpos : 0 < c := by positivity
    have hT : Tendsto (fun y : ℝ ↦ C * (c⁻¹) ^ A * ((c * y) ^ A * Real.exp (-(c * y)))) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero A).comp
        (tendsto_id.const_mul_atTop hcpos)).const_mul (C * (c⁻¹) ^ A)
    have heq : ∀ y : ℝ, C * (c⁻¹) ^ A * ((c * y) ^ A * Real.exp (-(c * y))) =
        C * y ^ A * Real.exp (-2 * π * y / M) := by
      intro y
      have : -(c * y) = -2 * π * y / M := by rw [hc]; ring
      rw [this, mul_pow, ← mul_assoc, ← mul_assoc, mul_assoc C, ← mul_pow, inv_mul_cancel₀ hcpos.ne',
        one_pow, mul_one]
    simp_rw [heq] at hT
    have hT' : Tendsto (fun τ : ℍ ↦ C * τ.im ^ A * Real.exp (-2 * π * τ.im / M)) atImInfty (𝓝 0) :=
      hT.comp tendsto_comap
    refine squeeze_zero_norm' ?_ hT'
    refine (atImInfty_mem _).2 ⟨1, fun τ hτ ↦ ?_⟩
    rw [Set.mem_setOf_eq, hnormg]
    exact mul_le_mul_of_nonneg_right (hbd' τ hτ) (Real.exp_pos _).le
  have hgbdd : IsBoundedAtImInfty g := hgzero.boundedAtFilter
  have hdecay := hgzero.exp_decay_atImInfty hM (periodic_comp_ofComplex_of_vadd' hgper) hgdiff hgbdd
  obtain ⟨K, hK⟩ := hdecay.bound
  obtain ⟨B, hB⟩ := (atImInfty_mem _).1 hK
  refine isBoundedAtImInfty_iff.2 ⟨K, B, fun τ hτ ↦ ?_⟩
  have h1 := hB τ hτ
  simp only [Set.mem_setOf_eq, hnormg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  exact le_of_mul_le_mul_right h1 (Real.exp_pos _)

end GlobalTheory
