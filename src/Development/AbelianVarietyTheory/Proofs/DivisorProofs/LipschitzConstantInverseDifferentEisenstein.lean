module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.LipEisConst

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

theorem absNorm_latM {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) :
    ((FractionalIdeal.absNorm (latM 𝔞) : ℚ) : ℝ) = (dF F * nrm 𝔞)⁻¹ := by
  rw [latM, map_mul, map_inv₀, Units.val_inv_eq_inv_val, map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    absNorm_differentIdeal F (𝓞 F), dF, nrm]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, mul_inv]

theorem lip_const_eis : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 1 ≤ k →
    ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lipConst k (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℂ) ^ (k - 1) = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) := by
  intro F _ _ 𝔞 k hk
  have hd : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hn : 0 < nrm 𝔞 := by
    have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
    have h3 := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) h2.symm
    unfold nrm; exact_mod_cast h3
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F) ≠ 0 := by
    apply pow_ne_zero
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  have hcov : covol (latM 𝔞) = (Real.sqrt (dF F) * nrm 𝔞)⁻¹ := by
    rw [covol, absNorm_latM, ← dF]
    have hs : Real.sqrt (dF F) * Real.sqrt (dF F) = dF F := Real.mul_self_sqrt hd.le
    have hs0 : 0 < Real.sqrt (dF F) := Real.sqrt_pos.2 hd
    field_simp
    rw [Real.sq_sqrt hd.le]

  set fac : ℝ := ((k - 1).factorial : ℝ) ^ Module.finrank ℚ F with hfac
  have hfac0 : 0 < fac := by positivity
  have hreal : nrm 𝔞 ^ (k - 1) / (fac * covol (latM 𝔞)) = omegaFactor 𝔞 ^ k / cK F k := by
    rw [hcov, omegaFactor, cK, ← hfac, mul_pow, ← Real.rpow_natCast (dF F ^ ((1:ℝ)/2)), ← Real.rpow_mul hd.le,
      Real.sqrt_eq_rpow]
    have hk' : ((k : ℝ) - 1) / 2 = (1:ℝ)/2 * k - 1/2 := by ring
    rw [hk', Real.rpow_sub hd]
    have hA : 0 < dF F ^ ((1:ℝ)/2 * k) := Real.rpow_pos_of_pos hd _
    have hB : 0 < dF F ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hd _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  have hc : (covol (latM 𝔞) : ℂ) ≠ 0 := by
    rw [hcov]; exact_mod_cast (inv_pos.2 (mul_pos (Real.sqrt_pos.2 hd) hn)).ne'
  have hf : (fac : ℂ) ≠ 0 := by exact_mod_cast hfac0.ne'
  calc _ = (((nrm 𝔞 ^ (k - 1) / (fac * covol (latM 𝔞)) : ℝ)) : ℂ) := by
        rw [lipConst, hfac]; push_cast
        rw [hfac] at hf; push_cast at hf
        field_simp
    _ = _ := by rw [hreal]; push_cast; rfl

end GlobalTheory.LipEisConst
