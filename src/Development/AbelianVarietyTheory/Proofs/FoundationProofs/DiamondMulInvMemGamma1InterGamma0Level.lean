module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
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

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem dia_mul_inv_mem_lev : ∀ (N l : ℕ) (d : ℤ) (σ τ : SL(2, ℤ)), 0 < N →
    GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l d τ → τ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  intro N l d σ τ _ hσ hτ
  obtain ⟨hσc, hσd⟩ := hσ
  obtain ⟨hτc, hτd⟩ := hτ
  have detσ := Matrix.SpecialLinearGroup.det_coe σ
  have detτ := Matrix.SpecialLinearGroup.det_coe τ
  rw [Matrix.det_fin_two] at detσ detτ
  have e00 : ((τ * σ⁻¹) 0 0 : ℤ) = τ 0 0 * σ 1 1 - τ 0 1 * σ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  have e10 : ((τ * σ⁻¹) 1 0 : ℤ) = τ 1 0 * σ 1 1 - τ 1 1 * σ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  have e11 : ((τ * σ⁻¹) 1 1 : ℤ) = τ 1 1 * σ 0 0 - τ 1 0 * σ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσc hτc
  push_cast at hσc hτc
  have hNl : (N : ℤ) * l ∣ (τ * σ⁻¹) 1 0 := by
    rw [e10]
    exact dvd_sub (dvd_mul_of_dvd_left hτc _) (dvd_mul_of_dvd_right hσc _)
  have hσN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hσc)
  have hτN : ((τ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hτc)
  have dσ : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - (σ 0 1 : ℤ) * (σ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) detσ
  have dτ : ((τ 0 0 : ℤ) : ZMod N) * (τ 1 1 : ℤ) - (τ 0 1 : ℤ) * (τ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) detτ
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · rw [e00]; push_cast
      linear_combination (τ 0 0 : ZMod N) * hσd - (τ 0 0 : ZMod N) * hτd + dτ
        + (τ 0 1 : ZMod N) * hτN - (τ 0 1 : ZMod N) * hσN
    · rw [e11]; push_cast
      linear_combination (σ 0 0 : ZMod N) * hτd - (σ 0 0 : ZMod N) * hσd + dσ
        + (σ 0 1 : ZMod N) * hσN - (σ 0 1 : ZMod N) * hτN
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hNl)
  · rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_left _ _) hNl)

end GlobalTheory.Hk
