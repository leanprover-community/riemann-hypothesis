import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFinitePlaneMeasure
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel
open Ad3 Ad3.LFS GlobalTheory.CompanionTheory.LFDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LFDual.ZRho

section Compact

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isCompact_modulus_le (R : ℝ) : IsCompact {x : F | (modulus x : ℝ) ≤ R} := by
  have hq : (1 : ℝ) < (residueCard F : ℝ) := by exact_mod_cast one_lt_residueCard (K := F)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R hq
  have hO : IsCompact (𝒪[F] : Set F) := IsNonarchimedeanLocalField.isCompact_closedBall F 1
  set u : Fˣ := unifUnit F ^ (k : ℤ) with hu
  have hI : IsCompact ((fun y : F => y * ((u⁻¹ : Fˣ) : F)) '' (𝒪[F] : Set F)) :=
    hO.image (continuous_id.mul continuous_const)
  have hmod : Continuous fun x : F => (modulus x : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  refine hI.of_isClosed_subset (isClosed_le hmod continuous_const) ?_
  intro x hx
  refine ⟨x * (u : F), ?_, by simp⟩
  have hmu : (modulus (u : F) : ℝ) = ((residueCard F : ℝ) ^ k)⁻¹ := by
    rw [modulus_of_ne_zero u.ne_zero, hu, ord_unifUnit_zpow]
    push_cast
    rw [_root_.zpow_neg, zpow_natCast]
  have hx' : (modulus x : ℝ) ≤ R := hx
  have hpos : (0 : ℝ) < (residueCard F : ℝ) ^ k := by positivity
  apply (modulus_le_one_iff).1
  rw [modulus_mul, ← NNReal.coe_le_coe]
  push_cast
  rw [hmu, ← div_eq_mul_inv, div_le_one hpos]
  exact hx'.trans hk.le

theorem isCompact_shell {r : ℝ} (hr : 0 < r) (R : ℝ) :
    IsCompact {τ : Fˣ | r ≤ (modulus (τ : F) : ℝ) ∧ (modulus (τ : F) : ℝ) ≤ R} := by
  have hmod : Continuous fun x : F => (modulus x : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  have hK : IsCompact {x : F | r ≤ (modulus x : ℝ) ∧ (modulus x : ℝ) ≤ R} :=
    (isCompact_modulus_le R).of_isClosed_subset
      ((isClosed_le continuous_const hmod).inter (isClosed_le hmod continuous_const))
      fun x hx => hx.2
  have hsub : {x : F | r ≤ (modulus x : ℝ) ∧ (modulus x : ℝ) ≤ R} ⊆ Set.range (Units.val : Fˣ → F) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := hx.1
      simp at this
      linarith
    exact ⟨Units.mk0 x hx0, rfl⟩
  exact ((isOpenEmbedding_units_val (K := F)).isInducing.isCompact_preimage_iff hsub).2 hK

theorem continuous_mp (z : ℂ) : Continuous fun τ : Fˣ => mp τ z := by
  have hm : Continuous fun τ : Fˣ => (((modulus (τ : F) : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))
  exact hm.cpow continuous_const fun τ =>
    Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast modulus_pos τ.ne_zero)

end Compact

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]



end GlobalTheory.CompanionTheory.LFDual.ZRho
