import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import BuildAid.ForwardExisting

section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem disc_pow_mul_slash : ∀ (w : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)), ((fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * f (γ • τ) := by
  intro w f γ
  funext τ
  rw [ModularForm.SL_slash_apply]
  have hd : (UpperHalfPlane.denom γ τ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [ReciprocityTheory.ChartRestriction.L1.DD_smul, mul_pow, ← pow_mul]
  rw [zpow_neg, zpow_natCast]
  field_simp

end GlobalTheory
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul : ∀ (w : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)), ((fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * f (γ • τ) := by
  atlas_forward_decl GlobalTheory.disc_pow_mul_slash
