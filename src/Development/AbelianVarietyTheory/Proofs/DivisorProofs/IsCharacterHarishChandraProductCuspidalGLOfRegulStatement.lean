import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLIsCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegularStatement

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

open Polynomial SemidirectProduct in
open scoped Classical in

theorem _root_.GlobalTheory.Shin.isChar_J_of_reg : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ _root_.GlobalTheory.Shin.Reg (Nat.card F) p.1 p.2) → ∀ n, n = _root_.GlobalTheory.Shin.deg L → _root_.GlobalTheory.BI.IsChar ℂ ℂ (_root_.GlobalTheory.Shin.J θ L n) := by
  intro F _ _ θ hθ L
  induction L with
  | nil =>
    intro _ n _
    rw [_root_.GlobalTheory.Shin.J_nil]
    exact _root_.GlobalTheory.BI.isChar_one ℂ ℂ _
  | cons p L ih =>
    intro hL n hn
    rw [_root_.GlobalTheory.Shin.J_cons]
    have hp := hL p List.mem_cons_self
    refine _root_.GlobalTheory.Shin.HCChar.hc_isChar F _ _ n ?_ _ _
      (_root_.GlobalTheory.Shin.isChar_cusp_and_norm_of_reg F θ hθ p.1 p.2 hp.1 hp.2).1
      (ih (fun q hq => hL q (List.mem_cons_of_mem p hq)) _ rfl)
    rw [hn]
    simp [_root_.GlobalTheory.Shin.deg]

end GlobalTheory.Shin
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card F) p.1 p.2) → ∀ n, n = deg L → IsChar ℂ ℂ (J θ L n) := by
  first | (exact @GlobalTheory.Shin.isChar_J_of_reg) | (exact GlobalTheory.Shin.isChar_J_of_reg) | (intros; apply GlobalTheory.Shin.isChar_J_of_reg <;> assumption)
end
