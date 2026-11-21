import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import BuildAid.ForwardExisting

section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SmoothCut

theorem exists_smooth_antitone_cut :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, deriv χ x ≤ 0) ∧ (∀ x, 0 ≤ χ x) ∧
      (∀ x, x ≤ 0 → χ x = 1) ∧ ∀ x, 1 ≤ x → χ x = 0 := by
  have hanti : Antitone (fun x : ℝ => Real.smoothTransition (1 - x)) := fun a b hab =>
    Real.smoothTransition.monotone (by linarith)
  refine ⟨fun x => Real.smoothTransition (1 - x),
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id), ?_,
    fun x => Real.smoothTransition.nonneg _,
    fun x hx => Real.smoothTransition.one_of_one_le (by linarith),
    fun x hx => Real.smoothTransition.zero_of_nonpos (by linarith)⟩
  intro x
  have hneg : Monotone (fun x : ℝ => -Real.smoothTransition (1 - x)) := fun a b hab =>
    neg_le_neg (hanti hab)
  have h := hneg.deriv_nonneg (x := x)
  rw [deriv.fun_neg] at h
  linarith

end GlobalTheory.CompanionTheory.SmoothCut
end

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_monotone_cutoff_exists : ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, deriv χ x ≤ 0) ∧ (∀ x, 0 ≤ χ x) ∧ (∀ x, x ≤ 0 → χ x = 1) ∧ ∀ x, 1 ≤ x → χ x = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut
