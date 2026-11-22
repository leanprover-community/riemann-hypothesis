module

public import Mathlib

@[expose] public section

noncomputable section

namespace Formalism.ValuationGridEstimates

open Finset

def GridValuationBoundIndexed : Prop :=
  ∀ (W X S : Type) (m N : ℕ) (lam δ : W → ℝ) (ell : W → ℕ) (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
    (vr : W → Fin m × Fin m → ℝ) (vx : W → X → ℝ) (XX : Fin m × Fin m → Bool → Finset X)
    (ch : W → Bool) (dd hh yy : Fin m × Fin m → ℕ) (S0 : Finset S) (cc ee qq : S → ℕ)
    (vq : W → S → ℝ) (H : X → ℝ) (BN Bδ : ℝ) (W0 : Finset W),
    (∀ w, 0 ≤ lam w) → (∀ w, 0 ≤ δ w) → (∀ ij s l, 0 ≤ N0 ij s l) → (∀ w s, 0 ≤ vq w s) →
    (∀ w, (ell w).Prime) →
    (∀ (l : ℕ) (F : Finset W), (∀ w ∈ F, ell w = l) → ∑ w ∈ F, lam w ≤ Real.log l) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ W0, ∀ ij, vr w ij ≤ (∑ x ∈ XX ij (ch w), |vx w x|) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ + 6 * δ w +
      2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) →
    (∀ (x : X) (F : Finset W), ∑ w ∈ F, lam w * |vx w x| ≤ H x) →
    (∀ ij (s : ℤ) (P : Finset ℕ), (∀ l ∈ P, l.Prime) → ∑ l ∈ P, N0 ij s l * Real.log l ≤ BN) →
    (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
    (∀ s ∈ S0, ∀ F : Finset W, ∑ w ∈ F, lam w * vq w s ≤ Real.log (qq s)) →
    ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) +
      (m : ℝ) ^ 2 * (10 * N * BN + 2 * N + 6 * Bδ + 4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))

end Formalism.ValuationGridEstimates
