import Formalism.LocalToGlobal.GlobalTheory.GL4.PLinks
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

def BranchingIntegralAt (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n) (T : ℕ) (G : GL (Fin (n + 1)) ℂ) : Prop :=
    ∃ P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ,
      (∀ f ∈ delSq ℂ (n + 1) lt, P f ∈ delSq ℂ n sg) ∧
      (∃ f ∈ delSq ℂ (n + 1) lt, P f ≠ 0) ∧
      (∀ f ∈ delSq ℤ (n + 1) lt, ∃ g ∈ delSq ℤ n sg,
        P (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
      (∀ (g : GL (Fin n) ℂ) (H : GL (Fin (n + 1)) ℂ),
        (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = blockMat (g : Matrix (Fin n) (Fin n) ℂ) →
        ∀ f ∈ delSq ℂ (n + 1) lt, P (sqAct ℂ (n + 1) lt H f) = sqAct ℂ n sg g (P f)) ∧
      (∀ f ∈ delSq ℂ (n + 1) lt,
        (normFock sg (P f) (P f)).re ≤
          Real.exp (-(degP lt sg : ℝ) * Real.log T) *
            ((((Formalism.BranchingDeterminantCap.cCap lt.w sg.w : ℤ) : ℝ) ^ 2) * dimV lt.w) * normTil lt G f)

def BranchingIntegral : Prop :=
  ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n), Interlace lt sg →
    ∀ (T : ℕ), 0 < T →
    ∀ (G : GL (Fin (n + 1)) ℂ), (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T → BranchingIntegralAt n lt sg T G

def BranchingIntegralNormalised : Prop :=
  ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n), lt.w (Fin.last n) = 0 → Interlace lt sg →
    ∀ (T : ℕ), 0 < T →
    ∀ (G : GL (Fin (n + 1)) ℂ), (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T → BranchingIntegralAt n lt sg T G




theorem spread_eq {n : ℕ} (lt : DomWeight (n + 1)) :
    lt.spread = lt.w 0 - lt.w (Fin.last n) + ((n : ℤ) + 1) := by
  unfold DomWeight.spread
  rw [dif_pos (Nat.succ_pos n)]
  have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [this]
  push_cast
  rfl




def shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) : DomWeight N where
  w := fun i => lam.w i + c
  anti := fun i j h => by have := lam.anti h; simp only; omega







theorem detPow_add (R : Type) [CommRing R] {N : ℕ} (g : GL (Fin N) R) (a b : ℤ) :
    detPow R N g (a + b) = detPow R N g a * detPow R N g b := by
  unfold detPow
  rw [zpow_add, Units.val_mul]



theorem det_blockMat {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : (blockMat g).det = g.det := by
  unfold blockMat
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]












end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
