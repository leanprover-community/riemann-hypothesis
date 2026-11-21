import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open Matrix

namespace Formalism.L2.SG.RealObj

theorem Dl_diagonal {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE hl i) := by
  unfold Dl
  rw [dif_pos hl, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal]
  rfl




theorem famSc_last {n r : ℕ} (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    famSc sc e z (Fin.last r) = z := by
  simp [famSc, fam]

theorem trG_one {n : ℕ} {ε : Fin n → Bool} (γ : Formalism.REAL.UJ ε) :
    trG (1 : Matrix (Fin n) (Fin n) ℂ) 1 γ = Formalism.MainNotions.S.uMat γ := by
  simp only [trG, one_mul, mul_one]

example : Formalism.L2.SG.DataInst.signAux (K := ℤ) 2 1 [(1, 5), (2, 7)] = [(1, 5), (2, 7)] := by decide

example : Formalism.L2.SG.DataInst.signAux (K := ℤ) 3 1 [(1, 5), (1, 6), (2, 7)] = [(1, -5), (1, 6), (2, 7)] := by decide

example : Formalism.L2.SG.DataInst.signAux (K := ℤ) 3 1 (Formalism.L2.SG.DataInst.signAux 3 1 [(1, 5), (1, 6), (2, 7)]) =
    [(1, 5), (1, 6), (2, 7)] := by decide

end Formalism.L2.SG.RealObj
