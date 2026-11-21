import Formalism.HermitianCurvature.HermitianCurvatureProofs.CardInsertEmbedding

section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

namespace DeterminantReindex

open C2x2 CardInsertEmbedding


lemma det_reindex {m k : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (e ρ f : Fin k → Fin m) (τ : Equiv.Perm (Fin k))
    (h : ∀ t, e t = ρ (τ t)) :
    (M.submatrix e f).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (M.submatrix ρ f).det := by
  have : M.submatrix e f = (M.submatrix ρ f).submatrix τ id := by
    ext t s; simp [h]
  rw [this, Matrix.det_permute]

lemma sign_sq {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp

lemma sign_pm {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 ∨ ((Equiv.Perm.sign τ : ℤ) : ℂ) = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp



lemma prod_emb {m k n : ℕ} (hkn : k = n) (d : Fin m → ℂ) (e : Fin k → Fin m) (he : ∀ t, (e t).val = t.val) :
    ∏ t, d (e t) = ∏ j ∈ Finset.range n, (if h : j < m then d ⟨j, h⟩ else 1) := by
  subst hkn
  rw [← Fin.prod_univ_eq_prod_range (fun j => if h : j < m then d ⟨j, h⟩ else 1)]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  have hlt : t.val < m := by have := (e t).isLt; rw [he] at this; exact this
  rw [dif_pos hlt]; congr 1; exact Fin.ext (he t)

end DeterminantReindex

end Formalism.FourierDecayAlt.P
end

section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x2 CardInsertEmbedding DeterminantReindex




end Formalism.FourierDecayAlt.P
end
