import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InertPrimesSquareNormOfGeneral

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minors

variable {K : Type} [Field K]

theorem sum_castLE {n l : ℕ} (hl : l ≤ n) (g : Fin n → K) (hg : ∀ k : Fin n, l ≤ k.val → g k = 0) :
    ∑ k, g k = ∑ k' : Fin l, g (Fin.castLE hl k') := by
  symm
  rw [show (∑ k' : Fin l, g (Fin.castLE hl k')) = ∑ k ∈ Finset.univ.map (Fin.castLEEmb hl), g k by
    rw [Finset.sum_map]; rfl]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  apply hg
  by_contra h
  push Not at h
  exact hk (Finset.mem_map.2 ⟨⟨k.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem submatrix_triple_mul_of_triangular {n l : ℕ} (hl : l ≤ n) (A Z B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ a b : Fin n, a < b → A a b = 0) (hB : ∀ a b : Fin n, b < a → B a b = 0) :
    (A * Z * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_castLE hl]
  · refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    rw [sum_castLE hl]
    intro k hk
    rw [hA _ _ (Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega)), zero_mul]
  · intro m hm
    rw [hB _ _ (Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega)), mul_zero]


end Minors

section Class

variable (D : D7) (u u' : D.what₂.Word)




end Class

end Formalism.MainNotions.GramProductBounds

end
