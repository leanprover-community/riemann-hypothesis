import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerAntidiagonalExact

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

namespace CardInsertEmbedding

open C2x2


lemma card_ins {m n : ℕ} (b : Fin m) (hb : n < b.val) (hn : n ≤ m) :
    (insert b (C2.iSet m n)).card = n + 1 := by
  rw [Finset.card_insert_of_notMem, c2x3_iSet_card hn]
  simp [C2.iSet]; omega

lemma cemb {m n k : ℕ} (b : Fin m) (hb : n < b.val) (h : (insert b (C2.iSet m n)).card = k) (t : Fin k) :
    (insert b (C2.iSet m n)).orderEmbOfFin h t = if ht : t.val < n then ⟨t.val, by omega⟩ else b := by
  have hk : k = n + 1 := by rw [← h, card_ins b hb (by omega)]
  subst hk
  have := Finset.orderEmbOfFin_unique h
    (f := fun t : Fin (n + 1) => if ht : t.val < n then (⟨t.val, by omega⟩ : Fin m) else b)
    (fun t => by
      beta_reduce
      split_ifs with ht
      · exact Finset.mem_insert_of_mem (by simp only [C2.iSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact ht)
      · exact Finset.mem_insert_self _ _)
    (fun x y hxy => by
      beta_reduce
      rw [Fin.lt_def] at hxy
      split_ifs with h1 h2 h2
      · rw [Fin.lt_def]; exact hxy
      · rw [Fin.lt_def]; simp only; omega
      · omega
      · omega)
  rw [← this]

lemma sum_emb {m k : ℕ} (hkm : k ≤ m) (e : Fin k → Fin m) (he : ∀ t, (e t).val = t.val) (g : Fin m → ℂ)
    (hg : ∀ j : Fin m, k ≤ j.val → g j = 0) : ∑ j, g j = ∑ t, g (e t) := by
  rw [sum_fin_castLE hkm g hg]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  congr 1; exact Fin.ext (he t).symm




end CardInsertEmbedding

end Formalism.FourierDecayAlt.P
