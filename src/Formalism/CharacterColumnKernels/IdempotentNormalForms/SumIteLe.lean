import Formalism.CharacterColumnKernels.StatementNG
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalConcreteOf
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthQuotSmulRangeFree

open Finset

noncomputable section

namespace Formalism.NG

lemma sum_ite_le (t : ℕ) (vhE : ℕ∞) (Sha : ℕ → ℕ∞) :
    ∑ i ∈ range t, (if i + 1 = 1 then vhE else Sha (i + 1 - 1)) ≤
      vhE + ∑ e ∈ Ioo 0 t, Sha e := by
  rcases t with _ | n
  · simp
  · have hs : Ioo 0 (n + 1) = (range n).map ⟨(· + 1), add_left_injective 1⟩ := by
      ext e
      simp only [mem_Ioo, mem_map, mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro h
        exact ⟨e - 1, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨by omega, by omega⟩
    rw [hs, Finset.sum_map, Finset.sum_range_succ', add_comm]
    refine add_le_add (le_of_eq (if_pos rfl)) (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    show (if i + 1 + 1 = 1 then vhE else Sha (i + 1 + 1 - 1)) = Sha (i + 1)
    exact (if_neg (by omega)).trans (congrArg Sha (by omega))


theorem etaBound : LocalSubalgebraEtaBound := by
  intro O _ _ _ X _ T _ hsep V _ _ _ _ _ act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG haB
    B hB
  refine (congBoundGood O X T hsep V act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG
    haB).trans ?_
  refine sum_le_sum fun x hx => ?_
  gcongr
  exact hB x hx

end Formalism.NG
