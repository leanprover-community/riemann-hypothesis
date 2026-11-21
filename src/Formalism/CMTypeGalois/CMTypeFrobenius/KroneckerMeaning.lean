import Mathlib
import Formalism.CMTypeGalois.StatementGroup

namespace Formalism.Q3

open ZMod



lemma sgn_one : sgn 1 = 1 := by
  unfold sgn; rw [if_pos rfl]

lemma cc_not_mem (a b : Gal3) (j : Fin 3) (ha : a j = 1) (hb : b j = 1) :
    cc ∉ Subgroup.closure ({a, b} : Set Gal3) := by
  intro h
  have hle : Subgroup.closure ({a, b} : Set Gal3) ≤ (Pi.evalMonoidHom (fun _ : Fin 3 => ℤˣ) j).ker := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]; exact ha
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]; exact hb
  have := hle h
  rw [MonoidHom.mem_ker, Pi.evalMonoidHom_apply] at this
  have h' : (-1 : ℤˣ) = 1 := this
  exact absurd h' (by decide)

end Formalism.Q3
