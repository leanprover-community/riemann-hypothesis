import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterSymmR

namespace Formalism.IndefR.Eqv

open scoped ContDiff

section Sym

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem natCast_lt_inf' (m : ℕ) : (m : WithTop ℕ∞) < ∞ := by
  exact_mod_cast ENat.natCast_lt_top m

theorem two_le_inf : minSmoothness ℝ 2 ≤ ∞ := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact_mod_cast (natCast_lt_inf' 2).le






end Sym

end Formalism.IndefR.Eqv
