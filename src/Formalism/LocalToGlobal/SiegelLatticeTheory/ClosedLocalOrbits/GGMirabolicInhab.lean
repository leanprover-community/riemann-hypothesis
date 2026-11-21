import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic

namespace Formalism.L2.SG.GGMirabolic.Inhab

open Formalism.L2.SG.GGMirabolic

noncomputable section

open Classical

def psi3 : AddChar (ZMod 3) ℂ := ZMod.stdAddChar







def u12 : GL (Fin 2) (ZMod 3) :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩







theorem cardU_pos (F : Type) [Field F] [Fintype F] (k : ℕ) : 0 < cardU F k := by
  unfold cardU
  have : Nonempty {x : GL (Fin k) F // IsUni k x} := ⟨⟨1, isUni_one⟩⟩
  exact Nat.card_pos


end

end Formalism.L2.SG.GGMirabolic.Inhab
