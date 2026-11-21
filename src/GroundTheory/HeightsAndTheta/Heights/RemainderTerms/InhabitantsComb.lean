import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

def inhNumberingFun (p : youngCells (![2, 1] : Fin 2 → ℕ)) : Fin 3 :=
  if p.1 = (0, 0) then 0 else if p.1 = (0, 1) then 1 else 2

theorem inhNumberingFun_bijective : Function.Bijective inhNumberingFun := by
  unfold inhNumberingFun
  decide

theorem inh_card_two_one : (youngCells (![2, 1] : Fin 2 → ℕ)).card = 3 := by decide

def inhNumbering :
    youngCells (![2, 1] : Fin 2 → ℕ) ≃ Fin (youngCells (![2, 1] : Fin 2 → ℕ)).card :=
  (Equiv.ofBijective _ inhNumberingFun_bijective).trans (finCongr inh_card_two_one.symm)






end

end GroundTheory.Heights₂.Heights.RestTerms
