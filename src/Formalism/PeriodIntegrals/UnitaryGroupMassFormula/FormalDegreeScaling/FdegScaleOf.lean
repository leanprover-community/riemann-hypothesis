import Formalism.PeriodIntegrals.FdegScale

noncomputable section

namespace PI.UnitaryGroupMassFormula.FdegScale

open PI PI.UpqRep MeasureTheory Finset
open scoped InnerProductSpace

lemma fdegHC_pos {n : ℕ} {lam : Fin n → ℝ} (h : IsHCParam lam) : 0 < fdegHC lam := by
  unfold fdegHC
  apply div_pos
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (h.1.injective.ne (ne_of_lt hab)))
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    have h' : (a : ℕ) < (b : ℕ) := hab
    rw [sub_pos]
    exact_mod_cast h'



end PI.UnitaryGroupMassFormula.FdegScale
