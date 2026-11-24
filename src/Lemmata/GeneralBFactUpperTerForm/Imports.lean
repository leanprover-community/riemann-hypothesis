module

public import Mathlib.NumberTheory.Padics.Complex

@[expose] public section

namespace Bl.general_b_fact_upper_ter_form

theorem goal1 :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset.{0} ι) (g : ι → PadicAlgCl p) {C : Real},
  LE.le.{0} 0 C →
    (∀ (j : ι), Membership.mem.{0, 0} s j → LE.le.{0} (Norm.norm.{0} (g j)) C) →
      LE.le.{0} (Norm.norm.{0} (Finset.sum.{0, 0} s fun (j : ι) ↦ g j)) C := by
  intro p _ ι s g C hC h
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

end Bl.general_b_fact_upper_ter_form
