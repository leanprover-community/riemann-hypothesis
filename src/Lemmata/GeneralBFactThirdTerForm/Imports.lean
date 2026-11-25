module

import Lemmata.GeneralBFactAltForm.Imports
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_third_ter_form

theorem goal1 :
  ∀ {K W : Type} [inst : Field.{0} K] [NumberField.{0} K] [inst_2 : AddCommGroup.{0} W] [inst_3 : Module.{0, 0} K W]
  [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) W]
  [inst_5 : IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K W]
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) W) [hΛ : Submodule.IsFullLattice.{0, 0, 0} K Λ] (v : W),
  Exists.{1} fun (s : NumberField.RingOfIntegers.{0} K) ↦
    And (Ne.{1} s 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} s v)) := by
  intro K W _ _ _ _ _ _ Λ hΛ v
  exact Bl.general_b_fact_alt_form.goal1 (F := K) Λ (x := v) (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)

end Bl.general_b_fact_third_ter_form
