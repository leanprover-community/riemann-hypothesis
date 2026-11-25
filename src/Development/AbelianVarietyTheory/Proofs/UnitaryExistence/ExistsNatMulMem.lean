module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ExistsNatSmulMem
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GlobalTheory.NatMulMemUnitaryExistence

open NumberField

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  apply PI.WAU.exists_nat_smul_mem <;> assumption

alias target := _root_.GlobalTheory.NatMulMemUnitaryExistence.main

end GlobalTheory.NatMulMemUnitaryExistence
