module

public import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open NumberField IntermediateField

noncomputable section

namespace Formalism.L2.DIV

open Formalism.L2.Host Formalism.DivisionValues

theorem exists_sqrt (m : ℤ) : ∃ x : Qb, x ∈ sqrts m := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (m : Qb) (n := 2) (by norm_num)
  exact ⟨x, hx⟩

end Formalism.L2.DIV
