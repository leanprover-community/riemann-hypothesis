import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SecondCountableQuotients.QuotientMeasureUnitaryGroup

open MeasureTheory MeasureTheory.Measure Matrix

noncomputable section

namespace CompanionTheory.D.Upq.Quot

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula CompanionTheory.D.Upq.ModEx

variable {m : ℕ}


def oneM (m : ℕ) : MtM m := Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ)


theorem isMatGroup_one : IsMatGroup ({1} : Set (Matrix (Fin m) (Fin m) ℂ)) :=
  ⟨isClosed_singleton, rfl, fun a ha b hb => by
    rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]; simp, fun a ha => by
    rw [Set.mem_singleton_iff.1 ha]; simp⟩



end CompanionTheory.D.Upq.Quot

end
