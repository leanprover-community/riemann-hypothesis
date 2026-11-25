module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCount
import Mathlib.Tactic.Linter.Style
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCountHolds

@[expose] public section

noncomputable section

namespace PI.VolStabSW
open PI.VolStabS (HenselCount)

open MeasureTheory Topology

section Hensel

variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

def hlev (Λ0 : AddSubgroup V) (H : AddSubgroup X) (G : V → X) (y : V) (h : X) : Set V :=
  {Z | Z ∈ Λ0 ∧ G (y + Z) - h ∈ H}

end Hensel

theorem henselCount_holds : HenselCount :=
  PI.VolStabS.henselCount_holds

end PI.VolStabSW
