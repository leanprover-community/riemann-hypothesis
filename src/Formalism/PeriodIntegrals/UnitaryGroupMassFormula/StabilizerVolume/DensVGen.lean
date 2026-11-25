module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibFour
import Mathlib.Algebra.Order.Star.Real
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVGen

@[expose] public section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter
open scoped Pointwise

export PI.VolStabSW (IsLCcOn HasCOSub HasDens nonneg_of_setIntegral isOpen_inf_iInf exists_sub_osc
  cosApx cosApx_sub_mem cosApx_eq cosApx_lc)

namespace HasDens
export PI.VolStabSW.HasDens (sub const_mul le)
end HasDens

section Main

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]

theorem densApprox_lc (μ : Measure V) [IsFiniteMeasureOnCompacts μ] (f : V → Y) (ι : X → Y)
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] (U : Set V)
    (hU : IsOpen U) (hNA : HasCOSub V) : DensApprox (IsLCcOn U) μ f ι ν U := by
  apply PI.VolStabSW.densApprox_lc <;> assumption

end Main

end PI.VolStabS
