module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormZpowSubOneLe
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

namespace GlobalTheory.CloseToUnitNorm

theorem norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - (1 : C)‖ < (1 : ℝ)) (i : ℤ) : ‖u ^ i - (1 : C)‖ ≤ ‖u - (1 : C)‖ := by
  apply GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption

end GlobalTheory.CloseToUnitNorm
