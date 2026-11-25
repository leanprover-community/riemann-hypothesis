module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

@[expose] public section

namespace PositivityTheory.ThKF0

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM

theorem actsEx : GlobalTheory.ThK.ActsEx := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  exact ThKH.Locrep.exists_unique_local_actions hP.base.std (IsUWeilPair.isUSplitting hP.weil) v

end PositivityTheory.ThKF0
