import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ} {ψ : AddChar (AF D.host.F) ℂ}

instance instTAGWO : IsTopologicalAddGroup (WO S T) := PHeisFC.tagWA T S

theorem eFin_idem : eFin D * eFin D = eFin D :=
  Prod.ext (show (0 : Ainf D.host.F) * 0 = 0 from mul_zero _) (show (1 : Af D.host.F) * 1 = 1 from mul_one _)

theorem symplOH_zero_right (x : WO S T) : symplOH S T x 0 = 0 := by
  have h := symplOH_add_right x (0 : WO S T) 0
  rw [add_zero] at h
  linear_combination -h



end Formalism.IndefR.Eqv

end
