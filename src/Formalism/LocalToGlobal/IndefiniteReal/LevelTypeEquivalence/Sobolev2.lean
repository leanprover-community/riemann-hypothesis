import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobDer

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ} {ψ : AddChar (AF D.host.F) ℂ}

theorem psi_neg_mul (a : AF D.host.F) : ψ (-a) * ψ a = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]




end Formalism.IndefR.Eqv

end
