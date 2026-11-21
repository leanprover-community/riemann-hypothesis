import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.PositiveBaseCharge

theorem q0_pos_allSt : AllSt fun _ _ _ _ _ _ x => 0 < GlobalTheory.ChiGrid.q0 (Dof x) :=
  StepW.of_all fun _ _ _ _ _ _ _ _ _ x => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (Dof x)).1.pos

end GlobalTheory.HeightCounting.Up.PositiveBaseCharge
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leastSplitAuxiliaryPrime_pos_allStates : AllSt fun _ _ _ _ _ _ x => 0 < GlobalTheory.ChiGrid.q0 (Dof x) := by
  atlas_forward_decl GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt
