import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistGrid

noncomputable section

namespace GlobalTheory.HeightCounting.Up.GridModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.Links NumberField IsDedekindDomain GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar





section Guard

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR GlobalTheory.BigTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}



end Guard


variable (hL : GlobalTheory.Published.LocalLanglandsGL)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem settingsFormsExist_of_grid : SettingsFormsExistGrid hL → SettingsFormsExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem seriesExist_of_grid : SeriesExistGrid hL → SeriesExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem moduliPointsExist_of_grid : ModuliPointsExistGrid hL → SB2 hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

end GlobalTheory.HeightCounting.Up.GridModel

end
