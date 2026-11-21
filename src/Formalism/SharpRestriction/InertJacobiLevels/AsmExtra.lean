import Formalism.SharpRestriction.InertJacobiLevels.AsmPoint
import Formalism.SharpRestriction.InertJacobiLevels.GaugeExists

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

structure RecExtra (D : D7) (ep : ℕ → ℕ) where
  shape : Shape D
  ties : Ties D
  X : DivX D
  mjH : ∀ j, Subsingleton (X.MjH j).V
  kapR : X.kapR D.what₂.embLL = 1
  ep_tie : ∀ u w hg, (D.gat u w hg).e = ep (D.what₂.places.resChar w)
  kap_def : DV.KapDef D
  duStar_def : ∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u
  Dstar_def : D.what₂.Dstar = StandardLattice.DstarD D
  cover : NTw.TwCover D.ntw
  le : LevErr D
  served : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ServedEmb D u w h
  gauge : GaugeExists D.host D.sp


end Formalism.MainNotions.Inhab

end
