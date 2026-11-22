module

public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)
  (g' : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w))
  (hd' : ∀ u w h, (g' u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev setGat : D7 := { D with gat := g', gat_d := hd' }

open Formalism.L2.Herm

end Formalism.L2.G
