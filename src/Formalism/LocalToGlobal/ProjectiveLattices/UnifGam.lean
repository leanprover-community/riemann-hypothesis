module

public import Formalism.LocalToGlobal.ProjectiveLattices.PerFrLact

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

end Lat

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

end Herm

section Gam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {r : ℕ}

end Gam

end Formalism.L2.Pj
