module

public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifGen
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Fam

section Genus

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Genus

section Rows

variable {D : D7}

end Rows

end Formalism.L2.Pj
