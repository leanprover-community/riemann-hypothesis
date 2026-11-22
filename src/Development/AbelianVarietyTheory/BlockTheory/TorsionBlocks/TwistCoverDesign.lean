module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR.Links
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)

variable {D : D7}

abbrev Place (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E)

def PrimeToAA (D : D7) (P : Place D) : Prop := FractionalIdeal.count D.host.E P D.host.AA = 0

end GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign
