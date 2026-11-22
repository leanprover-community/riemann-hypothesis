module

public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open IsDedekindDomain NumberField HeightOneSpectrum Filter
open scoped WithZero Topology

namespace LocFldPf

section Compl

variable {R : Type} [CommRing R] [IsDedekindDomain R] {L : Type} [Field L] [Algebra R L]
  [IsFractionRing R L] (w : HeightOneSpectrum R)

end Compl

end LocFldPf

section Cor

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end Cor

end Formalism.L2.Pj
