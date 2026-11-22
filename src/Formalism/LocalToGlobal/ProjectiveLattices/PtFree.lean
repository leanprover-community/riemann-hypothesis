module

public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst

@[expose] public section

noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section One

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]

end One

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)

def algCls (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop := y.IsAlg

def valSet (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  Set.range (vAtV : PtV Xo c cls Unit (fun _ _ _ _ => True) la → Rul Xo c → EReal)

variable {Xo c cls}

variable (Xo c cls)

variable {Xo c cls}

end Formalism.L2.PjFree
