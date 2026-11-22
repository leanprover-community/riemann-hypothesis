module

public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
  (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1)

def LevelPb (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∃ l : Level (hostOfRecord D), (l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) ∧
    l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

end Formalism.L2.Pj
