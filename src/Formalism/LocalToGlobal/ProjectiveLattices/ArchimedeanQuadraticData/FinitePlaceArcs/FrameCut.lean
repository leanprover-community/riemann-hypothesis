module

public import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.FinAtOfStatement

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : D7} {T : Core D} {j : ℕ}

attribute [instance] DvrFrame.algR DvrFrame.algW

variable {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)]
  {d : ArcDatumAt T j K₁} {w : HeightOneSpectrum (𝓞 K₁)} {Z : FinSite K₁ w}

end Formalism.L2.Pj.QAt
