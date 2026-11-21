import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FrameExBor
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NormDiagEqNormBdiag

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.BorelChar



variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {l : Level H} {r : ℕ}






variable {Dw : Datum H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}


end GlobalTheory.BorelChar
