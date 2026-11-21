import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DiscreteSeriesCoefficientsCuspidal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf

section
namespace GlobalTheory.Fc.S0

structure Hypotheses1 : Prop extends ArithmeticGeometryHyps where
  hilbertClassFieldJ : GlobalTheory.Published.HilbertClassFieldJ
  siegelWeilUnitarySchrodinger : GlobalTheory.Published.SiegelWeilUnitarySchrodinger
  localTateDualityK : Formalism.GaloisCohomology.LocalTateDualityK
  localEulerCharK : Formalism.GaloisCohomology.LocalEulerCharK
  localFinitenessK : Formalism.GaloisCohomology.LocalFinitenessK
  bhattScholzeIntegral : GlobalTheory.Published.BhattScholzeIntegral
  jacquetShalikaRigidity : GlobalTheory.Published.JacquetShalikaRigidity

end GlobalTheory.Fc.S0
end

section
namespace GlobalTheory.Fc.S0

structure Hypotheses2 : Prop extends Hypotheses1 where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  toHypothesesX : GlobalTheory.NRows.HypothesesX
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroWild' : GlobalTheory.Published.DepthZeroWild
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport

end GlobalTheory.Fc.S0
end
