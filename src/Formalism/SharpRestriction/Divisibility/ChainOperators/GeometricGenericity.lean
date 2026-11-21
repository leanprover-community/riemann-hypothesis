import Mathlib
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.LocalToGlobal.NormalizedHeckeFactors.UCardChoose
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GeoProdPow

namespace ConditionalKappaBounds.G2

open Formalism.BasicNotions Formalism.MainNotions

def UCard (D : D7) : Prop :=
  (Nat.card D.nexp.U : ℝ) = ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ^ (D.R.f * (D.R.r * (D.R.r - 1) / 2))




end ConditionalKappaBounds.G2

namespace Formalism.MainNotions.DIV.GeometricGenericity

open Formalism.BasicNotions Formalism.MainNotions


end Formalism.MainNotions.DIV.GeometricGenericity
