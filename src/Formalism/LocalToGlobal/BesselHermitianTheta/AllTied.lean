import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Formalism.LocalToGlobal.HermitianColumns.HermCols
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedDef
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedMY
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedLocW

section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Theta

theorem VolTieG.hermVolTied {D : D7} (h : VolTieG D) : Formalism.L2.Herm.VolumeCompatible D := by
  intro W P Q hs hsig μ hμ 𝓕 h𝓕
  exact ((h.volTie W P Q hs hsig).2 μ hμ).2 𝓕 h𝓕

end Formalism.L2.Theta

end
end

section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Theta

structure AllTied (D : D7) (X : ThetaX D) (A : TH.ProvA) where

  T : ThetaTied D X

  sm : ThetaSmoothnessCondition T

  ty : TypTied T

  W : WeilTied D X T
  unr : WeilUnramifiedCondition W

  kf : KfinTied W

  phiUp : PhiYupTied W

  B : BesselTied D X T W

  real : RealTied D

  prov : ProvisionCompatibility D A

end Formalism.L2.Theta

end
end
