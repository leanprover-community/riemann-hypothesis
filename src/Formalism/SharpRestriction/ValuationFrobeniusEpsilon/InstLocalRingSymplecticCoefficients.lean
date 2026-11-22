module

public import Formalism.ConjugateSelfDual.StatementRest
public import Mathlib
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LiftInvariantsFinrankEq
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

open NumberField Matrix

namespace Formalism.BasicNotions

namespace TV

section VKdefs

open Formalism.ConjugateSelfDual Filter

attribute [instance] KatoSys.instE KatoSys.instEalg KatoSys.instEfd KatoSys.instLam KatoSys.instLamAlg
  KatoSys.instAddCommGroupH1Alt KatoSys.instModuleH1Alt KatoSys.instAddCommGroupH2Alt KatoSys.instModuleH2Alt

end VKdefs

section ShaDefs

variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

end ShaDefs

section univ

open IsLocalRing

end univ

end TV

namespace VH

open IsDedekindDomain

attribute [instance] HidaSetting.hl HidaSetting.instO HidaSetting.instOdom HidaSetting.instOloc HidaSetting.instOalg
  HidaSetting.instOfin HidaSetting.instOQ HidaSetting.instL HidaSetting.instLnf HidaSetting.instLQ HidaSetting.instLac HidaSetting.instOdvr HidaSetting.instTT
  HidaSetting.instVl

namespace HidaSetting

variable (s : HidaSetting)

end HidaSetting

attribute [instance] Sys.instMf Sys.instMfL Sys.instT Sys.instTL

namespace Sys

variable {s : HidaSetting} (H : Sys s)

end Sys

namespace HidaSetting

variable (s : HidaSetting)

end HidaSetting

attribute [instance] UniversalOrdinaryDeterminantRing.instB UniversalOrdinaryDeterminantRing.instBL

namespace HidaSetting

variable (s : HidaSetting)

end HidaSetting

namespace Sys

variable {s : HidaSetting} (H : Sys s)

end Sys

attribute [instance] TWMod.instM TWMod.instMD TWMod.instTp TWMod.instTpL

end VH

namespace VH

open IsDedekindDomain

end VH

namespace VH

end VH

namespace VH

open IsDedekindDomain

end VH

attribute [instance] VData.instHq VData.instMsA VData.instMsM
attribute [instance] VData.instTauA VData.instTauM VData.instScA VData.instScM VData.instMA VData.instMM
attribute [instance] VDataX.instRing VDataX.instDomain VDataX.instLocal VDataX.instAlg VDataX.instFin
  VDataX.instUnitaryDeformationRing VDataX.instS3alg VDataX.instS3gr
  VDataX.instSS4 VDataX.instSS4alg VDataX.instSS4gr VDataX.instAddCommGroupSelmer VDataX.instModuleSelmer VData.instDdRa VData.instDdRm

attribute [instance] VDataX.instS3hat VDataX.instS3hatL VDataX.instS3hatA VDataX.instCommRingSymplecticCoefficients VDataX.instDomainSymplecticCoefficients VDataX.instLocalRingSymplecticCoefficients
  VDataX.instAlgebraSymplecticCoefficients VDataX.instSS4hat VDataX.instSS4hatL VDataX.instSS4hatA

namespace VData

variable {D : D7} (V : VData D)

end VData

namespace TV

open Formalism.ConjugateSelfDual Filter Polynomial IsDedekindDomain

end TV

namespace VData

variable {D : D7} (V : VData D)

end VData

end Formalism.BasicNotions

namespace Formalism.BasicNotions

end Formalism.BasicNotions

namespace Formalism.BasicNotions

end Formalism.BasicNotions
