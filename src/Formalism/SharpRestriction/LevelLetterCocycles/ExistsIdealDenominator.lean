module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.ExistsIdealDenominator

attribute [instance] PtGeo.acgBB PtGeo.acgSec PtGeo.modSec PtGeo.acgGt PtGeo.acgY PtGeo.acgYR PtGeo.modYR
  PtGeo.acgSecM PtGeo.modSecM PtGeo.finCo PtGeo.acgH PtGeo.modH PtGeo.acgGm PtGeo.modGm

namespace PtGeo

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [AddCommGroup Λ] {σ : Type} (X : PtGeo l Λ σ)

end PtGeo

variable (D : Formalism.BasicNotions.D7)

variable {D}

variable (X : Geo D)

end Formalism.MainNotions.ExistsIdealDenominator
