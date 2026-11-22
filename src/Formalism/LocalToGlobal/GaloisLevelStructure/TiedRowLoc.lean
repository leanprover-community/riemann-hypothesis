module

public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedGal
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
public import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsRowLoc

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain

namespace Formalism.L2

structure RowFrame (D : D7) where
  rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r
  inj : ∀ σ σ', (rep σ).Iso (rep σ') → σ = σ'

variable {D : D7} {lp : LPTiedPlaceholder D} {F : RowFrame D}

end Formalism.L2
