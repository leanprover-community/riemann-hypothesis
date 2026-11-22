module

public import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
public import Mathlib

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped ComplexOrder

namespace Formalism.L2.Geo

section Abs

variable {K : Type} [Field K] [NumberField K]

end Abs

namespace FormsPkg

variable {D : D7} {G : DV.Geo D.what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
  {algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
  (P : FormsPkg D G NW CompW algW PtY)

variable {j : ℕ}

section Gauss

variable (la : HeightOneSpectrum (𝓞 P.KO)) (y : P.Pt j la)

end Gauss

end FormsPkg

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

attribute [instance] FormsKPkg.grpHb FormsKPkg.act FormsKPkg.cmpKFin

namespace FormsKPkg

variable {F : ShimFam D G Lev} (P : FormsKPkg F)

end FormsKPkg

end Formalism.L2.Geo
