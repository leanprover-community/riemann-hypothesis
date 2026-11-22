module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

abbrev LevelMod (Dw : Datum H) (l : Level H) : Type :=
  Dw.La ⧸ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La))

abbrev LevelAut (Dw : Datum H) (l : Level H) : Type := LevelMod Dw l ≃ₗ[𝓞 E] LevelMod Dw l

variable {Xo : Moduli Dw l} {c : Coeff l}

section Laws

variable {G : Type} [Group G] (R : RelFam Xo c G)

variable {R}

end Laws

end General

variable {D : D7}

end GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms
