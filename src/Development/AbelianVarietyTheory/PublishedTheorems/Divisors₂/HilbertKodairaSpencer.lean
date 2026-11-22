module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsRapoportOfBasis

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

end GlobalTheory.RealMult

namespace GlobalTheory.Published

end GlobalTheory.Published
