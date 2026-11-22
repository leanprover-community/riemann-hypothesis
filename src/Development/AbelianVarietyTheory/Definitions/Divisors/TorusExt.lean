module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.LieHt

section Lat

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

variable (K' : Type) [Field K'] [NumberField K'] [Algebra K K']

end Lat

attribute [instance] SemiFib.grp

namespace SemiFib

variable {K : Type} [Field K] [NumberField K] (F : SemiFib K)

end SemiFib

end GlobalTheory.LieHt
end
