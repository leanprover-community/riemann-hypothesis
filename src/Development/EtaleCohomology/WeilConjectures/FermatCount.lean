module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace IsProjOver)

namespace LateralTheory.EWeil

attribute [local instance] MvPolynomial.gradedAlgebra

section Defs
variable (l : ℕ) [Fact l.Prime] {k : Type} [Field k]

end Defs

end LateralTheory.EWeil

end
