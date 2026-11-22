module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowSt

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section Pow

variable {S : Scheme.{0}} {A' A : Over S} [GrpObj A'] [GrpObj A] {n : ℕ}

variable [IsCommMonObj A'] [IsCommMonObj A]

end Pow

end Formalism.MainNotions.ModuliIntegralCharts.H1
