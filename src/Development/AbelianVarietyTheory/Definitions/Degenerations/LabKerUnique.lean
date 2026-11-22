module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical

namespace RealModel
open Inh

variable (B : Scheme.{0})

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

section More
variable {S : ThetaSys o Ω} (ρ : S.Real)

variable {ρ} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} {u : ρ.UTest p y₀}

end More

end RealModel
end GlobalTheory.ZH
end
