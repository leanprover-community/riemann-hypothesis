module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open GlobalTheory.DeRham (push push_comp push_congr push_id push_mul)
open GlobalTheory.AbDual (isMonHom_one push_one)

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPrimeTo

section Push

variable {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)

end Push

end GlobalTheory.PolPrimeTo
