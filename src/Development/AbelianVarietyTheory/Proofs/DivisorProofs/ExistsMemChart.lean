module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.LB (toMod)
open Limits (pullback)

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

variable (p) in
def ratFibre : Scheme.{0} := pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))

namespace ratFibre

variable (p)

def fst : ratFibre p ⟶ X := pullback.fst _ _

def snd : ratFibre p ⟶ Sp ℚ := pullback.snd _ _

instance algebra : Algebra ℚ Γ(ratFibre p, ⊤) := algebraΓOfHom (snd p)

theorem isPullback : IsPullback (fst p) (snd p) (p ≫ spMap (Int.castRingHom k))
    (spMap (Int.castRingHom ℚ)) := IsPullback.of_hasPullback _ _

theorem strHom_eq : strHom ℚ (ratFibre p) = snd p := GlobalTheory.strHom_eq fun _ => rfl

end ratFibre

variable (p) in
def ratDeg (L : LB X) : ℤ := degOfRank ℚ (toMod (L.pull (ratFibre.fst p))) 1

end GlobalTheory
