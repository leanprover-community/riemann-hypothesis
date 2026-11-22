module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField

namespace GlobalTheory.IwLevel

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}}

def htAct {s : S ⟶ Sp R} (o : Obj b N s) : Out.RingAct o.A D.O :=
  ⟨o.act.act, o.act.hom, o.act.one, o.act.mul, o.act.add⟩

@[simp] theorem htAct_act {s : S ⟶ Sp R} (o : Obj b N s) (c : D.O) : (htAct o).act c = o.act.act c := rfl

section Basic₂

end Basic₂

end GlobalTheory.IwLevel
