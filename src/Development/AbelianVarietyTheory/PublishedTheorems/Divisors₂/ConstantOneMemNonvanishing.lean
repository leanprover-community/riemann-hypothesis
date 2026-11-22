module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Matrix
open GlobalTheory.HermFrame

namespace GlobalTheory.CxForm

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ}

attribute [instance] ArRing.ring ArRing.alg ArRing.graded

end GlobalTheory.CxForm

namespace GlobalTheory.Published

open GlobalTheory.CxForm

end GlobalTheory.Published

namespace GlobalTheory.CxForm.ArRing

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt MvPolynomial

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {B : BottChern} {h : IsRegVar p D}
  (R : ArRing B h) (L : HermLB p) {ι : Type} [Fintype ι]

end GlobalTheory.CxForm.ArRing
