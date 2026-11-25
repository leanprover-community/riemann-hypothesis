module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

abbrev IxB (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

def eB (Dw : Datum H) : Fin (Fintype.card (IxB Dw)) ≃ IxB Dw := (Fintype.equivFin (IxB Dw)).symm

theorem hS (x : Sp S ⟶ Xo.X) :
    IsGrpPullback ((Over.pullback x).obj Xo.univ.t.G) Xo.univ.t.G x (pullback.fst Xo.univ.t.G.hom x) :=
  isGrpPullback_pullback Xo.univ.t.G x

def uS (y : FrPt Xo c S) (i : Fin (Fintype.card (IxB Dw))) : epsR S ⟶ (Over.pullback y.x).obj Xo.univ.t.G :=
  (push_surj (hS y.x) (tv (fullB y (eB Dw i)))).choose

end ReciprocityTheory.ChartRestriction.G.PullbackSections
