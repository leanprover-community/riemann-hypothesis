module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}

def GtTors (k : ℕ) {T : Over (Sp R)} (g : Out.GtPt D T) : Prop :=
  ∃ h : Out.GtPt D T, Out.GtPt.IsNsmul k g h ∧ h.IsZero

def unitGen {X Y : Scheme.{0}} (L : LB X) (z : Γ(Y, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top z

def TorusVal {T : Over (Sp R)} (g : Out.GtPt D T) (χ : D.X) (z : Γ(T.left, ⊤)ˣ) : Prop :=
  g.b = Out.DegPre.zeroT D T ∧ LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (unitGen D.P.L z)

end Points

section Formal

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
  {A : Out.PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def FormalEq (U : Out.UnifPre I D A G) {T : Over (Sp R)} (x : T ⟶ G) (g : Out.GtPt D.toPre T) : Prop :=
  ∀ e : ℕ,
    (Out.fstG I e T).left ≫ g.b.left =
        ((Over.pullback (Out.thick R I e)).map x).left ≫ (U.gt e).pG.left ∧
      ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _
        (LB.pullGen D.toPre.P.L _ _ (g.s χ) (Out.fstG I e T).left)
        (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ((Over.pullback (Out.thick R I e)).map x).left)

end Formal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Flat

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

end Flat

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
