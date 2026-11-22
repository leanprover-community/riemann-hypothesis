module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LevelIndexFourierCharacter
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace IsAuxiliarySplitSquarefreeLevel

variable {l : Level H} (a : IsAuxiliarySplitSquarefreeLevel l)

end IsAuxiliarySplitSquarefreeLevel

section Datum

variable {D : Datum H} {l : Level H} {a : IsAuxiliarySplitSquarefreeLevel l}

variable {F : Type} [Field F]

end Datum

section Cover

variable {D : Datum H} {l : Level H}

variable {Xo : Moduli D l} {c : Coeff l} {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a)

namespace Cover

end Cover

def fnAt {X : Scheme.{0}} {S : Type} [CommRing S] (y : Sp S ⟶ X) (f : Γ(X, ⊤)) : S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (y.appTop.hom f)

def basePt {Xo : Moduli D l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, sOf]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

end Cover

section Delta

variable {D : Datum H} {l : Level H}

namespace DeltaDatum

variable {Xo : Moduli D l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

end DeltaDatum

variable {Xo : Moduli D l} {c : Coeff l} {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a)

end Delta

section Trivial

variable {D : Datum H} {l : Level H}

end Trivial

end GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
