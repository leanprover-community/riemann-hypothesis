module

public import Mathlib
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SubsingletonOfLeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Per

section Defs

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Sp R))

variable {D T}

variable {C : Type} [NormedField C] [IsUltrametricDist C]

end Defs

section Rel

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

variable {g : R →+* V}

end Rel

section Main

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {D : DegPre R} {g : R →+* V}

end Main

section Exist

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegPre R}
  {C : Type} [NormedField C] [IsUltrametricDist C]

end Exist

section Point

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

end Point

end GlobalTheory.LocM.Per
