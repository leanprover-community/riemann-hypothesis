module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Sym

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

variable {G}

variable (G)

variable {G}

end Sym

section Iso

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G']
  [GrpObj G] [IsCommMonObj G]

end Iso

section Triv

variable {S : Scheme.{0}} {H G : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj G] [IsCommMonObj G]

variable {B : Over S} [GrpObj B] [IsCommMonObj B]

end Triv

section Pairing

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}
  (c : CubicalStr G L)

end Pairing

section Torus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

def charV (χ : X) {T : Over S} (z : T.left) (t : T ⟶ splitTorus S X) : (T.left.presheaf.stalk z)ˣ :=
  gm t.left z ⊤ (charUnit S X χ)

variable {B : Over S} [GrpObj B]

end Torus

section Examples

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
