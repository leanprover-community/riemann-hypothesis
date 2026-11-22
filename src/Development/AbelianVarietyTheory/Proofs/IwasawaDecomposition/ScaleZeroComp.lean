module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFreeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocomm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Pad.HTBound

section Divide

variable {O : Type} [CommRing O] [IsDomain O]

end Divide

section Points

variable {X : Scheme.{0}} {O : Type} [CommRing O] (x : Sp O ⟶ X) {G : Over X} [GrpObj G]

variable {R : Type} [CommRing R] [Algebra O R]

variable {x} {y : overAt x (DualNumber R) ⟶ G}

end Points

section Rep

open Algebra.TensorProduct

variable {X : Scheme.{0}} {O : Type} [CommRing O] {x : Sp O ⟶ X} {G : Over X} [GrpObj G] {q : ℕ}
  {A : Type} [CommRing A] [Algebra O A] {u : overAt x A ⟶ G}

variable (h : Rep q u) {B B' : Type} [CommRing B] [Algebra O B] [CommRing B'] [Algebra O B']
include h

variable [IsCommMonObj G] [Module.Finite O A]

end Rep

section Char

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {O : Type} [CommRing O] {x : Sp O ⟶ X} {q : ℕ} {A : Type} [CommRing A] [Algebra O A]
  [Module.Finite O A] {u : overAt x A ⟶ t.G}

end Char

end GlobalTheory.ShFam.Pad.HTBound
