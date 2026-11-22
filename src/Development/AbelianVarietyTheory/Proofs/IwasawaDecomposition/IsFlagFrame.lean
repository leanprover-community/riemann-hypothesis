module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

section Models

variable {F : Type} [Field F] [NumberField F]

end Models

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def IsTanBasis {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ} (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (e i)) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Sp (DualNumber S) ⟶ t.G.left),
    IsTanAtG t (spMap φ ≫ x) w →
      ∃! a : Fin g → S, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) a w

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end Tangent

end GlobalTheory.LineNorm
