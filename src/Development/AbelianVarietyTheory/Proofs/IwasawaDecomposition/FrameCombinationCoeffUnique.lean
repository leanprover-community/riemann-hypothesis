module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.Proof.frame_combination_coeff_unique

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

variable {X : Scheme.{0}} {t : SAB H X} {k : Type} [CommRing k] {x : Sp k ⟶ X}

end

end GlobalTheory.Proof.frame_combination_coeff_unique
