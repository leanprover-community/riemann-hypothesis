module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] {m : ℕ}

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

section Tan

variable {k : Type} [Field k] (x : Sp k ⟶ X) {m : ℕ}

variable {t x} {u u' u'' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)}

end Tan

section Norm

variable {t} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}

end Norm

end GlobalTheory.ShFam.Pad.Pull
