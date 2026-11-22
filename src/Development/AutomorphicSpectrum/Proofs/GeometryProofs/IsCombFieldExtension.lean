module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.CombBase

theorem comp_list_prod {S : Scheme.{0}} {G A B : Over S} [GrpObj G] (g : A ⟶ B) (l : List (B ⟶ G)) :
    g ≫ l.prod = (l.map (g ≫ ·)).prod := by
  induction l with
  | nil => simp [comp_one]
  | cons a l ih => simp only [List.prod_cons, List.map_cons, comp_mul, ih]

end GlobalTheory.CompanionTheory.Ar.CombBase
