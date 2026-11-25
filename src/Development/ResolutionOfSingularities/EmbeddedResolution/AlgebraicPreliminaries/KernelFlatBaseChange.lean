module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace FunctorialResolution.EmbeddedResolution

theorem quasiCompact_of_isPullback {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g) [QuasiCompact h] :
    QuasiCompact h' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) H ‹QuasiCompact h›

theorem ker_eq_comap_ker_of_isPullback_of_flat {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g)
    [QuasiCompact h] [QuasiCompact h'] [AlgebraicGeometry.Flat g] :
    h'.ker = h.ker.comap g :=
  GlobalTheory.ker_eq_comap_of_flat h H.flip

end FunctorialResolution.EmbeddedResolution
