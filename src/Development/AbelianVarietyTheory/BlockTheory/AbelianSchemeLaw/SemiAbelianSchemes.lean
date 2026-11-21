import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes

open ReciprocityTheory.ChartRestriction.G.Semi

structure IsAbelianScheme {S : Scheme.{u}} (A : Over S) [GrpObj A] : Prop where
  smooth : Smooth A.hom
  proper : IsProper A.hom
  geometricallyConnected : GeometricallyConnected A.hom
  comm : IsCommMonObj A

structure IsShortExact {S : Scheme.{u}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    (i : T ⟶ G) (q : G ⟶ B) : Prop where
  isMonHom_i : IsMonHom i
  isMonHom_q : IsMonHom q
  isKernel : IsPullback i (toUnit T) q (η : 𝟙_ (Over S) ⟶ B)
  flat : Flat q.left
  surjective : Surjective q.left
  finitePresentation : LocallyOfFinitePresentation q.left

def IsTorusExtension {k : Type u} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] :
    Prop :=
  IsCommMonObj G ∧
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
      (B : Over (Spec (CommRingCat.of k))) (_ : GrpObj B)
      (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G) (q : G ⟶ B),
      IsAbelianScheme B ∧ IsShortExact i q

structure IsSemiAbelianScheme {S : Scheme.{u}} (G : Over S) [GrpObj G] : Prop where
  smooth : Smooth G.hom
  separated : IsSeparated G.hom
  locallyOfFiniteType : LocallyOfFiniteType G.hom
  quasiCompact : QuasiCompact G.hom
  comm : IsCommMonObj G
  geometricFibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
    IsTorusExtension ((Over.pullback s).obj G)

theorem isAbelianScheme_unit (S : Scheme.{u}) : IsAbelianScheme (𝟙_ (Over S)) where
  smooth := inferInstanceAs (Smooth (𝟙 S))
  proper := inferInstanceAs (IsProper (𝟙 S))
  geometricallyConnected := by
    change GeometricallyConnected (𝟙 S)
    refine ⟨fun K _ y Z fst snd h => ?_⟩
    have : IsIso snd := h.isIso_snd_of_isIso
    exact (Scheme.homeoOfIso (asIso snd)).symm.surjective.connectedSpace
      (Scheme.homeoOfIso (asIso snd)).symm.continuous
  comm := inferInstance

section SplitTorus

variable (X : Type u) [AddCommGroup X]




end SplitTorus

end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
