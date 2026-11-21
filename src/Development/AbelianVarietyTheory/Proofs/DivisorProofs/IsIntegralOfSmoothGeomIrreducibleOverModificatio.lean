import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumInt

theorem isIntegral_of_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S),
    Smooth G.hom → GeometricallyIrreducible G.hom → Nonempty G.left → IsIntegral G.left := by
  intro R _ _ M G hsm hgi _
  haveI := M.integral
  haveI : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  haveI : IrreducibleSpace G.left := GeometricallyIrreducible.irreducibleSpace G.hom G.hom.isOpenMap
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.MumInt
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_smooth_geomIrreducible_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → GeometricallyIrreducible G.hom → Nonempty G.left → IsIntegral G.left := by
  atlas_forward_decl GlobalTheory.MumInt.isIntegral_of_smooth
