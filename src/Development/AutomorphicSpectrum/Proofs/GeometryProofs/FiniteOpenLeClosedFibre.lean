import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.ValAtRestrict
import BuildAid.ForwardExisting

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem isFinite_open_le_of_closedFibre_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' :=
  @PositivityTheory.HtPt.Unc.finite_le

end GlobalTheory.CompanionTheory.Ar.BT
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_open_le_closed_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.BT.isFinite_open_le_of_closedFibre_le
