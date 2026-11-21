import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
import BuildAid.ForwardExisting

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem exists_isFinite_open_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  intro R _ _ X f _ _ _ _
  refine ⟨GlobalTheory.finitePart f, GlobalTheory.isFinite_finitePart f, fun x hx => ?_⟩
  exact GlobalTheory.mem_finitePart_of_eq_closedPoint f x hx

end GlobalTheory.CompanionTheory.Ar.BT
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselian_quasi_finite_finite_part : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian
