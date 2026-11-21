import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.WeilBound.CoreStatements.HodgeTatePoints.ValAtRestrict
import BuildAid.ForwardExisting

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem regularAt_forall_iff_exists_section : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t :=
  PositivityTheory.HtPt.Unc.reg_iff

end GlobalTheory.CompanionTheory.Ar.BT
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_function_iff_section : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.BT.regularAt_forall_iff_exists_section
