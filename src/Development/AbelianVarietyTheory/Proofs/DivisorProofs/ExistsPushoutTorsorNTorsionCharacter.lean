import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorSectionEveryPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDifferenceOneCochain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAdditionTwoPointFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocOfIsSecDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAddOfIsSecDiffIsSecAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiEqOfTorsion

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem exists_pushout_torsor : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), (n : R) = 0 → HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → chi n g D x = b D x := by
  intro R _ A _ _ n hn hR b hb
  let S : SecFam A := fun D _ _ x ↦ Classical.choose (GlobalTheory.T.exists_pushoutTorsorSection_every_point R A n hR b hb D x)
  have hS : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x) :=
    fun D _ _ x ↦ Classical.choose_spec (GlobalTheory.T.exists_pushoutTorsorSection_every_point R A n hR b hb D x)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionDifference_one_cochain R A n hR b hb S hS
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_sectionAddition_two_point_function R A n hR b hb S hS
  exact ⟨u, g, isCoc_of_isSecDiff R A n hR b hb S hS u hu,
    isAdd_of_isSecDiff_isSecAdd R A n hR b hb S hS u g hu hg,
    chi_eq_of_torsion R A n hn hR b hb S hS g hg⟩

end GlobalTheory.PtExt
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pushout_torsor_nTorsion_character : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), (n : R) = 0 → HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → chi n g D x = b D x := by
  atlas_forward_decl GlobalTheory.PtExt.exists_pushout_torsor
