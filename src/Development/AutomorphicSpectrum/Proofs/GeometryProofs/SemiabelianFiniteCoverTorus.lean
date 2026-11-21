import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupRelDimGeneric
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsPreimmersionToNormalization
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.StratumGenericTorsionPoints
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusKernelTrivialSpreadsOpen
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TwoTorsionPointsSpreadOpen
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TwoTorsionRankBound
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MaximalTorusInFibre
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FiniteSurjectiveImageOpen
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsSplitTorusExtension

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ggeo

theorem normalisation_finite_cover :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (L : Type) [Field L] (z : Sp L ⟶ Z), GlobalTheory.IsGenericPointHom z → ∀ (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L'], ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (j : Sp L' ⟶ Z'), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap L L') ≫ z :=
  @PositivityTheory.Xgn.stratum_finite_normal_cover

end GlobalTheory.CompanionTheory.Ggeo
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_normal_cover_generic_point : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (L : Type) [Field L] (z : Sp L ⟶ Z), GlobalTheory.IsGenericPointHom z → ∀ (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L'], ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (j : Sp L' ⟶ Z'), IsFinite π ∧ Surjective π ∧ IsNormalScheme Z' ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap L L') ≫ z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ggeo.normalisation_finite_cover
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.GenTors

theorem exists_finite_ext_torusExtension_two_torsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ ∃ (τ : TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (spMap (algebraMap L L') ≫ z) ⟶ G)), Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) :=
  PositivityTheory.Xgn.stratum_generic_torsion_points

end GlobalTheory.CompanionTheory.Ar.GenTors
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_two_torsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ ∃ (τ : TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (spMap (algebraMap L L') ≫ z) ⟶ G)), Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GenTors.exists_finite_ext_torusExtension_two_torsion
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.KerSpread

theorem injective_on_points_of_generic : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (G : Over Z') [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus Z' X ⟶ G) [IsMonHom u] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → (∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Z'), ⊤ ≤ a ⁻¹ᵁ V → ∀ t : Over.mk a ⟶ splitTorus Z' X, t ≫ u = 1 → t = 1 :=
  @PositivityTheory.Xgn.torus_kernel_trivial_spreads_open

end GlobalTheory.CompanionTheory.Ar.KerSpread
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_kernel_trivial_open : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (G : Over Z') [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus Z' X ⟶ G) [IsMonHom u] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → (∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Z'), ⊤ ≤ a ⁻¹ᵁ V → ∀ t : Over.mk a ⟶ splitTorus Z' X, t ≫ u = 1 → t = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.KerSpread.injective_on_points_of_generic
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem pts_spread : ∀ (Z' S : Scheme.{0}) [IsIntegral Z'] (c : Z' ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ (m : ℕ) (P : Fin m → (Over.mk (j ≫ c) ⟶ G)), Function.Injective P → (∀ i, P i ^ 2 = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ x ⁻¹ᵁ V → ∃ Q : Fin m → (Over.mk (x ≫ c) ⟶ G), Function.Injective Q ∧ ∀ i, Q i ^ 2 = 1 := by
  exact @PositivityTheory.Xgn.two_torsion_points_spread_open

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_torsion_spread_open : ∀ (Z' S : Scheme.{0}) [IsIntegral Z'] (c : Z' ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ (m : ℕ) (P : Fin m → (Over.mk (j ≫ c) ⟶ G)), Function.Injective P → (∀ i, P i ^ 2 = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ x ⁻¹ᵁ V → ∃ Q : Fin m → (Over.mk (x ≫ c) ⟶ G), Function.Injective Q ∧ ∀ i, Q i ^ 2 = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.pts_spread
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.RankBound

theorem rank_bound_of_points_of_order_two :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) :=
  @PositivityTheory.Xgn.two_torsion_rank_bound

end GlobalTheory.CompanionTheory.Ar.RankBound
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_torsion_card_bound : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.RankBound.rank_bound_of_points_of_order_two
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.MaxTorus

theorem kernel_eq_of_rank_le : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ :=
  @PositivityTheory.Xgn.maximal_torus_in_fibre

end GlobalTheory.CompanionTheory.Ar.MaxTorus
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_rank_bound : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.MaxTorus.kernel_eq_of_rank_le
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.Strat

theorem preimage_le_of_finite_surjective : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V :=
  PositivityTheory.Xgn.finite_surjective_image_open

end GlobalTheory.CompanionTheory.Ar.Strat
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_surjective_open_image : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Strat.preimage_le_of_finite_surjective
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem torus_extension_generic : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 :=
  @PositivityTheory.Xgn.exists_split_torus_extension

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_split_map : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.torus_extension_generic
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.StratOpen

theorem charZero_of_point {k : Type} [Field k] (x : Sp k ⟶ Sp ℚ) : CharZero k :=
  (RingHom.charZero_iff (Spec.preimage x).hom.injective).1 inferInstance

theorem core (hE : GlobalTheory.Published.SemiAbelianHomExtension) (Z : Scheme.{0}) [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
    (s : Z ⟶ Sp ℚ) (G : Over Z) [GrpObj G] (hG : IsSemiAbelian G) (g : ℕ) (hg : SmoothOfRelativeDimension g G.hom)
    (Z' : Scheme.{0}) [IsIntegral Z'] (π : Z' ⟶ Z) (hfin : IsFinite π) (hsurj : Surjective π) (hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z')
    (L' : Type) [Field L'] (j : Sp L' ⟶ Z') (hj : GlobalTheory.IsGenericPointHom j)
    (τ : TorusExtension ((Over.pullback (j ≫ π)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (j ≫ π) ⟶ G))
    (hPi : Function.Injective P) (hP2 : ∀ i, P i ^ 2 = 1)
    (hcount : letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) :
    ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  have hsm := hG.smooth
  have hsep := hG.separated
  have hG' : IsSemiAbelian ((Over.pullback π).obj G) := IsSemiAbelian.pullback π G hG
  have hsep' := hG'.separated
  have hLN : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian π
  have hCS : CompactSpace Z' := QuasiCompact.compactSpace_of_compactSpace π
  have hN' : AlgebraicGeometry.IsNoetherian Z' := {}
  let τ' : TorusExtension ((Over.pullback j).obj ((Over.pullback π).obj G)) := torusExtOfIso (pullCompIso j π G) τ
  letI := τ'.addCommGroup
  haveI := τ'.free
  haveI := τ'.finite
  obtain ⟨u, hu, hmono⟩ := GlobalTheory.T.torus_extension_split_map hE Z' hnorm ((Over.pullback π).obj G) hG' L' j hj τ'
  obtain ⟨V₁, hV₁, hC⟩ := GlobalTheory.T.torus_kernel_trivial_open Z' ((Over.pullback π).obj G) τ'.X u L' j hj hmono
  obtain ⟨V₂, hV₂, hD⟩ := GlobalTheory.T.two_torsion_spread_open Z' Z π G L' j hj m P hPi hP2
  have hVne : ((V₁ ⊓ V₂ : Z'.Opens) : Set Z').Nonempty :=
    nonempty_preirreducible_inter V₁.isOpen V₂.isOpen hV₁ hV₂
  obtain ⟨U, hU, hUV⟩ := GlobalTheory.T.finite_surjective_open_image Z Z' π hfin hsurj (V₁ ⊓ V₂) hVne
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd hcount.symm (by simp)
    · exact h
  refine ⟨Z', inferInstance, π, (Over.pullback π).obj G, inferInstance, pullback.fst G.hom π, τ'.X, τ'.addCommGroup, τ'.free, τ'.finite, u, U, hfin, hsurj, hnorm, isGrpPullback_pullback G π, hu, hU, ?_⟩
  intro k _ x hx
  have hxV : ∀ W : Z'.Opens, V₁ ⊓ V₂ ≤ W → ⊤ ≤ x ⁻¹ᵁ W := fun W hW y _ => hW (hUV (hx trivial))
  have mono : ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' τ'.X), t ≫ u = 1 → t = 1 := by
    intro A _ g t ht
    refine hC A (spMap g ≫ x) (fun y _ => ?_) t ht
    have h1 := hxV V₁ inf_le_left (show (spMap g) y ∈ (⊤ : (Sp k).Opens) from trivial)
    simpa using h1
  refine ⟨mono, ?_⟩
  intro Gk _ ψ hψ τk
  letI := τk.grpB
  letI := τk.addCommGroup
  haveI := τk.free
  haveI := τk.finite
  obtain ⟨Q, hQi, hQ2⟩ := hD k x (hxV V₂ inf_le_right)
  have h2 : ((2 : ℕ) : k) ≠ 0 := by
    haveI : CharZero k := charZero_of_point (x ≫ π ≫ s)
    exact Nat.cast_ne_zero.2 two_ne_zero
  have hle := GlobalTheory.T.two_torsion_card_bound Z G hG g hg k h2 (x ≫ π) Gk (ψ ≫ pullback.fst G.hom π) (hψ.comp (isGrpPullback_pullback G π)) τk m Q hQi hQ2
  have hrk : Module.finrank ℤ τk.X ≤ Module.finrank ℤ τ'.X := by
    have h3 : m * 2 ^ Module.finrank ℤ τk.X ≤ m * 2 ^ Module.finrank ℤ τ'.X := hle.trans hcount.ge
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (Nat.le_of_mul_le_mul_left h3 hm)
  intro A _ gg p
  exact GlobalTheory.T.torus_extension_rank_bound Z' ((Over.pullback π).obj G) τ'.X u k x mono Gk ψ hψ τk hrk A gg p

theorem strat_open : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (G : Over Z) [GrpObj G], IsSemiAbelian G → ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  intro hE Z _ s _ _ G _ hG
  have hLN : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have hCS : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  have hN : AlgebraicGeometry.IsNoetherian Z := {}
  have hsm := hG.smooth
  have hsep := hG.separated
  have hfq := hG.quasiCompact
  let z : Sp Z.functionField ⟶ Z := Z.fromSpecStalk (genericPoint Z)
  have hz : GlobalTheory.IsGenericPointHom z := GlobalTheory.IsGenericPointHom.fromSpecStalk Z
  haveI : CharZero Z.functionField := charZero_of_point (z ≫ s)
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim Z Z.functionField z G (fun q => by
    have : genPt z = genericPoint Z := by
      have := hz.range_eq
      have h2 : genPt z ∈ Set.range z := ⟨_, rfl⟩
      rw [this] at h2
      exact h2
    rw [this]
    exact genericPoint_specializes q)
  obtain ⟨L', _, _, hfd, hB⟩ := GlobalTheory.T.torus_extension_two_torsion Z G hG g hg Z.functionField z
  obtain ⟨Z', _, π, j, hfin, hsurj, hnorm, hj, hjπ⟩ := GlobalTheory.T.finite_normal_cover_generic_point Z s Z.functionField z hz L'
  rw [← hjπ] at hB
  obtain ⟨τ, m, P, hPi, hP2, hcount⟩ := hB
  exact core hE Z s G hG g hg Z' π hfin hsurj hnorm L' j hj τ m P hPi hP2 hcount

end GlobalTheory.CompanionTheory.Ar.StratOpen
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_finite_cover_torus : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (G : Over Z) [GrpObj G], IsSemiAbelian G → ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.StratOpen.strat_open
end
