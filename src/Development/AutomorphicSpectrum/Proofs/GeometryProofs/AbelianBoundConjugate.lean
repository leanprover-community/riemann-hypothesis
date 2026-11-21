import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HeightBoundComplexConjugate

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem abBound_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M y) (C : ℝ) (z : Sp ℂ ⟶ X), AbBound t h C (spMap (starRingEnd ℂ) ≫ z) → AbBound t h C z := by
  exact @PositivityTheory.Xgn.height_bound_complex_conjugate

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_bound_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M y) (C : ℝ) (z : Sp ℂ ⟶ X), AbBound t h C (spMap (starRingEnd ℂ) ≫ z) → AbBound t h C z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.QuotUnif.abBound_of_conj
