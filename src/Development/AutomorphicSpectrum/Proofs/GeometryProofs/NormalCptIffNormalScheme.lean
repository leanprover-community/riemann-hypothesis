import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.WeilBound.CoreStatements.HodgeTatePoints.MfBase
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem component_whole_isIntegral_and_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) :=
  PositivityTheory.HtPt.Mf.xr_normal

end GlobalTheory.CompanionTheory.Ar.XR
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_cpt_iff_normal_scheme : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ IsNormalScheme X) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal
