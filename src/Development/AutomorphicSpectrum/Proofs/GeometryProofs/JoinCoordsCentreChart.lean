import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.WeilBound.CoreStatements.HodgeTatePoints.InChartOfMemCtrSet
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem join_points_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' :=
  @PositivityTheory.HtPt.Mb.join_charts

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_coords_centre_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.join_points_charts
