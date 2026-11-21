import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MapMemDifferentIdealIff
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem mem_differentIdeal_ringEquiv_iff :
    ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E),
      s d ∈ differentIdeal ℤ (𝓞 E) ↔ d ∈ differentIdeal ℤ (𝓞 E) :=
  @PositivityTheory.UnitarySelfGeneration.map_mem_differentIdeal_iff

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_ideal_automorphism_invariant : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E), s d ∈ differentIdeal ℤ (𝓞 E) ↔ d ∈ differentIdeal ℤ (𝓞 E) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.mem_differentIdeal_ringEquiv_iff
