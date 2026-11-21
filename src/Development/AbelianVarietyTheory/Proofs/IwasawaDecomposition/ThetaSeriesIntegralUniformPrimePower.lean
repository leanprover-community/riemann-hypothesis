import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerIntAtOfSeriesRat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsTowerCover

section
namespace GlobalTheory

theorem serInt_outright : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP
  exact ⟨fun u hu c0 hc0 => GlobalTheory.LevelSeries.serIntAt_record D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP u hu c0 hc0, GlobalTheory.T.unramified_descent_integral_forms_tower_cover D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP⟩

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_integral_uniform_prime_power : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  atlas_forward_decl GlobalTheory.serInt_outright
