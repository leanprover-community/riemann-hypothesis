import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite

section
namespace GlobalTheory.CompanionTheory.FlatFib

theorem flatOfFibresFinite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  intro R _ X Y f h1 h0 h2 h3 H
  exact GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ X Y f h1 h0 h2 h3 H

end GlobalTheory.CompanionTheory.FlatFib
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_fibres_finite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite
