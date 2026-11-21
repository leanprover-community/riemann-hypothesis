import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSncCoordsOfLocal

section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Geo.SncCoordsSide

theorem coordsStatement_side : ReciprocityTheory.ChartRestriction.G.Geo.ResK.CoordsStatement :=
  GlobalTheory.CompanionTheory.Geo.SncCoords.coordsStatement

end GlobalTheory.CompanionTheory.Geo.SncCoordsSide
end

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.CoordsStatement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Geo.SncCoordsSide.coordsStatement_side
