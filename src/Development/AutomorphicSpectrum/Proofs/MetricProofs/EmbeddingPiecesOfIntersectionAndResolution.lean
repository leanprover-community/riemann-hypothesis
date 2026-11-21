import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatementStatement

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem embeddingPieces_of_resK (hA : ArithIntersectionSystemStatement)
    (hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) :
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement :=
  have hInt : PtsIntegrableStatement := GlobalTheory.T.points_integrable_of_resolution_statement hR
  have hRes : ResExistsStatement := GlobalTheory.T.resolution_exists_of_resolution_statement hR
  GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt)
    (GlobalTheory.T.piece_degree_of_intersection_and_resolution hA hRes hInt)

end GlobalTheory.CompanionTheory.Ar.Giv
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_pieces_of_intersection_and_resolution : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Giv.embeddingPieces_of_resK
