import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightsNonnegOfIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GeneratedLineBundleNefOnFibres

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem smallGenerated_count_upper_of_moriwakiHS :
    MoriwakiHSStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G7.Statement := by
  intro hM K _ ι _ Ω _ _ y D A P0 II _ hII hY hb hS hconj
  obtain ⟨q, w, hw, hgen, hsmall⟩ := hS.gen
  have hnef : NefOnFibres (mCoordIdeal y) A.a :=
    GlobalTheory.T.generated_line_bundle_nef_on_fibres K ι Ω y D A.a q w hY hb hw hgen
  have hhts : HeightsNonneg II (mCoordIdeal y) A :=
    GlobalTheory.T.heights_nonneg_of_intersection_system K ι Ω y D A II q w hII hY hb hS.semipos.1 hw hgen hsmall
  have hgeneric : NefOnGeneric (mCoordIdeal y) A :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.proof K ι (mCoordIdeal y) P0 A hS.normalForm_baseLattice_le_dualSpan_sup_line
      hS.semipos
  exact le_of_eq
    (hM K ι Ω y D A P0 II hII hY hb hS.normalForm_baseLattice_le_dualSpan_sup_line hS.semipos hconj hnef hgeneric hhts).limsup_eq

end GlobalTheory.CompanionTheory.Ar.Giv
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_samuel_G7_of_moriwaki : MoriwakiHSStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G7.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Giv.smallGenerated_count_upper_of_moriwakiHS
