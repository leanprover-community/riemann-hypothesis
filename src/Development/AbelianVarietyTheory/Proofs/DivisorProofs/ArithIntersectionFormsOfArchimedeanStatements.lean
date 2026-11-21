import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedHeightOfArchimedeanIntegrals
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionNumberExistsOfMixedHeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithMixedInterInductiveOfMixedHeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPointStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtCalc

theorem arFormExists_arMix_heightProjection (hI : ArchInteg) (hR : ArchRecip) :
    GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  have hE := GlobalTheory.T.exists_mixedHeight_of_archimedean_integrals hI hR
  refine ⟨GlobalTheory.T.arithIntersectionNumber_exists_of_mixedHeights hI hE, GlobalTheory.T.arithMixedInterInductive_of_mixedHeights hI hE, ?_⟩
  intro k _ X Y _ p q D e hX hY π hπ _ _ L h hh
  obtain ⟨T, hT⟩ := hE k Y q (isAmb_of_isArithVar hY) (e + 1)
  obtain ⟨h', hh', -⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hI k Y q e hY T hT (L.pull π hπ)
  exact ⟨h', hh', GlobalTheory.T.arithHeight_projectionFormula_every_point k X Y p q D e hX hY π hπ L h h' hh hh' (genericPoint Y)⟩

end GlobalTheory.MixHtCalc
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersection_forms_of_archimedean_statements : ArchInteg → ArchRecip → GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  atlas_forward_decl GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection
