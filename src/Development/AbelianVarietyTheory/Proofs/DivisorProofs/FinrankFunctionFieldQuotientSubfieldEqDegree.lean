import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormPowerIntegralHermLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeProjectionFormulaSelfInterPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMorphismOfGeneratingSection

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem finrank_ratF_eq_gdeg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (Module.finrank (ratF x) X.functionField : ℝ) = (e : ℝ) ^ D * gdeg P.L D := by
  intro hA k _ X _ p D hX P hamp e x hg
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  obtain ⟨hI, π, hπ, hgen, hr0, hr, hiso⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hamp e x hg
  obtain ⟨B, -, hB⟩ := GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference k X p D hX P e x hg
  obtain ⟨u, hu, -⟩ := hB 1 le_rfl
  have h1 := (hiso u hu).gdeg_eq D
  obtain ⟨hPV, hdeg, hcard⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D
  have h2 := (GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow hA k (PSpace k D) (PSpace.str k D) D hPV).1 X p hX π hπ hgen hr0 (ProjSpace.hermitianTwistingSheaf k D)
  have h3 : gdeg ((up P.L u).pow e) D = (e : ℝ) ^ D * gdeg (up P.L u) D :=
    GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow k X p D hX (up P.L u) e fun _ _ => 1
  have h4 := GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hA k X p D hX P.L u
  rw [← hr]
  push_cast
  rw [← hcard, ← hdeg, ← h2, ← h1, h3, h4]

end GlobalTheory.HSAmp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (Module.finrank (ratF x) X.functionField : ℝ) = (e : ℝ) ^ D * gdeg P.L D := by
  atlas_forward_decl GlobalTheory.HSAmp.finrank_ratF_eq_gdeg
