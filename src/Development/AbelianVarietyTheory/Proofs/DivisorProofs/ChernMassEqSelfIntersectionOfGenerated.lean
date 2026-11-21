import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullO1ToProjOfIsLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDimSuccGeneratingSectionsInfiniteField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOfLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyPullbackChernMassEqDegree

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem chernInt_eq_topSelf_of_generated : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ n u hu
  have hL : L.IsLB := φ.isLB
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_dimSucc_generating_sections_infiniteField ℂ Y.X Y.str L hL Y.dim (Var.topologicalKrullDim_eq Y).le n u hu
  have hπ : ProjSpace.toProj Y.str s hs ≫ PSpace.str ℂ Y.dim = Y.str := ProjSpace.toProj_str Y.str s hs
  have e := GlobalTheory.ProjSpace.lbIso_pull_O1_toProj_of_isLB ℂ Y.dim Y.X L hL Y.str s hs
  have h1 := GlobalTheory.T.chernIntegral_eq_of_lineBundle_iso Y _ L (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull _ hπ) φ e
    (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf (RingHom.id ℂ)).pull _ hπ) hφ
  rw [← h1, GlobalTheory.T.chernInt_pull_fubiniStudy_eq_topSelf Y _ hπ,
    topSelf_congr ℂ (LB.isLB_pull (ProjSpace.O1_isLB ℂ Y.dim) (ProjSpace.toProj Y.str s hs)) hL e]

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMass_eq_selfIntersection_of_generated : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  atlas_forward_decl GlobalTheory.chernInt_eq_topSelf_of_generated
