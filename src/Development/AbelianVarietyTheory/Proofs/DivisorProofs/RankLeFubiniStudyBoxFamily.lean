import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFubiniStudyRatFnsMemPairSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeGeometricDegreeOfIsNef

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fs_box_rank_le : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J]
    (e : J → X.functionField) (x : Fin D → X.functionField) (w : J × Finset (Fin D) → ℝ),
    LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, 0 ≤ w c) →
    IsFS M (boxFam e x) w → (D.factorial : ℝ) * Fintype.card J ≤ gdeg M D := by
  intro hAr hHS k _ X _ p D hD M J _ e x w he hx hw hFS
  have hNef : M.IsNef D := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hAr k X p D hD M _ (boxFam e x) w hFS hw
  obtain ⟨P, hPL, hmem⟩ := GlobalTheory.T.isFubiniStudy_ratFns_mem_pairSections k X p M _ (boxFam e x) w hFS
  subst hPL
  exact GlobalTheory.T.rank_le_geometricDegree_of_isNef hAr hHS k X p D hD P hNef J e x he hx hmem

end GlobalTheory.HSNef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_le_fubiniStudy_boxFamily : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField) (w : J × Finset (Fin D) → ℝ), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, 0 ≤ w c) → IsFS M (boxFam e x) w → (D.factorial : ℝ) * Fintype.card J ≤ gdeg M D := by
  atlas_forward_decl GlobalTheory.HSNef.fs_box_rank_le
