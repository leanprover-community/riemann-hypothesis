import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernTensorAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEqStatement

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory

theorem c1F_grLB_add_grLB_flag_indep :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2), c1F hX σ (VMetric.grLB fl 0 H) + c1F hX σ (VMetric.grLB fl 1 H) = c1F hX σ (VMetric.grLB fl' 0 H) + c1F hX σ (VMetric.grLB fl' 1 H) := by
  intro k _ X _ p D hX σ E h H fl fl'
  rw [← GlobalTheory.T.firstChern_tensor_add k X p D hX σ, ← GlobalTheory.T.firstChern_tensor_add k X p D hX σ,
    GlobalTheory.T.firstChern_isometric_eq k X p D hX σ _ _ (VMetric.isometric_grLB_tens_grLB_det k X p E h H fl),
    GlobalTheory.T.firstChern_isometric_eq k X p D hX σ _ _ (VMetric.isometric_grLB_tens_grLB_det k X p E h H fl')]

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_first_chern_sum_indep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2), c1F hX σ (VMetric.grLB fl 0 H) + c1F hX σ (VMetric.grLB fl 1 H) = c1F hX σ (VMetric.grLB fl' 0 H) + c1F hX σ (VMetric.grLB fl' 1 H) := by
  atlas_forward_decl GlobalTheory.c1F_grLB_add_grLB_flag_indep
