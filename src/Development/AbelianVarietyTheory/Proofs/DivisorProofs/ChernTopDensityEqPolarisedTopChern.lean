import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffChernPolyEqPolarised

section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem chernTop_eq_mixTop {n m : ℕ} (G : V n → Mat (fun _ : Unit => m) ℂ) (v : V n) :
    chernTop (MvPolynomial.X ((), n)) G v =
      (Real.pi ^ n)⁻¹ * (mixTop fun _ => curvAt (fun u => G u ()) v).re := by
  rw [chernTop, MvPolynomial.aeval_X, GlobalTheory.T.topDegreeFormCoeff_chernPoly_eq_polarised]

end GlobalTheory.GoodTop
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTopDensity_eq_polarisedTopChern : ∀ {n m : ℕ} (G : V n → Mat (fun _ : Unit => m) ℂ) (v : V n), chernTop (MvPolynomial.X ((), n)) G v = (Real.pi ^ n)⁻¹ * (mixTop fun _ => curvAt (fun u => G u ()) v).re := by
  atlas_forward_decl GlobalTheory.GoodTop.chernTop_eq_mixTop
