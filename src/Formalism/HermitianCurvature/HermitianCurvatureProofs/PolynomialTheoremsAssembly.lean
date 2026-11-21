import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondPolynomialClauses

open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly

open Formalism.FourierDecayAlt.PairingProductCorollary

theorem thGrid_nonneg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) :
    0 ≤ F7.thGrid grid j := by
  unfold F7.thGrid
  exact Finset.prod_nonneg fun b _ => div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)







end Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly




end
