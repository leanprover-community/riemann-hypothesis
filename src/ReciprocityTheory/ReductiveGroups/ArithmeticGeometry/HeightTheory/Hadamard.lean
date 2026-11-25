module

import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LinearIndependentRealOfIntOfDiscrete
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SchurAverage
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open scoped BigOperators ComplexOrder
open Finset Matrix

theorem psd_det_re_le_prod_diag (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosSemidef) :
    G.det.re ≤ ∏ c, (G c c).re := by
  have hd (i : Fin N) : ((G i i).re : ℂ) = G i i :=
    Complex.conj_eq_iff_re.mp (by simpa [conjTranspose_apply] using congrFun (congrFun hG.1 i) i)
  have h := (Complex.le_def.mp (GlobalTheory.posSemidef_det_le_prod_diag hG)).1
  rwa [← Complex.ofReal_re (∏ i, (G i i).re), Complex.ofReal_prod,
    Finset.prod_congr rfl (fun i _ => hd i)]

theorem hadamard_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  apply Formalism.HermitianLatticeCounting.P.norm_det_le_prod_row_norms

end ReciprocityTheory.ChartRestriction.G.T0
