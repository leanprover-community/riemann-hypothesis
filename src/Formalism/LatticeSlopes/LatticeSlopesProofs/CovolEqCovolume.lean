module

public import Formalism.LatticeSlopes.Statement
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section
open Module Submodule MeasureTheory
noncomputable section
namespace Formalism.F

theorem covol_eq_covolume' : CovolEqCovolume := by
  intro E _ _ _ _ _ L _ _
  classical
  rw [covol, dite_eq_left (inferInstance : DiscreteTopology L)]
  let b := Module.finBasis ℤ L
  let bR := b.ofZLatticeBasis ℝ L
  let o := (stdOrthonormalBasis ℝ E).reindex (finCongr (ZLattice.rank ℝ L).symm)
  rw [show (fun i => ((b i : L) : E)) = (fun j => ∑ i, o.toBasis.toMatrix bR i j • o.toBasis i) by
        funext j
        rw [o.toBasis.sum_toMatrix_smul_self]
        exact (Basis.ofZLatticeBasis_apply ℝ L b j).symm,
      gram_sum_smul_eq_transpose_mul, show Matrix.gram ℝ (fun i => o.toBasis i) = 1 by
        ext i j
        simp [Matrix.gram, Matrix.one_apply, orthonormal_iff_ite.mp o.orthonormal],
      Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume (ZLattice.isAddFundamentalDomain b volume)]
  change _ = (volume (ZSpan.fundamentalDomain bR)).toReal
  rw [ZSpan.measure_fundamentalDomain bR volume o.toBasis,
      measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
      OrthonormalBasis.coe_toBasis, o.volume_parallelepiped, mul_one,
      ENNReal.toReal_ofReal (abs_nonneg _), Basis.det_apply]
end Formalism.F
