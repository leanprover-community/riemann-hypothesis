import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair

section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem det_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (blockSum a b).det = a.det * b.det := by
  rw [blockSum, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem neg_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : -(blockSum a b) = blockSum (-a) (-b) := by
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.neg_apply]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;> simp

theorem one_sub_smul_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) :
    (1 - (Polynomial.X : Polynomial R) • (blockSum a b).map Polynomial.C) =
      blockSum (1 - (Polynomial.X : Polynomial R) • a.map Polynomial.C)
        (1 - (Polynomial.X : Polynomial R) • b.map Polynomial.C) := by
  rw [blockSum_map]
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply]
  rw [show (1 : Matrix (Fin (M + N)) (Fin (M + N)) (Polynomial R)) i j =
      (1 : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) (Polynomial R)) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) by
    simp [Matrix.one_apply]]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;>
    simp [Matrix.one_apply]

theorem charpolyRev_neg_blockSum : ∀ {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R), Matrix.charpolyRev (-(blockSum a b)) = Matrix.charpolyRev (-a) * Matrix.charpolyRev (-b) := by
  intro R _ M N a b
  rw [neg_blockSum, Matrix.charpolyRev, Matrix.charpolyRev, Matrix.charpolyRev, one_sub_smul_blockSum, det_blockSum]

end GlobalTheory.GoodMetric.ChernSpan
end

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpolyRev_neg_finSumBlockDiagonalMatrix : ∀ {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R), Matrix.charpolyRev (-(blockSum a b)) = Matrix.charpolyRev (-a) * Matrix.charpolyRev (-b) := by
  atlas_forward_decl GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum
