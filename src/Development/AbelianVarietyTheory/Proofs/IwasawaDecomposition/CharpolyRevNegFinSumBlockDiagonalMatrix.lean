module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

@[expose] public section

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
