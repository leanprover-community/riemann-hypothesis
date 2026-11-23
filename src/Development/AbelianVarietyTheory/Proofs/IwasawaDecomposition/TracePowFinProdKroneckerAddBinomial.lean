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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

@[expose] public section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.ChernSpan

theorem kron_pow' {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) (n : ℕ) : kron a b ^ n = kron (a ^ n) (b ^ n) := by
  induction n with
  | zero => simp [kron_one]
  | succ n ih => rw [pow_succ, ih, ← kron_mul, pow_succ, pow_succ]

theorem trace_kron' {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (kron a b).trace = a.trace * b.trace := by
  rw [kron, ← Matrix.trace_kronecker]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finProdFinEquiv.symm fun x => Matrix.kroneckerMap (· * ·) a b x x

theorem trace_pow_kron_add {R : Type} [CommRing R] {M N : ℕ} (L : Matrix (Fin M) (Fin M) R)
    (L' : Matrix (Fin N) (Fin N) R) (i : ℕ) :
    ((kron L 1 + kron 1 L') ^ i).trace =
      ∑ a ∈ Finset.range (i + 1), (i.choose a : R) * (L ^ a).trace * (L' ^ (i - a)).trace := by
  have hc : Commute (kron L (1 : Matrix (Fin N) (Fin N) R)) (kron (1 : Matrix (Fin M) (Fin M) R) L') := by
    unfold Commute SemiconjBy
    rw [← kron_mul, ← kron_mul, mul_one, one_mul, mul_one, one_mul]
  rw [hc.add_pow, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [kron_pow', kron_pow', one_pow, one_pow, ← kron_mul, mul_one, one_mul, ← Nat.cast_comm,
    ← nsmul_eq_mul, Matrix.trace_smul, nsmul_eq_mul, trace_kron', mul_assoc]

end GlobalTheory.GoodMetric.ChernSpan
