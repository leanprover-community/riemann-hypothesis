module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u_1
namespace GlobalTheory.AevalTotalDegreeBound
open MvPolynomial

theorem aeval_totalDegree_le {σ : Type u_1} (f : σ → MvPolynomial σ ℂ)
    (hf : ∀ v, (f v).totalDegree ≤ 1) (P : MvPolynomial σ ℂ) :
    (aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]

  rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine le_trans ?_ (le_totalDegree hs)
  unfold Finsupp.prod
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  unfold Finsupp.sum
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)

theorem main : ∀ {σ : Type u_1} (f : σ → MvPolynomial σ ℂ), (∀ (v : σ), MvPolynomial.totalDegree (f v) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial σ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial σ ℂ → MvPolynomial σ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => aeval_totalDegree_le f hf P

end GlobalTheory.AevalTotalDegreeBound
