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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.AevalTotalDegreeLinear

open MvPolynomial

theorem totalDegree_aeval_le_of_linear {κ : Type} (f : κ → MvPolynomial κ ℂ)
    (hf : ∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) (P : MvPolynomial κ ℂ) :
    MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P)
      ≤ MvPolynomial.totalDegree P := by
  classical
  conv_lhs => rw [P.as_sum]

  rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  have hprod : totalDegree (s.prod fun i k => f i ^ k) ≤ s.sum fun _ k => k := by
    rw [Finsupp.prod, Finsupp.sum]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (totalDegree_pow _ _).trans ?_
    calc s i * totalDegree (f i) ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
      _ = s i := mul_one _
  refine hprod.trans ?_
  exact Finset.le_sup (f := fun s : κ →₀ ℕ => s.sum fun _ e => e) hs

theorem main : ∀ {κ : Type} (f : κ → MvPolynomial κ ℂ), (∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial κ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => totalDegree_aeval_le_of_linear f hf P

end GlobalTheory.AevalTotalDegreeLinear
