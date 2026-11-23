module

public import Mathlib.Algebra.MvPolynomial.Degrees
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

open NumberField MvPolynomial

noncomputable section

namespace GlobalTheory.SZShift

theorem totalDegree_aeval_le_of_deg_le_one {σ τ F E : Type} [CommRing F] [CommRing E] [Algebra F E]
    (g : σ → MvPolynomial τ E) (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial σ F) :
    (aeval g P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]

  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_apply, totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hd)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hg i))

end GlobalTheory.SZShift
