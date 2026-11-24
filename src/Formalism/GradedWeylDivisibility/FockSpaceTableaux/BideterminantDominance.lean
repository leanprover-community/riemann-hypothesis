module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetdomLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem bideterminantDominance : BideterminantDominance := by
  classical
  intro R _ r n K sz hsz I m hm
  have hm' : m ∈ (∏ k : Fin K, initMinor R (I k) (hsz k)).support := hm
  refine ⟨fun k => ?_, ?_⟩
  · have h := support_prod_le_of_additive (rowPart k) (rowPart_zero k)
      (rowPart_add k) Finset.univ (fun k' => initMinor R (I k') (hsz k'))
      (fun k' => min k (sz k'))
      (fun k' _ m' hm'' => (initMinor_support (I k') (hsz k') m' hm'').1 k)
      m hm'
    exact h.trans_eq (sum_min_eq_shapeDeg sz hsz k)
  · have h := support_prod_eq_of_additive rowTot rowTot_zero
      rowTot_add Finset.univ (fun k' => initMinor R (I k') (hsz k')) sz
      (fun k' _ m' hm'' => (initMinor_support (I k') (hsz k') m' hm'').2)
      m hm'
    have h2 := sum_min_eq_shapeDeg sz hsz n
    have h3 : ∑ t : Fin n with t.val < n, shapeDeg sz t =
        ∑ t : Fin n, shapeDeg sz t :=
      Finset.sum_congr (Finset.filter_true_of_mem fun t _ => t.isLt) fun _ _ => rfl
    have h4 : ∑ k' : Fin K, min n (sz k') = ∑ k' : Fin K, sz k' :=
      Finset.sum_congr rfl fun k' _ => min_eq_right (hsz k')
    exact h.trans (h4.symm.trans (h2.trans h3))

end Formalism.GradedWeylDivisibility
