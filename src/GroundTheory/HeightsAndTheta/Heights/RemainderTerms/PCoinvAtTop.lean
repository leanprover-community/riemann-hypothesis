module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvAtTop.proof (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAtTop.Statement := by
  intro K _ _ f n H hH
  obtain ⟨v, hv, hJ⟩ := h1 K f n H
  obtain ⟨Q, -, hQ⟩ := h2 K f n (H - v) hJ (coinvTop f n)
  obtain ⟨-, c, hc⟩ := h3 K f n v hv
  refine ⟨c, ?_⟩
  have hcomp : H - C c * monomial (staircase f n) 1 =
      homogeneousComponent (coinvTop f n) (H - v) := by
    rw [map_sub, homogeneousComponent_eq_self hH, hc]
  rw [hcomp, hQ]
  refine Ideal.sum_mem _ fun m hm => Ideal.sum_mem _ fun b _ => ?_
  rw [Finset.mem_Icc] at hm
  exact Ideal.mul_mem_right _ _ (bps_mem_psumIdeal b hm.1 hm.2)

end

end GroundTheory.Heights₂.Heights.RestTerms
