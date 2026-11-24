module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeVanishingHomog
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset

theorem ConeVanishingHomog.proof : ConeVanishingHomog.Statement := by
  intro n C hC f hf d
  rw [mem_vanishingIdeal_iff] at hf ⊢
  intro c hc
  replace hf : ∀ x ∈ C, eval x f = 0 := hf
  show eval c (homogeneousComponent d f) = 0

  set p : Polynomial ℂ := ∑ i ∈ range (f.totalDegree + 1),
    Polynomial.C (eval c (homogeneousComponent i f)) * Polynomial.X ^ i with hp
  have hroot : ∀ a : ℂ, a ≠ 0 → p.IsRoot a := by
    intro a ha
    have h0 := hf (a • c) (hC c hc a ha)

    rw [← sum_homogeneousComponent f, map_sum] at h0
    rw [Polynomial.IsRoot, hp, Polynomial.eval_finsetSum, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i f)]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hinf : Set.Infinite {x | p.IsRoot x} := by
    refine Set.Infinite.mono (s := ({0} : Set ℂ)ᶜ) ?_
      (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    exact hroot x (by simpa using hx)
  have hp0 : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hinf
  by_cases hd : d ≤ f.totalDegree
  · have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff d) hp0
    simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_ite_eq] at hcoeff
    simpa [Finset.mem_range, Nat.lt_succ_of_le hd] using hcoeff
  · rw [homogeneousComponent_eq_zero d f (by omega), map_zero]

end GroundTheory.Heights₂.Heights
