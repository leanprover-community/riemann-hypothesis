module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequalitySteps
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Polynomial


attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
theorem PolynomialPrimeOverZeroHeight.proof : PolynomialPrimeOverZeroHeight.Statement := by
  intro D _ _ Q _ hQ
  let K := FractionRing D
  have disj : Disjoint ((nonZeroDivisors D).map (C : D →+* D[X]) : Set D[X]) (Q : Set D[X]) := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha ↦ ?_
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb.1
    apply hb0
    have : b ∈ Q.comap (C : D →+* D[X]) := by
      rw [Ideal.mem_comap]
      simpa [hb.2] using ha
    rwa [hQ, Ideal.mem_bot] at this
  have hK : ringKrullDim K[X] = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one K[X] (Polynomial.not_isField K)
  have h := IsLocalization.height_map_of_disjoint ((nonZeroDivisors D).map (C : D →+* D[X]))
    (S := K[X]) Q disj
  have hP : (Q.map (algebraMap D[X] K[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors D).map (C : D →+* D[X])) K[X] Q
      ‹_› disj
  have hle : ((Q.map (algebraMap D[X] K[X])).height : WithBot ℕ∞) ≤ 1 :=
    hK ▸ Ideal.height_le_ringKrullDim_of_isPrime
  rw [h] at hle
  exact_mod_cast hle

end GroundTheory.Heights₂.Heights.NumbersDVR
