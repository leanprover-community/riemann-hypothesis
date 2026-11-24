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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem Coinv.bps_isHomogeneous (K : Type) [Field K] (f n m : ℕ) (b : Fin f) :
    (bps K f n m b).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X_pow _ _

theorem CoinvIdealComponent.proof (h1 : CoinvIdealRepresentation.Statement)
    (h2 : HomogeneousComponentMul.Statement) : CoinvIdealComponent.Statement := by
  intro K _ f n J hJ d
  obtain ⟨a, rfl⟩ := h1 K f n J hJ
  refine ⟨fun m b => if m ≤ d then homogeneousComponent (d - m) (a m b) else 0, ?_, ?_⟩
  · intro m b
    dsimp only
    split_ifs
    · exact homogeneousComponent_isHomogeneous _ _
    · exact isHomogeneous_zero _ _ _
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h2 (Fin f × Fin n) K (bps K f n m b) (a m b) m d (bps_isHomogeneous K f n m b)]
    by_cases hmd : m ≤ d <;> simp [hmd]

end

end GroundTheory.Heights₂.Heights.RestTerms
